-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1558_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:23:55.170549+00:00
-- url     : https://prove2.me/submissions/27bbcddf-4ccf-4601-9eca-08a64ef4e773

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_signed_majorant
/- Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa,
bwdaugherty and Yuxuan Xu. All new numerical implications are checked below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring
theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]
end HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalRealBundle
theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'
end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_support {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (w x : ι → ℝ)
    (hw : (∑ i, |w i| ^ q) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ w x hpq.symm
  have hq : 0 ≤ 1/q := hpq.symm.one_div_nonneg
  have hr := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (w i)) q) hw hq
  rw [Real.one_rpow] at hr
  have hn := lpNorm_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hr hn
  simpa only [lpNorm, Real.norm_eq_abs, one_mul] using h.trans hm

theorem power12over11_upper {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^12 ≤ y^11) : x^(12/11 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 12) h (by norm_num : (0 : ℝ) ≤ 1/11)
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast y 11,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy] at hr
  norm_num at hr ⊢
  exact hr

theorem norm_support12 (w v x : Fin 3 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i, |w i|^12 ≤ (v i)^11)
    (hs : (∑ i, v i) ≤ 1) : (∑ i, w i*x i) ≤ lpNorm 12 x := by
  apply norm_support (q := 12/11)
    (Real.holderConjugate_iff.mpr (by norm_num))
  exact (Finset.sum_le_sum fun i _ => power12over11_upper (abs_nonneg _) (hv i) (hp i)).trans hs

theorem power_ratio_upper {x y : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^m ≤ y^n) :
    x^((m : ℝ)/(n : ℝ)) ≤ y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.rpow_le_rpow (pow_nonneg hx m) h (one_div_nonneg.mpr hn0.le)
  rw [← Real.rpow_natCast x m, ← Real.rpow_natCast y n,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy,
    mul_one_div_cancel hn0.ne', Real.rpow_one] at hr
  simpa only [div_eq_mul_inv, one_div, one_mul] using hr

theorem norm_support_interval {p b : ℝ} (hp : 1 < p) (hb : 1 < b)
    (hpb : p ≤ b) (w x : Fin 3 → ℝ)
    (hw1 : ∀ i, |w i| ≤ 1)
    (hw : (∑ i, |w i|^(b/(b-1))) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have hqp : b/(b-1) ≤ p/(p-1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hq0 : 0 ≤ b/(b-1) := div_nonneg (by linarith) (by linarith)
  apply norm_support (q := p/(p-1))
    ((Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl)
  apply le_trans _ hw
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
    (abs_nonneg _) (hw1 i) hq0 hqp

theorem norm_support_interval_cert {p b : ℝ} (m n : ℕ) (hn : 0 < n)
    (hp : 1 < p) (hb : 1 < b) (hpb : p ≤ b)
    (hconj : b/(b-1) = (m : ℝ)/(n : ℝ))
    (w v x : Fin 3 → ℝ) (hw1 : ∀ i, |w i| ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (hpowers : ∀ i, |w i|^m ≤ (v i)^n) (hs : (∑ i, v i) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  apply norm_support_interval hp hb hpb w x hw1
  rw [hconj]
  exact (Finset.sum_le_sum fun i _ =>
    power_ratio_upper m n hn (abs_nonneg _) (hv i) (hpowers i)).trans hs

end HlawkaSchatten.DiagonalCutoff12


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6




theorem total_eq (X : Fin 3 → Fin 3 → ℝ) : total X = X 0+X 1+X 2 := by
  simp [total,Fin.sum_univ_three]
theorem pair0 (X : Fin 3 → Fin 3 → ℝ) : pair X 0 = X 1+X 2 := by
  rw [pair,total_eq];abel
theorem pair1 (X : Fin 3 → Fin 3 → ℝ) : pair X 1 = X 0+X 2 := by
  rw [pair,total_eq];abel
theorem pair2 (X : Fin 3 → Fin 3 → ℝ) : pair X 2 = X 0+X 1 := by
  rw [pair,total_eq];abel


theorem oriented_frame {p q k d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : RelativeOrientedData p q k d X) : Frame p k (3*q) d X := by
  constructor
  · simpa [Fin.sum_univ_three] using h.sum
  · simpa [total_eq] using h.norm_le_total
  · simpa [total_eq] using h.total_one
  · simpa [total_eq] using h.total_cap.le
  · intro i;fin_cases i
    · simpa [pair0] using h.main0
    · simpa [pair1] using h.main1
    · simpa [pair2] using h.main2
  · intro i h';fin_cases i
    · simpa [pair0] using h.max0 h'
    · simpa [pair1] using h.max1 h'
    · simpa [pair2] using h.max2 h'
  · simpa [total_eq,Fin.sum_univ_three,pair0,pair1,pair2] using h.linear_failure

theorem total_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) :
    total (relabel e X) = total X ∘ e := by
  ext h
  simp only [total,Finset.sum_apply,relabel,Function.comp_apply]
  exact Equiv.sum_comp e (fun j => X j (e h))

theorem pair_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    pair (relabel e X) i = pair X (e i) ∘ e := by
  ext h
  simp [pair,total_relabel,relabel]

theorem frame_relabel {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : Frame p k A d X) (e : Equiv.Perm (Fin 3)) : Frame p k A d (relabel e X) := by
  have hr (j : Fin 3) : lpNorm p (relabel e X j) = lpNorm p (X (e j)) :=
    lpNorm_comp_equiv p (X (e j)) e
  have ht : lpNorm p (total (relabel e X)) = lpNorm p (total X) := by
    rw [total_relabel,lpNorm_comp_equiv]
  have hp (i : Fin 3) : lpNorm p (pair (relabel e X) i) = lpNorm p (pair X (e i)) := by
    rw [pair_relabel,lpNorm_comp_equiv]
  constructor
  · simp_rw [hr];rw [Equiv.sum_comp e (fun j => lpNorm p (X j))];exact h.sum
  · intro j;rw [hr,ht];exact h.row_total (e j)
  · rw [ht];exact h.total_one
  · rw [ht];exact h.total_cap
  · intro i;rw [hp,pair_relabel];exact h.main (e i)
  · intro i j;rw [pair_relabel];exact h.maximal (e i) (e j)
  · simp_rw [ht,hp];rw [Equiv.sum_comp e (fun i => lpNorm p (pair X i))];exact h.linear_failure

theorem frame_box_of_base {p k A d ell u v w rho : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_ratio_of_base {p k A d rho R : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201

end HlawkaSchatten.DiagonalCutoff6

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6


theorem pair_eq_of_distinct (X : Fin 3 → Fin 3 → ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : pair X i = X j+X l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
  all_goals first
    | exact pair0 X
    | exact (pair0 X).trans (add_comm _ _)
    | exact pair1 X
    | exact (pair1 X).trans (add_comm _ _)
    | exact pair2 X
    | exact (pair2 X).trans (add_comm _ _)

theorem frame_linear_data {p k A d : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : Frame p k A d X) :
    LinearData k A d X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · exact h.main
  · exact h.maximal
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem linear_data_bounds {k A d T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : LinearData k A d X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]

theorem positive_pair_majorant {p a rho alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha)
    (hc1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hc2 : 1+2*rho^a ≤ (1+2*alpha*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hm : ∀ i, 0 ≤ pair X i i)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ pair X i i+alpha*(pair X i j+pair X i l) := by
  rw [HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p _ hij hil hjl]
  have hh := signed_majorant hp ha hap hrho hrho1 halpha hc1 hc2 (hm i)
    (hratio i j hij) (hratio i l hil)
  simpa only [abs_of_nonneg (hsign i j hij),abs_of_nonneg (hsign i l hil)] using hh

theorem frame_weaken {p k A d k' A' d' : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (h : Frame p k A d X) (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    Frame p k' A' d' X := by
  have f := frame_linear_data hp X h
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  constructor
  · exact h.sum
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap.trans hA
  · intro i
    exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (h.main i)
  · exact h.maximal
  · have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
    linarith only [hh,h.linear_failure]

end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

end HlawkaSchatten.DiagonalCutoff4

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff4

theorem rational_powers_le (a b c d m n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : a^m*d^n ≤ c^n*b^m) :
    ((a : ℝ)/b)^m ≤ ((c : ℝ)/d)^n := by
  rw [div_pow,div_pow]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)).mpr
  exact_mod_cast h

theorem rectangle_budgets {a lo hi c alpha pl ph : ℝ}
    (hl : lo^a ≤ pl) (hh : hi^a ≤ ph)
    (h00 : 1+2*pl ≤ (c+2*alpha*lo)^a)
    (h10 : 1+ph+pl ≤ (c+alpha*(hi+lo))^a)
    (h11 : 1+2*ph ≤ (c+2*alpha*hi)^a) :
    1+2*lo^a ≤ (c+2*alpha*lo)^a ∧
    1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a ∧
    1+2*hi^a ≤ (c+2*alpha*hi)^a := by
  constructor
  · linarith only [hl,h00]
  constructor
  · linarith only [hl,hh,h10]
  · linarith only [hh,h11]

theorem sum_two_bounds {x y X Y z : ℝ} (hx : x ≤ X) (hy : y ≤ Y)
    (hz : X+2*Y ≤ z) : x+2*y ≤ z := by
  linarith only [hx,hy,hz]

theorem three_bounds {x X : ℝ} (hx : x ≤ X) (hX : 3*X ≤ 1) : x+x+x ≤ 1 := by
  linarith only [hx,hX]

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1558_s0_0 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1638114257/10000000000 : ℝ)*x 0 + (235131153/400000000 : ℝ)*x 1 + (2437252759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1638114257/10000000000 : ℝ)^4613 ≤ (9776509470727/100000000000000 : ℝ)^3589 := by
    have hnat : (1638114257 : ℕ)^4613*100000000000000^3589 ≤ 9776509470727^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1638114257 10000000000 9776509470727 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235131153/400000000 : ℝ)^4613 ≤ (50514203653449/100000000000000 : ℝ)^3589 := by
    have hnat : (235131153 : ℕ)^4613*100000000000000^3589 ≤ 50514203653449^3589*400000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235131153 400000000 50514203653449 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2437252759/5000000000 : ℝ)^4613 ≤ (198546434311/500000000000 : ℝ)^3589 := by
    have hnat : (2437252759 : ℕ)^4613*500000000000^3589 ≤ 198546434311^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437252759 5000000000 198546434311 500000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1638114257/10000000000 : ℝ), (235131153/400000000 : ℝ), (2437252759/5000000000 : ℝ)] ![(9776509470727/100000000000000 : ℝ), (50514203653449/100000000000000 : ℝ), (198546434311/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1638114257/10000000000 : ℝ)|^4613 ≤ (9776509470727/100000000000000 : ℝ)^3589
        have hw : |(-1638114257/10000000000 : ℝ)|=(1638114257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(235131153/400000000 : ℝ)|^4613 ≤ (50514203653449/100000000000000 : ℝ)^3589
        have hw : |(235131153/400000000 : ℝ)|=(235131153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2437252759/5000000000 : ℝ)|^4613 ≤ (198546434311/500000000000 : ℝ)^3589
        have hw : |(2437252759/5000000000 : ℝ)|=(2437252759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s0_1 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (683505513/1250000000 : ℝ)*x 0 + (-549377181/2500000000 : ℝ)*x 1 + (4874505519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (683505513/1250000000 : ℝ)^4613 ≤ (11507241587701/25000000000000 : ℝ)^3589 := by
    have hnat : (683505513 : ℕ)^4613*25000000000000^3589 ≤ 11507241587701^3589*1250000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683505513 1250000000 11507241587701 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549377181/2500000000 : ℝ)^4613 ≤ (7130873379699/50000000000000 : ℝ)^3589 := by
    have hnat : (549377181 : ℕ)^4613*50000000000000^3589 ≤ 7130873379699^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549377181 2500000000 7130873379699 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4874505519/10000000000 : ℝ)^4613 ≤ (3970928687267/10000000000000 : ℝ)^3589 := by
    have hnat : (4874505519 : ℕ)^4613*10000000000000^3589 ≤ 3970928687267^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4874505519 10000000000 3970928687267 10000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(683505513/1250000000 : ℝ), (-549377181/2500000000 : ℝ), (4874505519/10000000000 : ℝ)] ![(11507241587701/25000000000000 : ℝ), (7130873379699/50000000000000 : ℝ), (3970928687267/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(683505513/1250000000 : ℝ)|^4613 ≤ (11507241587701/25000000000000 : ℝ)^3589
        have hw : |(683505513/1250000000 : ℝ)|=(683505513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-549377181/2500000000 : ℝ)|^4613 ≤ (7130873379699/50000000000000 : ℝ)^3589
        have hw : |(-549377181/2500000000 : ℝ)|=(549377181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4874505519/10000000000 : ℝ)|^4613 ≤ (3970928687267/10000000000000 : ℝ)^3589
        have hw : |(4874505519/10000000000 : ℝ)|=(4874505519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s0_2 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2734022073/5000000000 : ℝ)*x 0 + (487450547/1000000000 : ℝ)*x 1 + (-219750873/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2734022073/5000000000 : ℝ)^4613 ≤ (1841158672209/4000000000000 : ℝ)^3589 := by
    have hnat : (2734022073 : ℕ)^4613*4000000000000^3589 ≤ 1841158672209^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734022073 5000000000 1841158672209 4000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487450547/1000000000 : ℝ)^4613 ≤ (39709286359611/100000000000000 : ℝ)^3589 := by
    have hnat : (487450547 : ℕ)^4613*100000000000000^3589 ≤ 39709286359611^3589*1000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487450547 1000000000 39709286359611 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219750873/1000000000 : ℝ)^4613 ≤ (1782718351181/12500000000000 : ℝ)^3589 := by
    have hnat : (219750873 : ℕ)^4613*12500000000000^3589 ≤ 1782718351181^3589*1000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219750873 1000000000 1782718351181 12500000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2734022073/5000000000 : ℝ), (487450547/1000000000 : ℝ), (-219750873/1000000000 : ℝ)] ![(1841158672209/4000000000000 : ℝ), (39709286359611/100000000000000 : ℝ), (1782718351181/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2734022073/5000000000 : ℝ)|^4613 ≤ (1841158672209/4000000000000 : ℝ)^3589
        have hw : |(2734022073/5000000000 : ℝ)|=(2734022073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(487450547/1000000000 : ℝ)|^4613 ≤ (39709286359611/100000000000000 : ℝ)^3589
        have hw : |(487450547/1000000000 : ℝ)|=(487450547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219750873/1000000000 : ℝ)|^4613 ≤ (1782718351181/12500000000000 : ℝ)^3589
        have hw : |(-219750873/1000000000 : ℝ)|=(219750873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s0_3 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4132960461/10000000000 : ℝ)*x 0 + (309254647/1000000000 : ℝ)*x 1 + (1360664483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4132960461/10000000000 : ℝ)^4613 ≤ (16059956186633/50000000000000 : ℝ)^3589 := by
    have hnat : (4132960461 : ℕ)^4613*50000000000000^3589 ≤ 16059956186633^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132960461 10000000000 16059956186633 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309254647/1000000000 : ℝ)^4613 ≤ (11062803053127/50000000000000 : ℝ)^3589 := by
    have hnat : (309254647 : ℕ)^4613*50000000000000^3589 ≤ 11062803053127^3589*1000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309254647 1000000000 11062803053127 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360664483/2500000000 : ℝ)^4613 ≤ (5719310187841/12500000000000 : ℝ)^3589 := by
    have hnat : (1360664483 : ℕ)^4613*12500000000000^3589 ≤ 5719310187841^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360664483 2500000000 5719310187841 12500000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4132960461/10000000000 : ℝ), (309254647/1000000000 : ℝ), (1360664483/2500000000 : ℝ)] ![(16059956186633/50000000000000 : ℝ), (11062803053127/50000000000000 : ℝ), (5719310187841/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4132960461/10000000000 : ℝ)|^4613 ≤ (16059956186633/50000000000000 : ℝ)^3589
        have hw : |(4132960461/10000000000 : ℝ)|=(4132960461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(309254647/1000000000 : ℝ)|^4613 ≤ (11062803053127/50000000000000 : ℝ)^3589
        have hw : |(309254647/1000000000 : ℝ)|=(309254647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360664483/2500000000 : ℝ)|^4613 ≤ (5719310187841/12500000000000 : ℝ)^3589
        have hw : |(1360664483/2500000000 : ℝ)|=(1360664483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s0_4 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-65650411/400000000 : ℝ)*x 0 + (1224967409/2500000000 : ℝ)*x 1 + (5852014089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65650411/400000000 : ℝ)^4613 ≤ (2450162263249/25000000000000 : ℝ)^3589 := by
    have hnat : (65650411 : ℕ)^4613*25000000000000^3589 ≤ 2450162263249^3589*400000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65650411 400000000 2450162263249 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1224967409/2500000000 : ℝ)^4613 ≤ (9993765315481/25000000000000 : ℝ)^3589 := by
    have hnat : (1224967409 : ℕ)^4613*25000000000000^3589 ≤ 9993765315481^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1224967409 2500000000 9993765315481 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5852014089/10000000000 : ℝ)^4613 ≤ (50224289674061/100000000000000 : ℝ)^3589 := by
    have hnat : (5852014089 : ℕ)^4613*100000000000000^3589 ≤ 50224289674061^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5852014089 10000000000 50224289674061 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65650411/400000000 : ℝ), (1224967409/2500000000 : ℝ), (5852014089/10000000000 : ℝ)] ![(2450162263249/25000000000000 : ℝ), (9993765315481/25000000000000 : ℝ), (50224289674061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65650411/400000000 : ℝ)|^4613 ≤ (2450162263249/25000000000000 : ℝ)^3589
        have hw : |(-65650411/400000000 : ℝ)|=(65650411/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1224967409/2500000000 : ℝ)|^4613 ≤ (9993765315481/25000000000000 : ℝ)^3589
        have hw : |(1224967409/2500000000 : ℝ)|=(1224967409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5852014089/10000000000 : ℝ)|^4613 ≤ (50224289674061/100000000000000 : ℝ)^3589
        have hw : |(5852014089/10000000000 : ℝ)|=(5852014089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s0_5 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596828947/5000000000 : ℝ)*x 0 + (-610000227/5000000000 : ℝ)*x 1 + (5852014033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596828947/5000000000 : ℝ)^4613 ≤ (43081742548157/100000000000000 : ℝ)^3589 := by
    have hnat : (2596828947 : ℕ)^4613*100000000000000^3589 ≤ 43081742548157^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596828947 5000000000 43081742548157 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610000227/5000000000 : ℝ)^4613 ≤ (6693968384311/100000000000000 : ℝ)^3589 := by
    have hnat : (610000227 : ℕ)^4613*100000000000000^3589 ≤ 6693968384311^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610000227 5000000000 6693968384311 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5852014033/10000000000 : ℝ)^4613 ≤ (156950903301/312500000000 : ℝ)^3589 := by
    have hnat : (5852014033 : ℕ)^4613*312500000000^3589 ≤ 156950903301^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5852014033 10000000000 156950903301 312500000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596828947/5000000000 : ℝ), (-610000227/5000000000 : ℝ), (5852014033/10000000000 : ℝ)] ![(43081742548157/100000000000000 : ℝ), (6693968384311/100000000000000 : ℝ), (156950903301/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596828947/5000000000 : ℝ)|^4613 ≤ (43081742548157/100000000000000 : ℝ)^3589
        have hw : |(2596828947/5000000000 : ℝ)|=(2596828947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-610000227/5000000000 : ℝ)|^4613 ≤ (6693968384311/100000000000000 : ℝ)^3589
        have hw : |(-610000227/5000000000 : ℝ)|=(610000227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5852014033/10000000000 : ℝ)|^4613 ≤ (156950903301/312500000000 : ℝ)^3589
        have hw : |(5852014033/10000000000 : ℝ)|=(5852014033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s0_6 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038731581/2000000000 : ℝ)*x 0 + (1170402849/2000000000 : ℝ)*x 1 + (-244000021/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038731581/2000000000 : ℝ)^4613 ≤ (10770435666359/25000000000000 : ℝ)^3589 := by
    have hnat : (1038731581 : ℕ)^4613*25000000000000^3589 ≤ 10770435666359^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038731581 2000000000 10770435666359 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1170402849/2000000000 : ℝ)^4613 ≤ (50224291394911/100000000000000 : ℝ)^3589 := by
    have hnat : (1170402849 : ℕ)^4613*100000000000000^3589 ≤ 50224291394911^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170402849 2000000000 50224291394911 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244000021/2000000000 : ℝ)^4613 ≤ (3346982961521/50000000000000 : ℝ)^3589 := by
    have hnat : (244000021 : ℕ)^4613*50000000000000^3589 ≤ 3346982961521^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244000021 2000000000 3346982961521 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038731581/2000000000 : ℝ), (1170402849/2000000000 : ℝ), (-244000021/2000000000 : ℝ)] ![(10770435666359/25000000000000 : ℝ), (50224291394911/100000000000000 : ℝ), (3346982961521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038731581/2000000000 : ℝ)|^4613 ≤ (10770435666359/25000000000000 : ℝ)^3589
        have hw : |(1038731581/2000000000 : ℝ)|=(1038731581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1170402849/2000000000 : ℝ)|^4613 ≤ (50224291394911/100000000000000 : ℝ)^3589
        have hw : |(1170402849/2000000000 : ℝ)|=(1170402849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-244000021/2000000000 : ℝ)|^4613 ≤ (3346982961521/50000000000000 : ℝ)^3589
        have hw : |(-244000021/2000000000 : ℝ)|=(244000021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s0_7 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129385169/312500000 : ℝ)*x 0 + (538327351/1000000000 : ℝ)*x 1 + (3154039301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129385169/312500000 : ℝ)^4613 ≤ (8048374926757/25000000000000 : ℝ)^3589 := by
    have hnat : (129385169 : ℕ)^4613*25000000000000^3589 ≤ 8048374926757^3589*312500000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129385169 312500000 8048374926757 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538327351/1000000000 : ℝ)^4613 ≤ (45113822637279/100000000000000 : ℝ)^3589 := by
    have hnat : (538327351 : ℕ)^4613*100000000000000^3589 ≤ 45113822637279^3589*1000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538327351 1000000000 45113822637279 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154039301/10000000000 : ℝ)^4613 ≤ (22692677644909/100000000000000 : ℝ)^3589 := by
    have hnat : (3154039301 : ℕ)^4613*100000000000000^3589 ≤ 22692677644909^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154039301 10000000000 22692677644909 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129385169/312500000 : ℝ), (538327351/1000000000 : ℝ), (3154039301/10000000000 : ℝ)] ![(8048374926757/25000000000000 : ℝ), (45113822637279/100000000000000 : ℝ), (22692677644909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129385169/312500000 : ℝ)|^4613 ≤ (8048374926757/25000000000000 : ℝ)^3589
        have hw : |(129385169/312500000 : ℝ)|=(129385169/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538327351/1000000000 : ℝ)|^4613 ≤ (45113822637279/100000000000000 : ℝ)^3589
        have hw : |(538327351/1000000000 : ℝ)|=(538327351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154039301/10000000000 : ℝ)|^4613 ≤ (22692677644909/100000000000000 : ℝ)^3589
        have hw : |(3154039301/10000000000 : ℝ)|=(3154039301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1558_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3401/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12451/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (0 : ℝ) ^ (4611/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4611 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4611*1^1024 ≤ 0^1024*1^4611 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4611 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4611/1024 : ℝ) ≤ (1614745641990064473/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4611 ≤ (1614745641990064473/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4611*100000000000000000000^1024 ≤ 1614745641990064473^1024*5^4611 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1614745641990064473 100000000000000000000 4611 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1614745641990064473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4611 := by
      have hnat : (1 : ℕ)^1024*1^4611 ≤ 1^4611*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101614745641990064473/100000000000000000000 : ℝ) ≤ (5017818397621081/5000000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (101614745641990064473/100000000000000000000 : ℝ)^1024 ≤ (5017818397621081/5000000000000000 : ℝ)^4611 := by
      have hnat : (101614745641990064473 : ℕ)^1024*5000000000000000^4611 ≤ 5017818397621081^4611*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101614745641990064473 100000000000000000000 5017818397621081 5000000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5017818397621081/5000000000000000 : ℝ)) (X := (101614745641990064473/100000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51614745641990064473/50000000000000000000 : ℝ) ≤ (2517818397621081/2500000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (51614745641990064473/50000000000000000000 : ℝ)^1024 ≤ (2517818397621081/2500000000000000 : ℝ)^4611 := by
      have hnat : (51614745641990064473 : ℕ)^1024*2500000000000000^4611 ≤ 2517818397621081^4611*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51614745641990064473 50000000000000000000 2517818397621081 2500000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2517818397621081/2500000000000000 : ℝ)) (X := (51614745641990064473/50000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(17818397621081/2000000000000000 : ℝ)*(0 : ℝ))^(4611/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17818397621081/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1614745641990064473/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(17818397621081/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4611/1024 : ℝ) := by
    rw [show (1 : ℝ)+(17818397621081/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5017818397621081/5000000000000000 : ℝ) by norm_num, show 1+(1614745641990064473/100000000000000000000 : ℝ)+(0 : ℝ)=(101614745641990064473/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1614745641990064473/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(17818397621081/2000000000000000 : ℝ)*(2/5 : ℝ))^(4611/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17818397621081/2000000000000000 : ℝ)*(2/5 : ℝ)=(2517818397621081/2500000000000000 : ℝ) by norm_num, show 1+2*(1614745641990064473/100000000000000000000 : ℝ)=(51614745641990064473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(17818397621081/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17818397621081/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(17818397621081/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17818397621081/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(17818397621081/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17818397621081/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1638114257/10000000000 : ℝ)*X 0 0+(235131153/400000000 : ℝ)*X 0 1+(2437252759/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((683505513/1250000000 : ℝ)*X 1 0+(-549377181/2500000000 : ℝ)*X 1 1+(4874505519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2734022073/5000000000 : ℝ)*X 2 0+(487450547/1000000000 : ℝ)*X 2 1+(-219750873/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4132960461/10000000000 : ℝ)*X 0 0+(309254647/1000000000 : ℝ)*X 0 1+(1360664483/2500000000 : ℝ)*X 0 2+(4132960461/10000000000 : ℝ)*X 1 0+(309254647/1000000000 : ℝ)*X 1 1+(1360664483/2500000000 : ℝ)*X 1 2+(4132960461/10000000000 : ℝ)*X 2 0+(309254647/1000000000 : ℝ)*X 2 1+(1360664483/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-65650411/400000000 : ℝ)*X 0 0+(1224967409/2500000000 : ℝ)*X 0 1+(5852014089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2596828947/5000000000 : ℝ)*X 1 0+(-610000227/5000000000 : ℝ)*X 1 1+(5852014033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1038731581/2000000000 : ℝ)*X 2 0+(1170402849/2000000000 : ℝ)*X 2 1+(-244000021/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((129385169/312500000 : ℝ)*X 0 0+(538327351/1000000000 : ℝ)*X 0 1+(3154039301/10000000000 : ℝ)*X 0 2+(129385169/312500000 : ℝ)*X 1 0+(538327351/1000000000 : ℝ)*X 1 1+(3154039301/10000000000 : ℝ)*X 1 2+(129385169/312500000 : ℝ)*X 2 0+(538327351/1000000000 : ℝ)*X 2 1+(3154039301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (885242460098009703/200000000000000000000000 : ℝ) := by norm_num
    linear_combination (42593663/100000000000000 : ℝ)*(base1) + (3693867/400000000000 : ℝ)*(base19) + (931118911/100000000000000 : ℝ)*(base23) + (7456111/6250000000000 : ℝ)*(upper3) + (119504983/100000000000000 : ℝ)*(upper5) + (355440555964969/50000000000000 : ℝ)*(major0) + (355440555964969/50000000000000 : ℝ)*(major1) + (355440555964969/50000000000000 : ℝ)*(major2) + (199248820122753/20000000000000 : ℝ)*(sp0) + (996246544875541/100000000000000 : ℝ)*(sp1) + (49812326861169/5000000000000 : ℝ)*(sp2) + (42551310969041/10000000000000 : ℝ)*(sp3) + (852580547/25000000000000 : ℝ)*(sp4) + (727846547/50000000000000 : ℝ)*(sp7) + (212757303988583/50000000000000 : ℝ)*(f.failure) + (996247468342291/100000000000000 : ℝ)*(f.sum) + (128665130938511/50000000000000000000000000000 : ℝ)*base66 + (100306261388511/100000000000000000000000000000 : ℝ)*base68 + (951105830311489/100000000000000000000000000000 : ℝ)*base69 + (191866809311489/100000000000000000000000000000 : ℝ)*base71 + (239164675888511/50000000000000000000000000000 : ℝ)*base74 + (62300952611489/100000000000000000000000000000 : ℝ)*base75 + (119419487711489/100000000000000000000000000000 : ℝ)*base77 + (316364152088511/100000000000000000000000000000 : ℝ)*base80 + (51123371211489/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2752747/312500000000000000000 : ℝ)*base90 + (2752747/312500000000000000000 : ℝ)*base92 + (2752747/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (622541330362774106366289/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8216163/625000000000 : ℝ)*(base19) + (1339802151/100000000000000 : ℝ)*(base23) + (1732153/100000000000000 : ℝ)*(base32) + (773601/390625000000 : ℝ)*(upper3) + (88499681/50000000000000 : ℝ)*(upper5) + (749422754848077/100000000000000 : ℝ)*(major0) + (749422754848077/100000000000000 : ℝ)*(major1) + (749422754848077/100000000000000 : ℝ)*(major2) + (698439227/20000000000000 : ℝ)*(sp1) + (1963694041/50000000000000 : ℝ)*(sp2) + (525130343709009/50000000000000 : ℝ)*(sp4) + (1050255880635803/100000000000000 : ℝ)*(sp5) + (210051084045557/20000000000000 : ℝ)*(sp6) + (224292306516101/50000000000000 : ℝ)*(sp7) + (89716922952871/20000000000000 : ℝ)*(f.failure) + (525130343709009/50000000000000 : ℝ)*(f.sum) + (84661020911237/100000000000000000000000000000 : ℝ)*base65 + (256462273911237/200000000000000000000000000000 : ℝ)*base67 + (1106328913288763/200000000000000000000000000000 : ℝ)*base70 + (1025544700088763/200000000000000000000000000000 : ℝ)*base72 + (769343095711237/100000000000000000000000000000 : ℝ)*base73 + (953876305688763/200000000000000000000000000000 : ℝ)*base76 + (491112995088763/200000000000000000000000000000 : ℝ)*base78 + (513358609488763/200000000000000000000000000000 : ℝ)*base80 + (67706615811237/100000000000000000000000000000 : ℝ)*base81 + (279339/125000000000000000000 : ℝ)*base90 + (279339/125000000000000000000 : ℝ)*base92 + (279339/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1558_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3401/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12451/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1558_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1558_s1_0 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-88988447/500000000 : ℝ)*x 0 + (1385439829/2500000000 : ℝ)*x 1 + (639972357/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88988447/500000000 : ℝ)^4613 ≤ (10876275199773/100000000000000 : ℝ)^3589 := by
    have hnat : (88988447 : ℕ)^4613*100000000000000^3589 ≤ 10876275199773^3589*500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88988447 500000000 10876275199773 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385439829/2500000000 : ℝ)^4613 ≤ (23414030381923/50000000000000 : ℝ)^3589 := by
    have hnat : (1385439829 : ℕ)^4613*50000000000000^3589 ≤ 23414030381923^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385439829 2500000000 23414030381923 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (639972357/1250000000 : ℝ)^4613 ≤ (4229566402047/10000000000000 : ℝ)^3589 := by
    have hnat : (639972357 : ℕ)^4613*10000000000000^3589 ≤ 4229566402047^3589*1250000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639972357 1250000000 4229566402047 10000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88988447/500000000 : ℝ), (1385439829/2500000000 : ℝ), (639972357/1250000000 : ℝ)] ![(10876275199773/100000000000000 : ℝ), (23414030381923/50000000000000 : ℝ), (4229566402047/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88988447/500000000 : ℝ)|^4613 ≤ (10876275199773/100000000000000 : ℝ)^3589
        have hw : |(-88988447/500000000 : ℝ)|=(88988447/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1385439829/2500000000 : ℝ)|^4613 ≤ (23414030381923/50000000000000 : ℝ)^3589
        have hw : |(1385439829/2500000000 : ℝ)|=(1385439829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(639972357/1250000000 : ℝ)|^4613 ≤ (4229566402047/10000000000000 : ℝ)^3589
        have hw : |(639972357/1250000000 : ℝ)|=(639972357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s1_1 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378482399/10000000000 : ℝ)*x 0 + (-2000778611/10000000000 : ℝ)*x 1 + (5119778659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378482399/10000000000 : ℝ)^4613 ≤ (11265555524059/25000000000000 : ℝ)^3589 := by
    have hnat : (5378482399 : ℕ)^4613*25000000000000^3589 ≤ 11265555524059^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378482399 10000000000 11265555524059 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000778611/10000000000 : ℝ)^4613 ≤ (3160528990001/25000000000000 : ℝ)^3589 := by
    have hnat : (2000778611 : ℕ)^4613*25000000000000^3589 ≤ 3160528990001^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000778611 10000000000 3160528990001 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5119778659/10000000000 : ℝ)^4613 ≤ (42295661928667/100000000000000 : ℝ)^3589 := by
    have hnat : (5119778659 : ℕ)^4613*100000000000000^3589 ≤ 42295661928667^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5119778659 10000000000 42295661928667 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378482399/10000000000 : ℝ), (-2000778611/10000000000 : ℝ), (5119778659/10000000000 : ℝ)] ![(11265555524059/25000000000000 : ℝ), (3160528990001/25000000000000 : ℝ), (42295661928667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378482399/10000000000 : ℝ)|^4613 ≤ (11265555524059/25000000000000 : ℝ)^3589
        have hw : |(5378482399/10000000000 : ℝ)|=(5378482399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2000778611/10000000000 : ℝ)|^4613 ≤ (3160528990001/25000000000000 : ℝ)^3589
        have hw : |(-2000778611/10000000000 : ℝ)|=(2000778611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5119778659/10000000000 : ℝ)|^4613 ≤ (42295661928667/100000000000000 : ℝ)^3589
        have hw : |(5119778659/10000000000 : ℝ)|=(5119778659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s1_2 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378482307/10000000000 : ℝ)*x 0 + (5119778453/10000000000 : ℝ)*x 1 + (-1000389501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378482307/10000000000 : ℝ)^4613 ≤ (45062221105517/100000000000000 : ℝ)^3589 := by
    have hnat : (5378482307 : ℕ)^4613*100000000000000^3589 ≤ 45062221105517^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378482307 10000000000 45062221105517 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5119778453/10000000000 : ℝ)^4613 ≤ (42295659741299/100000000000000 : ℝ)^3589 := by
    have hnat : (5119778453 : ℕ)^4613*100000000000000^3589 ≤ 42295659741299^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5119778453 10000000000 42295659741299 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000389501/5000000000 : ℝ)^4613 ≤ (1264211913547/10000000000000 : ℝ)^3589 := by
    have hnat : (1000389501 : ℕ)^4613*10000000000000^3589 ≤ 1264211913547^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000389501 5000000000 1264211913547 10000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378482307/10000000000 : ℝ), (5119778453/10000000000 : ℝ), (-1000389501/5000000000 : ℝ)] ![(45062221105517/100000000000000 : ℝ), (42295659741299/100000000000000 : ℝ), (1264211913547/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378482307/10000000000 : ℝ)|^4613 ≤ (45062221105517/100000000000000 : ℝ)^3589
        have hw : |(5378482307/10000000000 : ℝ)|=(5378482307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5119778453/10000000000 : ℝ)|^4613 ≤ (42295659741299/100000000000000 : ℝ)^3589
        have hw : |(5119778453/10000000000 : ℝ)|=(5119778453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1000389501/5000000000 : ℝ)|^4613 ≤ (1264211913547/10000000000000 : ℝ)^3589
        have hw : |(-1000389501/5000000000 : ℝ)|=(1000389501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s1_3 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2116414753/5000000000 : ℝ)*x 0 + (3762300819/10000000000 : ℝ)*x 1 + (4750273951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116414753/5000000000 : ℝ)^4613 ≤ (8280231516417/25000000000000 : ℝ)^3589 := by
    have hnat : (2116414753 : ℕ)^4613*25000000000000^3589 ≤ 8280231516417^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116414753 5000000000 8280231516417 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3762300819/10000000000 : ℝ)^4613 ≤ (28465807569349/100000000000000 : ℝ)^3589 := by
    have hnat : (3762300819 : ℕ)^4613*100000000000000^3589 ≤ 28465807569349^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3762300819 10000000000 28465807569349 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4750273951/10000000000 : ℝ)^4613 ≤ (4801658293989/12500000000000 : ℝ)^3589 := by
    have hnat : (4750273951 : ℕ)^4613*12500000000000^3589 ≤ 4801658293989^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4750273951 10000000000 4801658293989 12500000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2116414753/5000000000 : ℝ), (3762300819/10000000000 : ℝ), (4750273951/10000000000 : ℝ)] ![(8280231516417/25000000000000 : ℝ), (28465807569349/100000000000000 : ℝ), (4801658293989/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2116414753/5000000000 : ℝ)|^4613 ≤ (8280231516417/25000000000000 : ℝ)^3589
        have hw : |(2116414753/5000000000 : ℝ)|=(2116414753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3762300819/10000000000 : ℝ)|^4613 ≤ (28465807569349/100000000000000 : ℝ)^3589
        have hw : |(3762300819/10000000000 : ℝ)|=(3762300819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4750273951/10000000000 : ℝ)|^4613 ≤ (4801658293989/12500000000000 : ℝ)^3589
        have hw : |(4750273951/10000000000 : ℝ)|=(4750273951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s1_4 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-14239969/80000000 : ℝ)*x 0 + (2562101713/5000000000 : ℝ)*x 1 + (1384317063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14239969/80000000 : ℝ)^4613 ≤ (1087805968979/10000000000000 : ℝ)^3589 := by
    have hnat : (14239969 : ℕ)^4613*10000000000000^3589 ≤ 1087805968979^3589*80000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14239969 80000000 1087805968979 10000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2562101713/5000000000 : ℝ)^4613 ≤ (42342651185231/100000000000000 : ℝ)^3589 := by
    have hnat : (2562101713 : ℕ)^4613*100000000000000^3589 ≤ 42342651185231^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562101713 5000000000 42342651185231 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1384317063/2500000000 : ℝ)^4613 ≤ (11694822276123/25000000000000 : ℝ)^3589 := by
    have hnat : (1384317063 : ℕ)^4613*25000000000000^3589 ≤ 11694822276123^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384317063 2500000000 11694822276123 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14239969/80000000 : ℝ), (2562101713/5000000000 : ℝ), (1384317063/2500000000 : ℝ)] ![(1087805968979/10000000000000 : ℝ), (42342651185231/100000000000000 : ℝ), (11694822276123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14239969/80000000 : ℝ)|^4613 ≤ (1087805968979/10000000000000 : ℝ)^3589
        have hw : |(-14239969/80000000 : ℝ)|=(14239969/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2562101713/5000000000 : ℝ)|^4613 ≤ (42342651185231/100000000000000 : ℝ)^3589
        have hw : |(2562101713/5000000000 : ℝ)|=(2562101713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1384317063/2500000000 : ℝ)|^4613 ≤ (11694822276123/25000000000000 : ℝ)^3589
        have hw : |(1384317063/2500000000 : ℝ)|=(1384317063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s1_5 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053352563/2000000000 : ℝ)*x 0 + (-1583291617/10000000000 : ℝ)*x 1 + (2768633581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053352563/2000000000 : ℝ)^4613 ≤ (43862731392343/100000000000000 : ℝ)^3589 := by
    have hnat : (1053352563 : ℕ)^4613*100000000000000^3589 ≤ 43862731392343^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053352563 2000000000 43862731392343 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1583291617/10000000000 : ℝ)^4613 ≤ (9357991324183/100000000000000 : ℝ)^3589 := by
    have hnat : (1583291617 : ℕ)^4613*100000000000000^3589 ≤ 9357991324183^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583291617 10000000000 9357991324183 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2768633581/5000000000 : ℝ)^4613 ≤ (5847409658597/12500000000000 : ℝ)^3589 := by
    have hnat : (2768633581 : ℕ)^4613*12500000000000^3589 ≤ 5847409658597^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768633581 5000000000 5847409658597 12500000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053352563/2000000000 : ℝ), (-1583291617/10000000000 : ℝ), (2768633581/5000000000 : ℝ)] ![(43862731392343/100000000000000 : ℝ), (9357991324183/100000000000000 : ℝ), (5847409658597/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053352563/2000000000 : ℝ)|^4613 ≤ (43862731392343/100000000000000 : ℝ)^3589
        have hw : |(1053352563/2000000000 : ℝ)|=(1053352563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1583291617/10000000000 : ℝ)|^4613 ≤ (9357991324183/100000000000000 : ℝ)^3589
        have hw : |(-1583291617/10000000000 : ℝ)|=(1583291617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2768633581/5000000000 : ℝ)|^4613 ≤ (5847409658597/12500000000000 : ℝ)^3589
        have hw : |(2768633581/5000000000 : ℝ)|=(2768633581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s1_6 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633382513/5000000000 : ℝ)*x 0 + (2768633253/5000000000 : ℝ)*x 1 + (-1583289439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633382513/5000000000 : ℝ)^4613 ≤ (175451020239/400000000000 : ℝ)^3589 := by
    have hnat : (2633382513 : ℕ)^4613*400000000000^3589 ≤ 175451020239^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633382513 5000000000 175451020239 400000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2768633253/5000000000 : ℝ)^4613 ≤ (4677927014563/10000000000000 : ℝ)^3589 := by
    have hnat : (2768633253 : ℕ)^4613*10000000000000^3589 ≤ 4677927014563^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768633253 5000000000 4677927014563 10000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1583289439/10000000000 : ℝ)^4613 ≤ (2339493694579/25000000000000 : ℝ)^3589 := by
    have hnat : (1583289439 : ℕ)^4613*25000000000000^3589 ≤ 2339493694579^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583289439 10000000000 2339493694579 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633382513/5000000000 : ℝ), (2768633253/5000000000 : ℝ), (-1583289439/10000000000 : ℝ)] ![(175451020239/400000000000 : ℝ), (4677927014563/10000000000000 : ℝ), (2339493694579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633382513/5000000000 : ℝ)|^4613 ≤ (175451020239/400000000000 : ℝ)^3589
        have hw : |(2633382513/5000000000 : ℝ)|=(2633382513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2768633253/5000000000 : ℝ)|^4613 ≤ (4677927014563/10000000000000 : ℝ)^3589
        have hw : |(2768633253/5000000000 : ℝ)|=(2768633253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1583289439/10000000000 : ℝ)|^4613 ≤ (2339493694579/25000000000000 : ℝ)^3589
        have hw : |(-1583289439/10000000000 : ℝ)|=(1583289439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s1_7 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4233362187/10000000000 : ℝ)*x 0 + (4739912483/10000000000 : ℝ)*x 1 + (754563303/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4233362187/10000000000 : ℝ)^4613 ≤ (16563141749001/50000000000000 : ℝ)^3589 := by
    have hnat : (4233362187 : ℕ)^4613*50000000000000^3589 ≤ 16563141749001^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233362187 10000000000 16563141749001 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4739912483/10000000000 : ℝ)^4613 ≤ (38305605295639/100000000000000 : ℝ)^3589 := by
    have hnat : (4739912483 : ℕ)^4613*100000000000000^3589 ≤ 38305605295639^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4739912483 10000000000 38305605295639 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (754563303/2000000000 : ℝ)^4613 ≤ (14284055597839/50000000000000 : ℝ)^3589 := by
    have hnat : (754563303 : ℕ)^4613*50000000000000^3589 ≤ 14284055597839^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754563303 2000000000 14284055597839 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4233362187/10000000000 : ℝ), (4739912483/10000000000 : ℝ), (754563303/2000000000 : ℝ)] ![(16563141749001/50000000000000 : ℝ), (38305605295639/100000000000000 : ℝ), (14284055597839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4233362187/10000000000 : ℝ)|^4613 ≤ (16563141749001/50000000000000 : ℝ)^3589
        have hw : |(4233362187/10000000000 : ℝ)|=(4233362187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4739912483/10000000000 : ℝ)|^4613 ≤ (38305605295639/100000000000000 : ℝ)^3589
        have hw : |(4739912483/10000000000 : ℝ)|=(4739912483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(754563303/2000000000 : ℝ)|^4613 ≤ (14284055597839/50000000000000 : ℝ)^3589
        have hw : |(754563303/2000000000 : ℝ)|=(754563303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1558_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12451/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2233/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17867/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12451/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12451/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12451/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12451/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12451/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12451/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (3401/100000 : ℝ) ^ (4611/1024 : ℝ) ≤ (24430249931191/100000000000000000000 : ℝ) := by
    have hpowers : (3401/100000 : ℝ)^4611 ≤ (24430249931191/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3401 : ℕ)^4611*100000000000000000000^1024 ≤ 24430249931191^1024*100000^4611 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3401 100000 24430249931191 100000000000000000000 4611 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3401/100000 : ℝ)) (X := (24430249931191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12451/50000 : ℝ) ^ (4611/1024 : ℝ) ≤ (191110779769464113/100000000000000000000 : ℝ) := by
    have hpowers : (12451/50000 : ℝ)^4611 ≤ (191110779769464113/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12451 : ℕ)^4611*100000000000000000000^1024 ≤ 191110779769464113^1024*50000^4611 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12451 50000 191110779769464113 100000000000000000000 4611 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12451/50000 : ℝ)) (X := (191110779769464113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000024430249931191/50000000000000000000 : ℝ) ≤ (5000000542541123/5000000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (50000024430249931191/50000000000000000000 : ℝ)^1024 ≤ (5000000542541123/5000000000000000 : ℝ)^4611 := by
      have hnat : (50000024430249931191 : ℕ)^1024*5000000000000000^4611 ≤ 5000000542541123^4611*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000024430249931191 50000000000000000000 5000000542541123 5000000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000542541123/5000000000000000 : ℝ)) (X := (50000024430249931191/50000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12523891901252424413/12500000000000000000 : ℝ) ≤ (5002120766768783/5000000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (12523891901252424413/12500000000000000000 : ℝ)^1024 ≤ (5002120766768783/5000000000000000 : ℝ)^4611 := by
      have hnat : (12523891901252424413 : ℕ)^1024*5000000000000000^4611 ≤ 5002120766768783^4611*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12523891901252424413 12500000000000000000 5002120766768783 5000000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002120766768783/5000000000000000 : ℝ)) (X := (12523891901252424413/12500000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50191110779769464113/50000000000000000000 : ℝ) ≤ (5004240990996443/5000000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (50191110779769464113/50000000000000000000 : ℝ)^1024 ≤ (5004240990996443/5000000000000000 : ℝ)^4611 := by
      have hnat : (50191110779769464113 : ℕ)^1024*5000000000000000^4611 ≤ 5004240990996443^4611*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50191110779769464113 50000000000000000000 5004240990996443 5000000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004240990996443/5000000000000000 : ℝ)) (X := (50191110779769464113/50000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24430249931191/100000000000000000000 : ℝ) ≤ ((11943398877775571367/11945000000000000000 : ℝ)+2*(11779023487/5972500000000 : ℝ)*(3401/100000 : ℝ))^(4611/1024 : ℝ) := by
    rw [show (11943398877775571367/11945000000000000000 : ℝ)+2*(11779023487/5972500000000 : ℝ)*(3401/100000 : ℝ)=(5000000542541123/5000000000000000 : ℝ) by norm_num, show 1+2*(24430249931191/100000000000000000000 : ℝ)=(50000024430249931191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(191110779769464113/100000000000000000000 : ℝ)+(24430249931191/100000000000000000000 : ℝ) ≤ ((11943398877775571367/11945000000000000000 : ℝ)+(11779023487/5972500000000 : ℝ)*((12451/50000 : ℝ)+(3401/100000 : ℝ)))^(4611/1024 : ℝ) := by
    rw [show (11943398877775571367/11945000000000000000 : ℝ)+(11779023487/5972500000000 : ℝ)*((12451/50000 : ℝ)+(3401/100000 : ℝ))=(5002120766768783/5000000000000000 : ℝ) by norm_num, show 1+(191110779769464113/100000000000000000000 : ℝ)+(24430249931191/100000000000000000000 : ℝ)=(12523891901252424413/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(191110779769464113/100000000000000000000 : ℝ) ≤ ((11943398877775571367/11945000000000000000 : ℝ)+2*(11779023487/5972500000000 : ℝ)*(12451/50000 : ℝ))^(4611/1024 : ℝ) := by
    rw [show (11943398877775571367/11945000000000000000 : ℝ)+2*(11779023487/5972500000000 : ℝ)*(12451/50000 : ℝ)=(5004240990996443/5000000000000000 : ℝ) by norm_num, show 1+2*(191110779769464113/100000000000000000000 : ℝ)=(50191110779769464113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11943398877775571367/11945000000000000000 : ℝ)*(X 1 0+X 2 0)+(11779023487/5972500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (3401/100000 : ℝ)) (hi := (12451/50000 : ℝ)) (c := (11943398877775571367/11945000000000000000 : ℝ)) (alpha := (11779023487/5972500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11943398877775571367/11945000000000000000 : ℝ)*(X 0 1+X 2 1)+(11779023487/5972500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (3401/100000 : ℝ)) (hi := (12451/50000 : ℝ)) (c := (11943398877775571367/11945000000000000000 : ℝ)) (alpha := (11779023487/5972500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11943398877775571367/11945000000000000000 : ℝ)*(X 0 2+X 1 2)+(11779023487/5972500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (3401/100000 : ℝ)) (hi := (12451/50000 : ℝ)) (c := (11943398877775571367/11945000000000000000 : ℝ)) (alpha := (11779023487/5972500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-88988447/500000000 : ℝ)*X 0 0+(1385439829/2500000000 : ℝ)*X 0 1+(639972357/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5378482399/10000000000 : ℝ)*X 1 0+(-2000778611/10000000000 : ℝ)*X 1 1+(5119778659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5378482307/10000000000 : ℝ)*X 2 0+(5119778453/10000000000 : ℝ)*X 2 1+(-1000389501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2116414753/5000000000 : ℝ)*X 0 0+(3762300819/10000000000 : ℝ)*X 0 1+(4750273951/10000000000 : ℝ)*X 0 2+(2116414753/5000000000 : ℝ)*X 1 0+(3762300819/10000000000 : ℝ)*X 1 1+(4750273951/10000000000 : ℝ)*X 1 2+(2116414753/5000000000 : ℝ)*X 2 0+(3762300819/10000000000 : ℝ)*X 2 1+(4750273951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-14239969/80000000 : ℝ)*X 0 0+(2562101713/5000000000 : ℝ)*X 0 1+(1384317063/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1053352563/2000000000 : ℝ)*X 1 0+(-1583291617/10000000000 : ℝ)*X 1 1+(2768633581/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2633382513/5000000000 : ℝ)*X 2 0+(2768633253/5000000000 : ℝ)*X 2 1+(-1583289439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4233362187/10000000000 : ℝ)*X 0 0+(4739912483/10000000000 : ℝ)*X 0 1+(754563303/2000000000 : ℝ)*X 0 2+(4233362187/10000000000 : ℝ)*X 1 0+(4739912483/10000000000 : ℝ)*X 1 1+(754563303/2000000000 : ℝ)*X 1 2+(4233362187/10000000000 : ℝ)*X 2 0+(4739912483/10000000000 : ℝ)*X 2 1+(754563303/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4392346318690530426911576307/597250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27032033/25000000000000 : ℝ)*(base1) + (513776841/50000000000000 : ℝ)*(base19) + (987017979/100000000000000 : ℝ)*(base23) + (227694891/100000000000000 : ℝ)*(upper3) + (432849/20000000000000 : ℝ)*(upper5) + (1690984151582393/100000000000000 : ℝ)*(major0) + (1690984151582393/100000000000000 : ℝ)*(major1) + (1690984151582393/100000000000000 : ℝ)*(major2) + (296223215053181/12500000000000 : ℝ)*(sp0) + (29622358726763/1250000000000 : ℝ)*(sp1) + (296223592334593/12500000000000 : ℝ)*(sp2) + (506087542354453/50000000000000 : ℝ)*(sp3) + (2056698703/50000000000000 : ℝ)*(sp4) + (313949021/10000000000000 : ℝ)*(sp7) + (1012178332327247/100000000000000 : ℝ)*(f.failure) + (1184894862847361/50000000000000 : ℝ)*(f.sum) + (1536036067481/597250000000000000000000000 : ℝ)*base65 + (1943432915758141231/1194500000000000000000000000000000 : ℝ)*base67 + (6712670555892141231/1194500000000000000000000000000000 : ℝ)*base69 + (5385560617997141231/1194500000000000000000000000000000 : ℝ)*base71 + (1085137898893/597250000000000000000000000 : ℝ)*base73 + (7350075393472141231/1194500000000000000000000000000000 : ℝ)*base75 + (2422663045638858769/1194500000000000000000000000000000 : ℝ)*base78 + (2119313036047858769/1194500000000000000000000000000000 : ℝ)*base80 + (5185255407719/597250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2355277/625000000000000000000 : ℝ)*base89 + (2355277/625000000000000000000 : ℝ)*base91 + (2355277/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6525379058410431407052368373/597250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82788737/6250000000000 : ℝ)*(base19) + (184365009/6250000000000 : ℝ)*(base23) + (17909809/10000000000000 : ℝ)*(upper3) + (167037783/100000000000000 : ℝ)*(lower4) + (110334309/25000000000000 : ℝ)*(upper5) + (1727478708089073/100000000000000 : ℝ)*(major0) + (1727478708089073/100000000000000 : ℝ)*(major1) + (1727478708089073/100000000000000 : ℝ)*(major2) + (709780139/20000000000000 : ℝ)*(sp1) + (2162909951/12500000000000 : ℝ)*(sp2) + (1210467022294097/50000000000000 : ℝ)*(sp4) + (605232292766927/25000000000000 : ℝ)*(sp5) + (2420913791468443/100000000000000 : ℝ)*(sp6) + (1034023007399681/100000000000000 : ℝ)*(sp7) + (1034023007399681/100000000000000 : ℝ)*(f.failure) + (1210467022294097/50000000000000 : ℝ)*(f.sum) + (400040491307/95560000000000000000000000 : ℝ)*base65 + (812521880124872791/1194500000000000000000000000000000 : ℝ)*base67 + (1057799983877127209/1194500000000000000000000000000000 : ℝ)*base70 + (4561774158202372791/1194500000000000000000000000000000 : ℝ)*base71 + (673815012653/238900000000000000000000000 : ℝ)*base74 + (3575872652505627209/1194500000000000000000000000000000 : ℝ)*base76 + (1743901573928127209/1194500000000000000000000000000000 : ℝ)*base78 + (141410523816127209/1194500000000000000000000000000000 : ℝ)*base80 + (84612521103/47780000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3685629/625000000000000000000 : ℝ)*base90 + (3685629/625000000000000000000 : ℝ)*base92 + (3685629/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1558_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12451/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2233/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17867/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1558_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1558_s2_0 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-449868311/2500000000 : ℝ)*x 0 + (5444548171/10000000000 : ℝ)*x 1 + (5204165411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449868311/2500000000 : ℝ)^4613 ≤ (441251572643/4000000000000 : ℝ)^3589 := by
    have hnat : (449868311 : ℕ)^4613*4000000000000^3589 ≤ 441251572643^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449868311 2500000000 441251572643 4000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444548171/10000000000 : ℝ)^4613 ≤ (5721863364361/12500000000000 : ℝ)^3589 := by
    have hnat : (5444548171 : ℕ)^4613*12500000000000^3589 ≤ 5721863364361^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444548171 10000000000 5721863364361 12500000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5204165411/10000000000 : ℝ)^4613 ≤ (43193803752641/100000000000000 : ℝ)^3589 := by
    have hnat : (5204165411 : ℕ)^4613*100000000000000^3589 ≤ 43193803752641^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204165411 10000000000 43193803752641 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-449868311/2500000000 : ℝ), (5444548171/10000000000 : ℝ), (5204165411/10000000000 : ℝ)] ![(441251572643/4000000000000 : ℝ), (5721863364361/12500000000000 : ℝ), (43193803752641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-449868311/2500000000 : ℝ)|^4613 ≤ (441251572643/4000000000000 : ℝ)^3589
        have hw : |(-449868311/2500000000 : ℝ)|=(449868311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444548171/10000000000 : ℝ)|^4613 ≤ (5721863364361/12500000000000 : ℝ)^3589
        have hw : |(5444548171/10000000000 : ℝ)|=(5444548171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5204165411/10000000000 : ℝ)|^4613 ≤ (43193803752641/100000000000000 : ℝ)^3589
        have hw : |(5204165411/10000000000 : ℝ)|=(5204165411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s2_1 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353453297/10000000000 : ℝ)*x 0 + (-1922918129/10000000000 : ℝ)*x 1 + (2602082799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353453297/10000000000 : ℝ)^4613 ≤ (44792870604073/100000000000000 : ℝ)^3589 := by
    have hnat : (5353453297 : ℕ)^4613*100000000000000^3589 ≤ 44792870604073^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353453297 10000000000 44792870604073 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1922918129/10000000000 : ℝ)^4613 ≤ (2402664727259/20000000000000 : ℝ)^3589 := by
    have hnat : (1922918129 : ℕ)^4613*20000000000000^3589 ≤ 2402664727259^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922918129 10000000000 2402664727259 20000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2602082799/5000000000 : ℝ)^4613 ≤ (8638761149509/20000000000000 : ℝ)^3589 := by
    have hnat : (2602082799 : ℕ)^4613*20000000000000^3589 ≤ 8638761149509^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602082799 5000000000 8638761149509 20000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353453297/10000000000 : ℝ), (-1922918129/10000000000 : ℝ), (2602082799/5000000000 : ℝ)] ![(44792870604073/100000000000000 : ℝ), (2402664727259/20000000000000 : ℝ), (8638761149509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353453297/10000000000 : ℝ)|^4613 ≤ (44792870604073/100000000000000 : ℝ)^3589
        have hw : |(5353453297/10000000000 : ℝ)|=(5353453297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1922918129/10000000000 : ℝ)|^4613 ≤ (2402664727259/20000000000000 : ℝ)^3589
        have hw : |(-1922918129/10000000000 : ℝ)|=(1922918129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2602082799/5000000000 : ℝ)|^4613 ≤ (8638761149509/20000000000000 : ℝ)^3589
        have hw : |(2602082799/5000000000 : ℝ)|=(2602082799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s2_2 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669181599/1250000000 : ℝ)*x 0 + (5204166063/10000000000 : ℝ)*x 1 + (-961459093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669181599/1250000000 : ℝ)^4613 ≤ (44792865173117/100000000000000 : ℝ)^3589 := by
    have hnat : (669181599 : ℕ)^4613*100000000000000^3589 ≤ 44792865173117^3589*1250000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669181599 1250000000 44792865173117 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204166063/10000000000 : ℝ)^4613 ≤ (8638762141627/20000000000000 : ℝ)^3589 := by
    have hnat : (5204166063 : ℕ)^4613*20000000000000^3589 ≤ 8638762141627^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204166063 10000000000 8638762141627 20000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961459093/5000000000 : ℝ)^4613 ≤ (12013324094001/100000000000000 : ℝ)^3589 := by
    have hnat : (961459093 : ℕ)^4613*100000000000000^3589 ≤ 12013324094001^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961459093 5000000000 12013324094001 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669181599/1250000000 : ℝ), (5204166063/10000000000 : ℝ), (-961459093/5000000000 : ℝ)] ![(44792865173117/100000000000000 : ℝ), (8638762141627/20000000000000 : ℝ), (12013324094001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669181599/1250000000 : ℝ)|^4613 ≤ (44792865173117/100000000000000 : ℝ)^3589
        have hw : |(669181599/1250000000 : ℝ)|=(669181599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204166063/10000000000 : ℝ)|^4613 ≤ (8638762141627/20000000000000 : ℝ)^3589
        have hw : |(5204166063/10000000000 : ℝ)|=(5204166063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-961459093/5000000000 : ℝ)|^4613 ≤ (12013324094001/100000000000000 : ℝ)^3589
        have hw : |(-961459093/5000000000 : ℝ)|=(961459093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s2_3 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849416931/2000000000 : ℝ)*x 0 + (794660327/2000000000 : ℝ)*x 1 + (4536101933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849416931/2000000000 : ℝ)^4613 ≤ (3326436329481/10000000000000 : ℝ)^3589 := by
    have hnat : (849416931 : ℕ)^4613*10000000000000^3589 ≤ 3326436329481^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849416931 2000000000 3326436329481 10000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (794660327/2000000000 : ℝ)^4613 ≤ (30533947727467/100000000000000 : ℝ)^3589 := by
    have hnat : (794660327 : ℕ)^4613*100000000000000^3589 ≤ 30533947727467^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794660327 2000000000 30533947727467 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4536101933/10000000000 : ℝ)^4613 ≤ (36201688963993/100000000000000 : ℝ)^3589 := by
    have hnat : (4536101933 : ℕ)^4613*100000000000000^3589 ≤ 36201688963993^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536101933 10000000000 36201688963993 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849416931/2000000000 : ℝ), (794660327/2000000000 : ℝ), (4536101933/10000000000 : ℝ)] ![(3326436329481/10000000000000 : ℝ), (30533947727467/100000000000000 : ℝ), (36201688963993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849416931/2000000000 : ℝ)|^4613 ≤ (3326436329481/10000000000000 : ℝ)^3589
        have hw : |(849416931/2000000000 : ℝ)|=(849416931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(794660327/2000000000 : ℝ)|^4613 ≤ (30533947727467/100000000000000 : ℝ)^3589
        have hw : |(794660327/2000000000 : ℝ)|=(794660327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4536101933/10000000000 : ℝ)|^4613 ≤ (36201688963993/100000000000000 : ℝ)^3589
        have hw : |(4536101933/10000000000 : ℝ)|=(4536101933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s2_4 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1799515267/10000000000 : ℝ)*x 0 + (5205610077/10000000000 : ℝ)*x 1 + (1360772811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1799515267/10000000000 : ℝ)^4613 ≤ (11031620431473/100000000000000 : ℝ)^3589 := by
    have hnat : (1799515267 : ℕ)^4613*100000000000000^3589 ≤ 11031620431473^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799515267 10000000000 11031620431473 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205610077/10000000000 : ℝ)^4613 ≤ (10802303991427/25000000000000 : ℝ)^3589 := by
    have hnat : (5205610077 : ℕ)^4613*25000000000000^3589 ≤ 10802303991427^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205610077 10000000000 10802303991427 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360772811/2500000000 : ℝ)^4613 ≤ (45759163576403/100000000000000 : ℝ)^3589 := by
    have hnat : (1360772811 : ℕ)^4613*100000000000000^3589 ≤ 45759163576403^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360772811 2500000000 45759163576403 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1799515267/10000000000 : ℝ), (5205610077/10000000000 : ℝ), (1360772811/2500000000 : ℝ)] ![(11031620431473/100000000000000 : ℝ), (10802303991427/25000000000000 : ℝ), (45759163576403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1799515267/10000000000 : ℝ)|^4613 ≤ (11031620431473/100000000000000 : ℝ)^3589
        have hw : |(-1799515267/10000000000 : ℝ)|=(1799515267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205610077/10000000000 : ℝ)|^4613 ≤ (10802303991427/25000000000000 : ℝ)^3589
        have hw : |(5205610077/10000000000 : ℝ)|=(5205610077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360772811/2500000000 : ℝ)|^4613 ≤ (45759163576403/100000000000000 : ℝ)^3589
        have hw : |(1360772811/2500000000 : ℝ)|=(1360772811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s2_5 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528994061/1000000000 : ℝ)*x 0 + (-336798661/2000000000 : ℝ)*x 1 + (544309149/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528994061/1000000000 : ℝ)^4613 ≤ (2756936946153/6250000000000 : ℝ)^3589 := by
    have hnat : (528994061 : ℕ)^4613*6250000000000^3589 ≤ 2756936946153^3589*1000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528994061 1000000000 2756936946153 6250000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336798661/2000000000 : ℝ)^4613 ≤ (506492130929/5000000000000 : ℝ)^3589 := by
    have hnat : (336798661 : ℕ)^4613*5000000000000^3589 ≤ 506492130929^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336798661 2000000000 506492130929 5000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544309149/1000000000 : ℝ)^4613 ≤ (45759166234541/100000000000000 : ℝ)^3589 := by
    have hnat : (544309149 : ℕ)^4613*100000000000000^3589 ≤ 45759166234541^3589*1000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544309149 1000000000 45759166234541 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528994061/1000000000 : ℝ), (-336798661/2000000000 : ℝ), (544309149/1000000000 : ℝ)] ![(2756936946153/6250000000000 : ℝ), (506492130929/5000000000000 : ℝ), (45759166234541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528994061/1000000000 : ℝ)|^4613 ≤ (2756936946153/6250000000000 : ℝ)^3589
        have hw : |(528994061/1000000000 : ℝ)|=(528994061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-336798661/2000000000 : ℝ)|^4613 ≤ (506492130929/5000000000000 : ℝ)^3589
        have hw : |(-336798661/2000000000 : ℝ)|=(336798661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544309149/1000000000 : ℝ)|^4613 ≤ (45759166234541/100000000000000 : ℝ)^3589
        have hw : |(544309149/1000000000 : ℝ)|=(544309149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s2_6 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644970301/5000000000 : ℝ)*x 0 + (5443092741/10000000000 : ℝ)*x 1 + (-1683991567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644970301/5000000000 : ℝ)^4613 ≤ (8822198210541/20000000000000 : ℝ)^3589 := by
    have hnat : (2644970301 : ℕ)^4613*20000000000000^3589 ≤ 8822198210541^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644970301 5000000000 8822198210541 20000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443092741/10000000000 : ℝ)^4613 ≤ (11439794938037/25000000000000 : ℝ)^3589 := by
    have hnat : (5443092741 : ℕ)^4613*25000000000000^3589 ≤ 11439794938037^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443092741 10000000000 11439794938037 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1683991567/10000000000 : ℝ)^4613 ≤ (10129829180969/100000000000000 : ℝ)^3589 := by
    have hnat : (1683991567 : ℕ)^4613*100000000000000^3589 ≤ 10129829180969^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683991567 10000000000 10129829180969 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644970301/5000000000 : ℝ), (5443092741/10000000000 : ℝ), (-1683991567/10000000000 : ℝ)] ![(8822198210541/20000000000000 : ℝ), (11439794938037/25000000000000 : ℝ), (10129829180969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644970301/5000000000 : ℝ)|^4613 ≤ (8822198210541/20000000000000 : ℝ)^3589
        have hw : |(2644970301/5000000000 : ℝ)|=(2644970301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443092741/10000000000 : ℝ)|^4613 ≤ (11439794938037/25000000000000 : ℝ)^3589
        have hw : |(5443092741/10000000000 : ℝ)|=(5443092741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1683991567/10000000000 : ℝ)|^4613 ≤ (10129829180969/100000000000000 : ℝ)^3589
        have hw : |(-1683991567/10000000000 : ℝ)|=(1683991567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s2_7 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849436597/2000000000 : ℝ)*x 0 + (2266360561/5000000000 : ℝ)*x 1 + (248544479/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849436597/2000000000 : ℝ)^4613 ≤ (519771143471/1562500000000 : ℝ)^3589 := by
    have hnat : (849436597 : ℕ)^4613*1562500000000^3589 ≤ 519771143471^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849436597 2000000000 519771143471 1562500000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266360561/5000000000 : ℝ)^4613 ≤ (226043830159/625000000000 : ℝ)^3589 := by
    have hnat : (2266360561 : ℕ)^4613*625000000000^3589 ≤ 226043830159^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266360561 5000000000 226043830159 625000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248544479/625000000 : ℝ)^4613 ≤ (30567633976029/100000000000000 : ℝ)^3589 := by
    have hnat : (248544479 : ℕ)^4613*100000000000000^3589 ≤ 30567633976029^3589*625000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248544479 625000000 30567633976029 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849436597/2000000000 : ℝ), (2266360561/5000000000 : ℝ), (248544479/625000000 : ℝ)] ![(519771143471/1562500000000 : ℝ), (226043830159/625000000000 : ℝ), (30567633976029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849436597/2000000000 : ℝ)|^4613 ≤ (519771143471/1562500000000 : ℝ)^3589
        have hw : |(849436597/2000000000 : ℝ)|=(849436597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2266360561/5000000000 : ℝ)|^4613 ≤ (226043830159/625000000000 : ℝ)^3589
        have hw : |(2266360561/5000000000 : ℝ)|=(2266360561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(248544479/625000000 : ℝ)|^4613 ≤ (30567633976029/100000000000000 : ℝ)^3589
        have hw : |(248544479/625000000 : ℝ)|=(248544479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1558_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17867/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (43/400 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3169/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17867/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2233/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17867/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2233/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17867/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2233/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17867/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2233/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17867/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2233/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17867/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2233/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (2233/25000 : ℝ) ^ (4611/1024 : ℝ) ≤ (1888842831900281/100000000000000000000 : ℝ) := by
    have hpowers : (2233/25000 : ℝ)^4611 ≤ (1888842831900281/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2233 : ℕ)^4611*100000000000000000000^1024 ≤ 1888842831900281^1024*25000^4611 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2233 25000 1888842831900281 100000000000000000000 4611 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2233/25000 : ℝ)) (X := (1888842831900281/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17867/100000 : ℝ) ^ (4611/1024 : ℝ) ≤ (42858909172557457/100000000000000000000 : ℝ) := by
    have hpowers : (17867/100000 : ℝ)^4611 ≤ (42858909172557457/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17867 : ℕ)^4611*100000000000000000000^1024 ≤ 42858909172557457^1024*100000^4611 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17867 100000 42858909172557457 100000000000000000000 4611 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17867/100000 : ℝ)) (X := (42858909172557457/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001888842831900281/50000000000000000000 : ℝ) ≤ (10000083892719161/10000000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (50001888842831900281/50000000000000000000 : ℝ)^1024 ≤ (10000083892719161/10000000000000000 : ℝ)^4611 := by
      have hnat : (50001888842831900281 : ℕ)^1024*10000000000000000^4611 ≤ 10000083892719161^4611*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001888842831900281 50000000000000000000 10000083892719161 10000000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000083892719161/10000000000000000 : ℝ)) (X := (50001888842831900281/50000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022373876002228869/50000000000000000000 : ℝ) ≤ (312531049206271/312500000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (50022373876002228869/50000000000000000000 : ℝ)^1024 ≤ (312531049206271/312500000000000 : ℝ)^4611 := by
      have hnat : (50022373876002228869 : ℕ)^1024*312500000000000^4611 ≤ 312531049206271^4611*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022373876002228869 50000000000000000000 312531049206271 312500000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312531049206271/312500000000000 : ℝ)) (X := (50022373876002228869/50000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042858909172557457/50000000000000000000 : ℝ) ≤ (10001903256482183/10000000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (50042858909172557457/50000000000000000000 : ℝ)^1024 ≤ (10001903256482183/10000000000000000 : ℝ)^4611 := by
      have hnat : (50042858909172557457 : ℕ)^1024*10000000000000000^4611 ≤ 10001903256482183^4611*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042858909172557457 50000000000000000000 10001903256482183 10000000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001903256482183/10000000000000000 : ℝ)) (X := (50042858909172557457/50000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1888842831900281/100000000000000000000 : ℝ) ≤ ((89334499024314391031/89350000000000000000 : ℝ)+2*(909681881511/893500000000000 : ℝ)*(2233/25000 : ℝ))^(4611/1024 : ℝ) := by
    rw [show (89334499024314391031/89350000000000000000 : ℝ)+2*(909681881511/893500000000000 : ℝ)*(2233/25000 : ℝ)=(10000083892719161/10000000000000000 : ℝ) by norm_num, show 1+2*(1888842831900281/100000000000000000000 : ℝ)=(50001888842831900281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42858909172557457/100000000000000000000 : ℝ)+(1888842831900281/100000000000000000000 : ℝ) ≤ ((89334499024314391031/89350000000000000000 : ℝ)+(909681881511/893500000000000 : ℝ)*((17867/100000 : ℝ)+(2233/25000 : ℝ)))^(4611/1024 : ℝ) := by
    rw [show (89334499024314391031/89350000000000000000 : ℝ)+(909681881511/893500000000000 : ℝ)*((17867/100000 : ℝ)+(2233/25000 : ℝ))=(312531049206271/312500000000000 : ℝ) by norm_num, show 1+(42858909172557457/100000000000000000000 : ℝ)+(1888842831900281/100000000000000000000 : ℝ)=(50022373876002228869/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42858909172557457/100000000000000000000 : ℝ) ≤ ((89334499024314391031/89350000000000000000 : ℝ)+2*(909681881511/893500000000000 : ℝ)*(17867/100000 : ℝ))^(4611/1024 : ℝ) := by
    rw [show (89334499024314391031/89350000000000000000 : ℝ)+2*(909681881511/893500000000000 : ℝ)*(17867/100000 : ℝ)=(10001903256482183/10000000000000000 : ℝ) by norm_num, show 1+2*(42858909172557457/100000000000000000000 : ℝ)=(50042858909172557457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (89334499024314391031/89350000000000000000 : ℝ)*(X 1 0+X 2 0)+(909681881511/893500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (2233/25000 : ℝ)) (hi := (17867/100000 : ℝ)) (c := (89334499024314391031/89350000000000000000 : ℝ)) (alpha := (909681881511/893500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (89334499024314391031/89350000000000000000 : ℝ)*(X 0 1+X 2 1)+(909681881511/893500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (2233/25000 : ℝ)) (hi := (17867/100000 : ℝ)) (c := (89334499024314391031/89350000000000000000 : ℝ)) (alpha := (909681881511/893500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (89334499024314391031/89350000000000000000 : ℝ)*(X 0 2+X 1 2)+(909681881511/893500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (2233/25000 : ℝ)) (hi := (17867/100000 : ℝ)) (c := (89334499024314391031/89350000000000000000 : ℝ)) (alpha := (909681881511/893500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-449868311/2500000000 : ℝ)*X 0 0+(5444548171/10000000000 : ℝ)*X 0 1+(5204165411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353453297/10000000000 : ℝ)*X 1 0+(-1922918129/10000000000 : ℝ)*X 1 1+(2602082799/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669181599/1250000000 : ℝ)*X 2 0+(5204166063/10000000000 : ℝ)*X 2 1+(-961459093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((849416931/2000000000 : ℝ)*X 0 0+(794660327/2000000000 : ℝ)*X 0 1+(4536101933/10000000000 : ℝ)*X 0 2+(849416931/2000000000 : ℝ)*X 1 0+(794660327/2000000000 : ℝ)*X 1 1+(4536101933/10000000000 : ℝ)*X 1 2+(849416931/2000000000 : ℝ)*X 2 0+(794660327/2000000000 : ℝ)*X 2 1+(4536101933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1799515267/10000000000 : ℝ)*X 0 0+(5205610077/10000000000 : ℝ)*X 0 1+(1360772811/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528994061/1000000000 : ℝ)*X 1 0+(-336798661/2000000000 : ℝ)*X 1 1+(544309149/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644970301/5000000000 : ℝ)*X 2 0+(5443092741/10000000000 : ℝ)*X 2 1+(-1683991567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((849436597/2000000000 : ℝ)*X 0 0+(2266360561/5000000000 : ℝ)*X 0 1+(248544479/625000000 : ℝ)*X 0 2+(849436597/2000000000 : ℝ)*X 1 0+(2266360561/5000000000 : ℝ)*X 1 1+(248544479/625000000 : ℝ)*X 1 2+(849436597/2000000000 : ℝ)*X 2 0+(2266360561/5000000000 : ℝ)*X 2 1+(248544479/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4287382433191617635468222307/446750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42411781/3125000000000 : ℝ)*(base19) + (775224493/100000000000000 : ℝ)*(base23) + (188070779/100000000000000 : ℝ)*(lower2) + (51673691/20000000000000 : ℝ)*(upper3) + (21652287/25000000000000 : ℝ)*(lower4) + (593692041297799/20000000000000 : ℝ)*(major0) + (593692041297799/20000000000000 : ℝ)*(major1) + (593692041297799/20000000000000 : ℝ)*(major2) + (4160058740410827/100000000000000 : ℝ)*(sp0) + (2080038533679987/50000000000000 : ℝ)*(sp1) + (2080038824656237/50000000000000 : ℝ)*(sp2) + (1776834296363969/100000000000000 : ℝ)*(sp3) + (984206307/5000000000000 : ℝ)*(sp4) + (3686091407/50000000000000 : ℝ)*(sp7) + (55526302142087/3125000000000 : ℝ)*(f.failure) + (2080039212268483/50000000000000 : ℝ)*(f.sum) + (8045291621553/4467500000000000000000000000 : ℝ)*base66 + (10942444672305459231/1787000000000000000000000000000000 : ℝ)*base68 + (11110727909775459231/1787000000000000000000000000000000 : ℝ)*base70 + (2912208031446459231/1787000000000000000000000000000000 : ℝ)*base72 + (5600264234897/4467500000000000000000000000 : ℝ)*base73 + (19010673547359540769/1787000000000000000000000000000000 : ℝ)*base75 + (15277520954756459231/1787000000000000000000000000000000 : ℝ)*base78 + (9546457543660459231/1787000000000000000000000000000000 : ℝ)*base80 + (7368550665063/4467500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (591559/39062500000000000000 : ℝ)*base89 + (591559/39062500000000000000 : ℝ)*base91 + (591559/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7534785787172058474186654249/558437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7903719/5000000000000 : ℝ)*(base19) + (587221817/50000000000000 : ℝ)*(base23) + (41801011/25000000000000 : ℝ)*(upper3) + (145185401/50000000000000 : ℝ)*(lower4) + (144246581/100000000000000 : ℝ)*(upper5) + (375586748691293/12500000000000 : ℝ)*(major0) + (375586748691293/12500000000000 : ℝ)*(major1) + (375586748691293/12500000000000 : ℝ)*(major2) + (352247023/100000000000000 : ℝ)*(sp1) + (39817300739/100000000000000 : ℝ)*(sp2) + (1052714319444483/25000000000000 : ℝ)*(sp4) + (421085676745653/10000000000000 : ℝ)*(sp5) + (105270407150839/2500000000000 : ℝ)*(sp6) + (1798530251528699/100000000000000 : ℝ)*(sp7) + (1798530251528699/100000000000000 : ℝ)*(f.failure) + (1052714319444483/25000000000000 : ℝ)*(f.sum) + (168585546057141/44675000000000000000000000000 : ℝ)*base66 + (1079117387595543083/1116875000000000000000000000000000 : ℝ)*base67 + (694609153799293083/1116875000000000000000000000000000 : ℝ)*base69 + (9427720668871956917/1116875000000000000000000000000000 : ℝ)*base72 + (158429577860391/44675000000000000000000000000 : ℝ)*base74 + (9398385884451956917/1116875000000000000000000000000000 : ℝ)*base76 + (3382465275746331917/1116875000000000000000000000000000 : ℝ)*base78 + (16008609684036331917/1116875000000000000000000000000000 : ℝ)*base80 + (13804178928717/22337500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3149791/625000000000000000000 : ℝ)*base90 + (3149791/625000000000000000000 : ℝ)*base92 + (3149791/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1558_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17867/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (43/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3169/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1558_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1558_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (43/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3169/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1558_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1558_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1558_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (43/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3169/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1558_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
