-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1081_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:50:13.077707+00:00
-- url     : https://prove2.me/submissions/cb51c17b-43c2-4663-9c0a-8a254a011705

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
theorem support_rectangle_w1081_s9_0 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098203501/5000000000 : ℝ)*x 0 + (2697033057/5000000000 : ℝ)*x 1 + (131618777/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098203501/5000000000 : ℝ)^4137 ≤ (6670275481939/50000000000000 : ℝ)^3113 := by
    have hnat : (1098203501 : ℕ)^4137*50000000000000^3113 ≤ 6670275481939^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098203501 5000000000 6670275481939 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697033057/5000000000 : ℝ)^4137 ≤ (44028304283393/100000000000000 : ℝ)^3113 := by
    have hnat : (2697033057 : ℕ)^4137*100000000000000^3113 ≤ 44028304283393^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697033057 5000000000 44028304283393 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131618777/250000000 : ℝ)^4137 ≤ (2131557236569/5000000000000 : ℝ)^3113 := by
    have hnat : (131618777 : ℕ)^4137*5000000000000^3113 ≤ 2131557236569^3113*250000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131618777 250000000 2131557236569 5000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098203501/5000000000 : ℝ), (2697033057/5000000000 : ℝ), (131618777/250000000 : ℝ)] ![(6670275481939/50000000000000 : ℝ), (44028304283393/100000000000000 : ℝ), (2131557236569/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098203501/5000000000 : ℝ)|^4137 ≤ (6670275481939/50000000000000 : ℝ)^3113
        have hw : |(-1098203501/5000000000 : ℝ)|=(1098203501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697033057/5000000000 : ℝ)|^4137 ≤ (44028304283393/100000000000000 : ℝ)^3113
        have hw : |(2697033057/5000000000 : ℝ)|=(2697033057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131618777/250000000 : ℝ)|^4137 ≤ (2131557236569/5000000000000 : ℝ)^3113
        have hw : |(131618777/250000000 : ℝ)|=(131618777/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s9_1 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672467567/5000000000 : ℝ)*x 0 + (-282751573/1250000000 : ℝ)*x 1 + (2632375691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672467567/5000000000 : ℝ)^4137 ≤ (2174808263479/5000000000000 : ℝ)^3113 := by
    have hnat : (2672467567 : ℕ)^4137*5000000000000^3113 ≤ 2174808263479^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672467567 5000000000 2174808263479 5000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282751573/1250000000 : ℝ)^4137 ≤ (3468171684371/25000000000000 : ℝ)^3113 := by
    have hnat : (282751573 : ℕ)^4137*25000000000000^3113 ≤ 3468171684371^3113*1250000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282751573 1250000000 3468171684371 25000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632375691/5000000000 : ℝ)^4137 ≤ (5328893497653/12500000000000 : ℝ)^3113 := by
    have hnat : (2632375691 : ℕ)^4137*12500000000000^3113 ≤ 5328893497653^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632375691 5000000000 5328893497653 12500000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672467567/5000000000 : ℝ), (-282751573/1250000000 : ℝ), (2632375691/5000000000 : ℝ)] ![(2174808263479/5000000000000 : ℝ), (3468171684371/25000000000000 : ℝ), (5328893497653/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672467567/5000000000 : ℝ)|^4137 ≤ (2174808263479/5000000000000 : ℝ)^3113
        have hw : |(2672467567/5000000000 : ℝ)|=(2672467567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-282751573/1250000000 : ℝ)|^4137 ≤ (3468171684371/25000000000000 : ℝ)^3113
        have hw : |(-282751573/1250000000 : ℝ)|=(282751573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632375691/5000000000 : ℝ)|^4137 ≤ (5328893497653/12500000000000 : ℝ)^3113
        have hw : |(2632375691/5000000000 : ℝ)|=(2632375691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s9_2 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672467709/5000000000 : ℝ)*x 0 + (1052950237/2000000000 : ℝ)*x 1 + (-2262012467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672467709/5000000000 : ℝ)^4137 ≤ (21748084170479/50000000000000 : ℝ)^3113 := by
    have hnat : (2672467709 : ℕ)^4137*50000000000000^3113 ≤ 21748084170479^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672467709 5000000000 21748084170479 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052950237/2000000000 : ℝ)^4137 ≤ (42631145861293/100000000000000 : ℝ)^3113 := by
    have hnat : (1052950237 : ℕ)^4137*100000000000000^3113 ≤ 42631145861293^3113*2000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052950237 2000000000 42631145861293 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262012467/10000000000 : ℝ)^4137 ≤ (13872685783903/100000000000000 : ℝ)^3113 := by
    have hnat : (2262012467 : ℕ)^4137*100000000000000^3113 ≤ 13872685783903^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262012467 10000000000 13872685783903 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672467709/5000000000 : ℝ), (1052950237/2000000000 : ℝ), (-2262012467/10000000000 : ℝ)] ![(21748084170479/50000000000000 : ℝ), (42631145861293/100000000000000 : ℝ), (13872685783903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672467709/5000000000 : ℝ)|^4137 ≤ (21748084170479/50000000000000 : ℝ)^3113
        have hw : |(2672467709/5000000000 : ℝ)|=(2672467709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052950237/2000000000 : ℝ)|^4137 ≤ (42631145861293/100000000000000 : ℝ)^3113
        have hw : |(1052950237/2000000000 : ℝ)|=(1052950237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2262012467/10000000000 : ℝ)|^4137 ≤ (13872685783903/100000000000000 : ℝ)^3113
        have hw : |(-2262012467/10000000000 : ℝ)|=(2262012467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s9_3 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4373340933/10000000000 : ℝ)*x 0 + (1062027167/2500000000 : ℝ)*x 1 + (900460289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373340933/10000000000 : ℝ)^4137 ≤ (2082290713699/6250000000000 : ℝ)^3113 := by
    have hnat : (4373340933 : ℕ)^4137*6250000000000^3113 ≤ 2082290713699^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373340933 10000000000 2082290713699 6250000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062027167/2500000000 : ℝ)^4137 ≤ (32054803281059/100000000000000 : ℝ)^3113 := by
    have hnat : (1062027167 : ℕ)^4137*100000000000000^3113 ≤ 32054803281059^3113*2500000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062027167 2500000000 32054803281059 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900460289/2000000000 : ℝ)^4137 ≤ (34628545283871/100000000000000 : ℝ)^3113 := by
    have hnat : (900460289 : ℕ)^4137*100000000000000^3113 ≤ 34628545283871^3113*2000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900460289 2000000000 34628545283871 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373340933/10000000000 : ℝ), (1062027167/2500000000 : ℝ), (900460289/2000000000 : ℝ)] ![(2082290713699/6250000000000 : ℝ), (32054803281059/100000000000000 : ℝ), (34628545283871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373340933/10000000000 : ℝ)|^4137 ≤ (2082290713699/6250000000000 : ℝ)^3113
        have hw : |(4373340933/10000000000 : ℝ)|=(4373340933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062027167/2500000000 : ℝ)|^4137 ≤ (32054803281059/100000000000000 : ℝ)^3113
        have hw : |(1062027167/2500000000 : ℝ)|=(1062027167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900460289/2000000000 : ℝ)|^4137 ≤ (34628545283871/100000000000000 : ℝ)^3113
        have hw : |(900460289/2000000000 : ℝ)|=(900460289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s9_4 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098205907/5000000000 : ℝ)*x 0 + (658134387/1250000000 : ℝ)*x 1 + (168554409/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098205907/5000000000 : ℝ)^4137 ≤ (13340589805121/100000000000000 : ℝ)^3113 := by
    have hnat : (1098205907 : ℕ)^4137*100000000000000^3113 ≤ 13340589805121^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098205907 5000000000 13340589805121 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658134387/1250000000 : ℝ)^4137 ≤ (42634631526301/100000000000000 : ℝ)^3113 := by
    have hnat : (658134387 : ℕ)^4137*100000000000000^3113 ≤ 42634631526301^3113*1250000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658134387 1250000000 42634631526301 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168554409/312500000 : ℝ)^4137 ≤ (4402477866021/10000000000000 : ℝ)^3113 := by
    have hnat : (168554409 : ℕ)^4137*10000000000000^3113 ≤ 4402477866021^3113*312500000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168554409 312500000 4402477866021 10000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098205907/5000000000 : ℝ), (658134387/1250000000 : ℝ), (168554409/312500000 : ℝ)] ![(13340589805121/100000000000000 : ℝ), (42634631526301/100000000000000 : ℝ), (4402477866021/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098205907/5000000000 : ℝ)|^4137 ≤ (13340589805121/100000000000000 : ℝ)^3113
        have hw : |(-1098205907/5000000000 : ℝ)|=(1098205907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658134387/1250000000 : ℝ)|^4137 ≤ (42634631526301/100000000000000 : ℝ)^3113
        have hw : |(658134387/1250000000 : ℝ)|=(658134387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168554409/312500000 : ℝ)|^4137 ≤ (4402477866021/10000000000000 : ℝ)^3113
        have hw : |(168554409/312500000 : ℝ)|=(168554409/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s9_5 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546668809/1250000000 : ℝ)*x 0 + (1125416323/2500000000 : ℝ)*x 1 + (4248747437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546668809/1250000000 : ℝ)^4137 ≤ (33316747992561/100000000000000 : ℝ)^3113 := by
    have hnat : (546668809 : ℕ)^4137*100000000000000^3113 ≤ 33316747992561^3113*1250000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546668809 1250000000 33316747992561 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125416323/2500000000 : ℝ)^4137 ≤ (8655510781293/25000000000000 : ℝ)^3113 := by
    have hnat : (1125416323 : ℕ)^4137*25000000000000^3113 ≤ 8655510781293^3113*2500000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125416323 2500000000 8655510781293 25000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4248747437/10000000000 : ℝ)^4137 ≤ (8015302215303/25000000000000 : ℝ)^3113 := by
    have hnat : (4248747437 : ℕ)^4137*25000000000000^3113 ≤ 8015302215303^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248747437 10000000000 8015302215303 25000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546668809/1250000000 : ℝ), (1125416323/2500000000 : ℝ), (4248747437/10000000000 : ℝ)] ![(33316747992561/100000000000000 : ℝ), (8655510781293/25000000000000 : ℝ), (8015302215303/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546668809/1250000000 : ℝ)|^4137 ≤ (33316747992561/100000000000000 : ℝ)^3113
        have hw : |(546668809/1250000000 : ℝ)|=(546668809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125416323/2500000000 : ℝ)|^4137 ≤ (8655510781293/25000000000000 : ℝ)^3113
        have hw : |(1125416323/2500000000 : ℝ)|=(1125416323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4248747437/10000000000 : ℝ)|^4137 ≤ (8015302215303/25000000000000 : ℝ)^3113
        have hw : |(4248747437/10000000000 : ℝ)|=(4248747437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1081_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11273/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3503/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1409/12500 : ℝ) ^ (8273/2048 : ℝ) ≤ (2961691467796527/20000000000000000000 : ℝ) := by
    have hpowers : (1409/12500 : ℝ)^8273 ≤ (2961691467796527/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1409 : ℕ)^8273*20000000000000000000^2048 ≤ 2961691467796527^2048*12500^8273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 12500 2961691467796527 20000000000000000000 8273 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/12500 : ℝ)) (X := (2961691467796527/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3503/25000 : ℝ) ^ (8273/2048 : ℝ) ≤ (17832569783750107/50000000000000000000 : ℝ) := by
    have hpowers : (3503/25000 : ℝ)^8273 ≤ (17832569783750107/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3503 : ℕ)^8273*50000000000000000000^2048 ≤ 17832569783750107^2048*25000^8273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3503 25000 17832569783750107 50000000000000000000 8273 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3503/25000 : ℝ)) (X := (17832569783750107/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002961691467796527/10000000000000000000 : ℝ) ≤ (5000366545895337/5000000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (10002961691467796527/10000000000000000000 : ℝ)^2048 ≤ (5000366545895337/5000000000000000 : ℝ)^8273 := by
      have hnat : (10002961691467796527 : ℕ)^2048*5000000000000000^8273 ≤ 5000366545895337^8273*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002961691467796527 10000000000000000000 5000366545895337 5000000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000366545895337/5000000000000000 : ℝ)) (X := (10002961691467796527/10000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050473596906482849/100000000000000000000 : ℝ) ≤ (10001249248192321/10000000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (100050473596906482849/100000000000000000000 : ℝ)^2048 ≤ (10001249248192321/10000000000000000 : ℝ)^8273 := by
      have hnat : (100050473596906482849 : ℕ)^2048*10000000000000000^8273 ≤ 10001249248192321^8273*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050473596906482849 100000000000000000000 10001249248192321 10000000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001249248192321/10000000000000000 : ℝ)) (X := (100050473596906482849/100000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017832569783750107/25000000000000000000 : ℝ) ≤ (625110337787123/625000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (25017832569783750107/25000000000000000000 : ℝ)^2048 ≤ (625110337787123/625000000000000 : ℝ)^8273 := by
      have hnat : (25017832569783750107 : ℕ)^2048*625000000000000^8273 ≤ 625110337787123^8273*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017832569783750107 25000000000000000000 625110337787123 625000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625110337787123/625000000000000 : ℝ)) (X := (25017832569783750107/25000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2961691467796527/20000000000000000000 : ℝ) ≤ ((3423796555198464599/3425000000000000000 : ℝ)+2*(516156401647/274000000000000 : ℝ)*(1409/12500 : ℝ))^(8273/2048 : ℝ) := by
    rw [show (3423796555198464599/3425000000000000000 : ℝ)+2*(516156401647/274000000000000 : ℝ)*(1409/12500 : ℝ)=(5000366545895337/5000000000000000 : ℝ) by norm_num, show 1+2*(2961691467796527/20000000000000000000 : ℝ)=(10002961691467796527/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17832569783750107/50000000000000000000 : ℝ)+(2961691467796527/20000000000000000000 : ℝ) ≤ ((3423796555198464599/3425000000000000000 : ℝ)+(516156401647/274000000000000 : ℝ)*((3503/25000 : ℝ)+(1409/12500 : ℝ)))^(8273/2048 : ℝ) := by
    rw [show (3423796555198464599/3425000000000000000 : ℝ)+(516156401647/274000000000000 : ℝ)*((3503/25000 : ℝ)+(1409/12500 : ℝ))=(10001249248192321/10000000000000000 : ℝ) by norm_num, show 1+(17832569783750107/50000000000000000000 : ℝ)+(2961691467796527/20000000000000000000 : ℝ)=(100050473596906482849/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17832569783750107/50000000000000000000 : ℝ) ≤ ((3423796555198464599/3425000000000000000 : ℝ)+2*(516156401647/274000000000000 : ℝ)*(3503/25000 : ℝ))^(8273/2048 : ℝ) := by
    rw [show (3423796555198464599/3425000000000000000 : ℝ)+2*(516156401647/274000000000000 : ℝ)*(3503/25000 : ℝ)=(625110337787123/625000000000000 : ℝ) by norm_num, show 1+2*(17832569783750107/50000000000000000000 : ℝ)=(25017832569783750107/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3423796555198464599/3425000000000000000 : ℝ)*(X 1 0+X 2 0)+(516156401647/274000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (3423796555198464599/3425000000000000000 : ℝ)) (alpha := (516156401647/274000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3423796555198464599/3425000000000000000 : ℝ)*(X 0 1+X 2 1)+(516156401647/274000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (3423796555198464599/3425000000000000000 : ℝ)) (alpha := (516156401647/274000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3423796555198464599/3425000000000000000 : ℝ)*(X 0 2+X 1 2)+(516156401647/274000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (3423796555198464599/3425000000000000000 : ℝ)) (alpha := (516156401647/274000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1098203501/5000000000 : ℝ)*X 0 0+(2697033057/5000000000 : ℝ)*X 0 1+(131618777/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672467567/5000000000 : ℝ)*X 1 0+(-282751573/1250000000 : ℝ)*X 1 1+(2632375691/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672467709/5000000000 : ℝ)*X 2 0+(1052950237/2000000000 : ℝ)*X 2 1+(-2262012467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4373340933/10000000000 : ℝ)*X 0 0+(1062027167/2500000000 : ℝ)*X 0 1+(900460289/2000000000 : ℝ)*X 0 2+(4373340933/10000000000 : ℝ)*X 1 0+(1062027167/2500000000 : ℝ)*X 1 1+(900460289/2000000000 : ℝ)*X 1 2+(4373340933/10000000000 : ℝ)*X 2 0+(1062027167/2500000000 : ℝ)*X 2 1+(900460289/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1098205907/5000000000 : ℝ)*X 0 0+(658134387/1250000000 : ℝ)*X 0 1+(168554409/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((546668809/1250000000 : ℝ)*X 0 0+(1125416323/2500000000 : ℝ)*X 0 1+(4248747437/10000000000 : ℝ)*X 0 2+(546668809/1250000000 : ℝ)*X 1 0+(1125416323/2500000000 : ℝ)*X 1 1+(4248747437/10000000000 : ℝ)*X 1 2+(546668809/1250000000 : ℝ)*X 2 0+(1125416323/2500000000 : ℝ)*X 2 1+(4248747437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (487715638521087169765131/625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (509869963/50000000000000 : ℝ)*(base19) + (1136720203/100000000000000 : ℝ)*(base23) + (28501959/20000000000000 : ℝ)*(upper3) + (157095671/100000000000000 : ℝ)*(upper4) + (19135541/10000000000000 : ℝ)*(upper5) + (2916791809251951/50000000000000 : ℝ)*(major0) + (2916791809251951/50000000000000 : ℝ)*(major1) + (2916791809251951/50000000000000 : ℝ)*(major2) + (966635738058739/12500000000000 : ℝ)*(sp0) + (309325175071079/4000000000000 : ℝ)*(sp1) + (3866564629898349/50000000000000 : ℝ)*(sp2) + (3934028091287041/100000000000000 : ℝ)*(sp3) + (44492046989/100000000000000 : ℝ)*(sp4) + (4361596179/50000000000000 : ℝ)*(sp5) + (3934036814479399/100000000000000 : ℝ)*(f.failure) + (7733130396516901/100000000000000 : ℝ)*(f.sum) + (44277807269/50000000000000000000000000 : ℝ)*base66 + (3419306546924123/1250000000000000000000000000000 : ℝ)*base68 + (201953644325877/1250000000000000000000000000000 : ℝ)*base69 + (5976038399325877/1250000000000000000000000000000 : ℝ)*base71 + (195226115519/50000000000000000000000000 : ℝ)*base74 + (9812471928174123/1250000000000000000000000000000 : ℝ)*base76 + (3098849243174123/1250000000000000000000000000000 : ℝ)*base78 + (7615730569424123/1250000000000000000000000000000 : ℝ)*base80 + (76365374431/50000000000000000000000000 : ℝ)*base81 + (23718873/10000000000000000000000 : ℝ)*base89 + (23718873/10000000000000000000000 : ℝ)*base91 + (23718873/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1081_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1081_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1081_box_0 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-25843251/125000000 : ℝ)*x 0 + (53771631/100000000 : ℝ)*x 1 + (2688581409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25843251/125000000 : ℝ)^4137 ≤ (12309909848157/100000000000000 : ℝ)^3113 := by
    have hnat : (25843251 : ℕ)^4137*100000000000000^3113 ≤ 12309909848157^3113*125000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25843251 125000000 12309909848157 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53771631/100000000 : ℝ)^4137 ≤ (21922523298761/50000000000000 : ℝ)^3113 := by
    have hnat : (53771631 : ℕ)^4137*50000000000000^3113 ≤ 21922523298761^3113*100000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53771631 100000000 21922523298761 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688581409/5000000000 : ℝ)^4137 ≤ (43845043541737/100000000000000 : ℝ)^3113 := by
    have hnat : (2688581409 : ℕ)^4137*100000000000000^3113 ≤ 43845043541737^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688581409 5000000000 43845043541737 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25843251/125000000 : ℝ), (53771631/100000000 : ℝ), (2688581409/5000000000 : ℝ)] ![(12309909848157/100000000000000 : ℝ), (21922523298761/50000000000000 : ℝ), (43845043541737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25843251/125000000 : ℝ)|^4137 ≤ (12309909848157/100000000000000 : ℝ)^3113
        have hw : |(-25843251/125000000 : ℝ)|=(25843251/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53771631/100000000 : ℝ)|^4137 ≤ (21922523298761/50000000000000 : ℝ)^3113
        have hw : |(53771631/100000000 : ℝ)|=(53771631/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688581409/5000000000 : ℝ)|^4137 ≤ (43845043541737/100000000000000 : ℝ)^3113
        have hw : |(2688581409/5000000000 : ℝ)|=(2688581409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_1 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647685483/5000000000 : ℝ)*x 0 + (-2178225339/10000000000 : ℝ)*x 1 + (2688581441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647685483/5000000000 : ℝ)^4137 ≤ (42960962324069/100000000000000 : ℝ)^3113 := by
    have hnat : (2647685483 : ℕ)^4137*100000000000000^3113 ≤ 42960962324069^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647685483 5000000000 42960962324069 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178225339/10000000000 : ℝ)^4137 ≤ (824624589049/6250000000000 : ℝ)^3113 := by
    have hnat : (2178225339 : ℕ)^4137*6250000000000^3113 ≤ 824624589049^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178225339 10000000000 824624589049 6250000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688581441/5000000000 : ℝ)^4137 ≤ (43845044235249/100000000000000 : ℝ)^3113 := by
    have hnat : (2688581441 : ℕ)^4137*100000000000000^3113 ≤ 43845044235249^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688581441 5000000000 43845044235249 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647685483/5000000000 : ℝ), (-2178225339/10000000000 : ℝ), (2688581441/5000000000 : ℝ)] ![(42960962324069/100000000000000 : ℝ), (824624589049/6250000000000 : ℝ), (43845044235249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647685483/5000000000 : ℝ)|^4137 ≤ (42960962324069/100000000000000 : ℝ)^3113
        have hw : |(2647685483/5000000000 : ℝ)|=(2647685483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178225339/10000000000 : ℝ)|^4137 ≤ (824624589049/6250000000000 : ℝ)^3113
        have hw : |(-2178225339/10000000000 : ℝ)|=(2178225339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688581441/5000000000 : ℝ)|^4137 ≤ (43845044235249/100000000000000 : ℝ)^3113
        have hw : |(2688581441/5000000000 : ℝ)|=(2688581441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_2 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059074141/2000000000 : ℝ)*x 0 + (168036343/312500000 : ℝ)*x 1 + (-1089112781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059074141/2000000000 : ℝ)^4137 ≤ (21480479755033/50000000000000 : ℝ)^3113 := by
    have hnat : (1059074141 : ℕ)^4137*50000000000000^3113 ≤ 21480479755033^3113*2000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059074141 2000000000 21480479755033 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168036343/312500000 : ℝ)^4137 ≤ (10961261313461/25000000000000 : ℝ)^3113 := by
    have hnat : (168036343 : ℕ)^4137*25000000000000^3113 ≤ 10961261313461^3113*312500000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168036343 312500000 10961261313461 25000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089112781/5000000000 : ℝ)^4137 ≤ (13193995219867/100000000000000 : ℝ)^3113 := by
    have hnat : (1089112781 : ℕ)^4137*100000000000000^3113 ≤ 13193995219867^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089112781 5000000000 13193995219867 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059074141/2000000000 : ℝ), (168036343/312500000 : ℝ), (-1089112781/5000000000 : ℝ)] ![(21480479755033/50000000000000 : ℝ), (10961261313461/25000000000000 : ℝ), (13193995219867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059074141/2000000000 : ℝ)|^4137 ≤ (21480479755033/50000000000000 : ℝ)^3113
        have hw : |(1059074141/2000000000 : ℝ)|=(1059074141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168036343/312500000 : ℝ)|^4137 ≤ (10961261313461/25000000000000 : ℝ)^3113
        have hw : |(168036343/312500000 : ℝ)|=(168036343/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1089112781/5000000000 : ℝ)|^4137 ≤ (13193995219867/100000000000000 : ℝ)^3113
        have hw : |(-1089112781/5000000000 : ℝ)|=(1089112781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_3 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2240777307/5000000000 : ℝ)*x 0 + (135043289/312500000 : ℝ)*x 1 + (270086539/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2240777307/5000000000 : ℝ)^4137 ≤ (17208323306151/50000000000000 : ℝ)^3113 := by
    have hnat : (2240777307 : ℕ)^4137*50000000000000^3113 ≤ 17208323306151^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240777307 5000000000 17208323306151 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135043289/312500000 : ℝ)^4137 ≤ (16395839915161/50000000000000 : ℝ)^3113 := by
    have hnat : (135043289 : ℕ)^4137*50000000000000^3113 ≤ 16395839915161^3113*312500000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135043289 312500000 16395839915161 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270086539/625000000 : ℝ)^4137 ≤ (327916735377/1000000000000 : ℝ)^3113 := by
    have hnat : (270086539 : ℕ)^4137*1000000000000^3113 ≤ 327916735377^3113*625000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270086539 625000000 327916735377 1000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2240777307/5000000000 : ℝ), (135043289/312500000 : ℝ), (270086539/625000000 : ℝ)] ![(17208323306151/50000000000000 : ℝ), (16395839915161/50000000000000 : ℝ), (327916735377/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2240777307/5000000000 : ℝ)|^4137 ≤ (17208323306151/50000000000000 : ℝ)^3113
        have hw : |(2240777307/5000000000 : ℝ)|=(2240777307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135043289/312500000 : ℝ)|^4137 ≤ (16395839915161/50000000000000 : ℝ)^3113
        have hw : |(135043289/312500000 : ℝ)|=(135043289/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270086539/625000000 : ℝ)|^4137 ≤ (327916735377/1000000000000 : ℝ)^3113
        have hw : |(270086539/625000000 : ℝ)|=(270086539/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_4 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-36355193/156250000 : ℝ)*x 0 + (2640156151/5000000000 : ℝ)*x 1 + (1056062463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36355193/156250000 : ℝ)^4137 ≤ (720131840483/5000000000000 : ℝ)^3113 := by
    have hnat : (36355193 : ℕ)^4137*5000000000000^3113 ≤ 720131840483^3113*156250000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36355193 156250000 720131840483 5000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640156151/5000000000 : ℝ)^4137 ≤ (42798681519733/100000000000000 : ℝ)^3113 := by
    have hnat : (2640156151 : ℕ)^4137*100000000000000^3113 ≤ 42798681519733^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640156151 5000000000 42798681519733 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056062463/2000000000 : ℝ)^4137 ≤ (42798681659763/100000000000000 : ℝ)^3113 := by
    have hnat : (1056062463 : ℕ)^4137*100000000000000^3113 ≤ 42798681659763^3113*2000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056062463 2000000000 42798681659763 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-36355193/156250000 : ℝ), (2640156151/5000000000 : ℝ), (1056062463/2000000000 : ℝ)] ![(720131840483/5000000000000 : ℝ), (42798681519733/100000000000000 : ℝ), (42798681659763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-36355193/156250000 : ℝ)|^4137 ≤ (720131840483/5000000000000 : ℝ)^3113
        have hw : |(-36355193/156250000 : ℝ)|=(36355193/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640156151/5000000000 : ℝ)|^4137 ≤ (42798681519733/100000000000000 : ℝ)^3113
        have hw : |(2640156151/5000000000 : ℝ)|=(2640156151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056062463/2000000000 : ℝ)|^4137 ≤ (42798681659763/100000000000000 : ℝ)^3113
        have hw : |(1056062463/2000000000 : ℝ)|=(1056062463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_5 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363890437/10000000000 : ℝ)*x 0 + (-2216136471/10000000000 : ℝ)*x 1 + (5280312359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363890437/10000000000 : ℝ)^4137 ≤ (43701280875591/100000000000000 : ℝ)^3113 := by
    have hnat : (5363890437 : ℕ)^4137*100000000000000^3113 ≤ 43701280875591^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363890437 10000000000 43701280875591 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216136471/10000000000 : ℝ)^4137 ≤ (13500036979187/100000000000000 : ℝ)^3113 := by
    have hnat : (2216136471 : ℕ)^4137*100000000000000^3113 ≤ 13500036979187^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216136471 10000000000 13500036979187 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280312359/10000000000 : ℝ)^4137 ≤ (4279868213371/10000000000000 : ℝ)^3113 := by
    have hnat : (5280312359 : ℕ)^4137*10000000000000^3113 ≤ 4279868213371^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280312359 10000000000 4279868213371 10000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363890437/10000000000 : ℝ), (-2216136471/10000000000 : ℝ), (5280312359/10000000000 : ℝ)] ![(43701280875591/100000000000000 : ℝ), (13500036979187/100000000000000 : ℝ), (4279868213371/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363890437/10000000000 : ℝ)|^4137 ≤ (43701280875591/100000000000000 : ℝ)^3113
        have hw : |(5363890437/10000000000 : ℝ)|=(5363890437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2216136471/10000000000 : ℝ)|^4137 ≤ (13500036979187/100000000000000 : ℝ)^3113
        have hw : |(-2216136471/10000000000 : ℝ)|=(2216136471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280312359/10000000000 : ℝ)|^4137 ≤ (4279868213371/10000000000000 : ℝ)^3113
        have hw : |(5280312359/10000000000 : ℝ)|=(5280312359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_6 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681945129/5000000000 : ℝ)*x 0 + (5280312221/10000000000 : ℝ)*x 1 + (-1108068447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681945129/5000000000 : ℝ)^4137 ≤ (21850639468751/50000000000000 : ℝ)^3113 := by
    have hnat : (2681945129 : ℕ)^4137*50000000000000^3113 ≤ 21850639468751^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681945129 5000000000 21850639468751 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280312221/10000000000 : ℝ)^4137 ≤ (1069967016181/2500000000000 : ℝ)^3113 := by
    have hnat : (5280312221 : ℕ)^4137*2500000000000^3113 ≤ 1069967016181^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280312221 10000000000 1069967016181 2500000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108068447/5000000000 : ℝ)^4137 ≤ (13500040403593/100000000000000 : ℝ)^3113 := by
    have hnat : (1108068447 : ℕ)^4137*100000000000000^3113 ≤ 13500040403593^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108068447 5000000000 13500040403593 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681945129/5000000000 : ℝ), (5280312221/10000000000 : ℝ), (-1108068447/5000000000 : ℝ)] ![(21850639468751/50000000000000 : ℝ), (1069967016181/2500000000000 : ℝ), (13500040403593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681945129/5000000000 : ℝ)|^4137 ≤ (21850639468751/50000000000000 : ℝ)^3113
        have hw : |(2681945129/5000000000 : ℝ)|=(2681945129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280312221/10000000000 : ℝ)|^4137 ≤ (1069967016181/2500000000000 : ℝ)^3113
        have hw : |(5280312221/10000000000 : ℝ)|=(5280312221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1108068447/5000000000 : ℝ)|^4137 ≤ (13500040403593/100000000000000 : ℝ)^3113
        have hw : |(-1108068447/5000000000 : ℝ)|=(1108068447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_7 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2132395711/5000000000 : ℝ)*x 0 + (4429745139/10000000000 : ℝ)*x 1 + (4429745263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132395711/5000000000 : ℝ)^4137 ≤ (6444440375887/20000000000000 : ℝ)^3113 := by
    have hnat : (2132395711 : ℕ)^4137*20000000000000^3113 ≤ 6444440375887^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132395711 5000000000 6444440375887 20000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4429745139/10000000000 : ℝ)^4137 ≤ (33888898423347/100000000000000 : ℝ)^3113 := by
    have hnat : (4429745139 : ℕ)^4137*100000000000000^3113 ≤ 33888898423347^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429745139 10000000000 33888898423347 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4429745263/10000000000 : ℝ)^4137 ≤ (33888899684033/100000000000000 : ℝ)^3113 := by
    have hnat : (4429745263 : ℕ)^4137*100000000000000^3113 ≤ 33888899684033^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429745263 10000000000 33888899684033 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2132395711/5000000000 : ℝ), (4429745139/10000000000 : ℝ), (4429745263/10000000000 : ℝ)] ![(6444440375887/20000000000000 : ℝ), (33888898423347/100000000000000 : ℝ), (33888899684033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2132395711/5000000000 : ℝ)|^4137 ≤ (6444440375887/20000000000000 : ℝ)^3113
        have hw : |(2132395711/5000000000 : ℝ)|=(2132395711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4429745139/10000000000 : ℝ)|^4137 ≤ (33888898423347/100000000000000 : ℝ)^3113
        have hw : |(4429745139/10000000000 : ℝ)|=(4429745139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4429745263/10000000000 : ℝ)|^4137 ≤ (33888899684033/100000000000000 : ℝ)^3113
        have hw : |(4429745263/10000000000 : ℝ)|=(4429745263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_8 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1136294037/5000000000 : ℝ)*x 0 + (5214563739/10000000000 : ℝ)*x 1 + (2693382767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1136294037/5000000000 : ℝ)^4137 ≤ (13958946038519/100000000000000 : ℝ)^3113 := by
    have hnat : (1136294037 : ℕ)^4137*100000000000000^3113 ≤ 13958946038519^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136294037 5000000000 13958946038519 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214563739/10000000000 : ℝ)^4137 ≤ (42091923688669/100000000000000 : ℝ)^3113 := by
    have hnat : (5214563739 : ℕ)^4137*100000000000000^3113 ≤ 42091923688669^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214563739 10000000000 42091923688669 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693382767/5000000000 : ℝ)^4137 ≤ (21974565127447/50000000000000 : ℝ)^3113 := by
    have hnat : (2693382767 : ℕ)^4137*50000000000000^3113 ≤ 21974565127447^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693382767 5000000000 21974565127447 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1136294037/5000000000 : ℝ), (5214563739/10000000000 : ℝ), (2693382767/5000000000 : ℝ)] ![(13958946038519/100000000000000 : ℝ), (42091923688669/100000000000000 : ℝ), (21974565127447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1136294037/5000000000 : ℝ)|^4137 ≤ (13958946038519/100000000000000 : ℝ)^3113
        have hw : |(-1136294037/5000000000 : ℝ)|=(1136294037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214563739/10000000000 : ℝ)|^4137 ≤ (42091923688669/100000000000000 : ℝ)^3113
        have hw : |(5214563739/10000000000 : ℝ)|=(5214563739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693382767/5000000000 : ℝ)|^4137 ≤ (21974565127447/50000000000000 : ℝ)^3113
        have hw : |(2693382767/5000000000 : ℝ)|=(2693382767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_9 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322143391/2500000000 : ℝ)*x 0 + (-1087198207/5000000000 : ℝ)*x 1 + (5386765377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322143391/2500000000 : ℝ)^4137 ≤ (42887690797437/100000000000000 : ℝ)^3113 := by
    have hnat : (1322143391 : ℕ)^4137*100000000000000^3113 ≤ 42887690797437^3113*2500000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322143391 2500000000 42887690797437 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087198207/5000000000 : ℝ)^4137 ≤ (3290795157521/25000000000000 : ℝ)^3113 := by
    have hnat : (1087198207 : ℕ)^4137*25000000000000^3113 ≤ 3290795157521^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087198207 5000000000 3290795157521 25000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386765377/10000000000 : ℝ)^4137 ≤ (351593028421/800000000000 : ℝ)^3113 := by
    have hnat : (5386765377 : ℕ)^4137*800000000000^3113 ≤ 351593028421^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386765377 10000000000 351593028421 800000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322143391/2500000000 : ℝ), (-1087198207/5000000000 : ℝ), (5386765377/10000000000 : ℝ)] ![(42887690797437/100000000000000 : ℝ), (3290795157521/25000000000000 : ℝ), (351593028421/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322143391/2500000000 : ℝ)|^4137 ≤ (42887690797437/100000000000000 : ℝ)^3113
        have hw : |(1322143391/2500000000 : ℝ)|=(1322143391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1087198207/5000000000 : ℝ)|^4137 ≤ (3290795157521/25000000000000 : ℝ)^3113
        have hw : |(-1087198207/5000000000 : ℝ)|=(1087198207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386765377/10000000000 : ℝ)|^4137 ≤ (351593028421/800000000000 : ℝ)^3113
        have hw : |(5386765377/10000000000 : ℝ)|=(5386765377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_10 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322143409/2500000000 : ℝ)*x 0 + (1077353101/2000000000 : ℝ)*x 1 + (-1087198073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322143409/2500000000 : ℝ)^4137 ≤ (8577538314677/20000000000000 : ℝ)^3113 := by
    have hnat : (1322143409 : ℕ)^4137*20000000000000^3113 ≤ 8577538314677^3113*2500000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322143409 2500000000 8577538314677 20000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077353101/2000000000 : ℝ)^4137 ≤ (21974564970231/50000000000000 : ℝ)^3113 := by
    have hnat : (1077353101 : ℕ)^4137*50000000000000^3113 ≤ 21974564970231^3113*2000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077353101 2000000000 21974564970231 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087198073/5000000000 : ℝ)^4137 ≤ (3290794618503/25000000000000 : ℝ)^3113 := by
    have hnat : (1087198073 : ℕ)^4137*25000000000000^3113 ≤ 3290794618503^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087198073 5000000000 3290794618503 25000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322143409/2500000000 : ℝ), (1077353101/2000000000 : ℝ), (-1087198073/5000000000 : ℝ)] ![(8577538314677/20000000000000 : ℝ), (21974564970231/50000000000000 : ℝ), (3290794618503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322143409/2500000000 : ℝ)|^4137 ≤ (8577538314677/20000000000000 : ℝ)^3113
        have hw : |(1322143409/2500000000 : ℝ)|=(1322143409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077353101/2000000000 : ℝ)|^4137 ≤ (21974564970231/50000000000000 : ℝ)^3113
        have hw : |(1077353101/2000000000 : ℝ)|=(1077353101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087198073/5000000000 : ℝ)|^4137 ≤ (3290794618503/25000000000000 : ℝ)^3113
        have hw : |(-1087198073/5000000000 : ℝ)|=(1087198073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_11 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2251386387/5000000000 : ℝ)*x 0 + (4310635173/10000000000 : ℝ)*x 1 + (4310635493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251386387/5000000000 : ℝ)^4137 ≤ (17316681480649/50000000000000 : ℝ)^3113 := by
    have hnat : (2251386387 : ℕ)^4137*50000000000000^3113 ≤ 17316681480649^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251386387 5000000000 17316681480649 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4310635173/10000000000 : ℝ)^4137 ≤ (4085414612247/12500000000000 : ℝ)^3113 := by
    have hnat : (4310635173 : ℕ)^4137*12500000000000^3113 ≤ 4085414612247^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310635173 10000000000 4085414612247 12500000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4310635493/10000000000 : ℝ)^4137 ≤ (32683320122319/100000000000000 : ℝ)^3113 := by
    have hnat : (4310635493 : ℕ)^4137*100000000000000^3113 ≤ 32683320122319^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310635493 10000000000 32683320122319 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2251386387/5000000000 : ℝ), (4310635173/10000000000 : ℝ), (4310635493/10000000000 : ℝ)] ![(17316681480649/50000000000000 : ℝ), (4085414612247/12500000000000 : ℝ), (32683320122319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2251386387/5000000000 : ℝ)|^4137 ≤ (17316681480649/50000000000000 : ℝ)^3113
        have hw : |(2251386387/5000000000 : ℝ)|=(2251386387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4310635173/10000000000 : ℝ)|^4137 ≤ (4085414612247/12500000000000 : ℝ)^3113
        have hw : |(4310635173/10000000000 : ℝ)|=(4310635173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4310635493/10000000000 : ℝ)|^4137 ≤ (32683320122319/100000000000000 : ℝ)^3113
        have hw : |(4310635493/10000000000 : ℝ)|=(4310635493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_12 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121962759/10000000000 : ℝ)*x 0 + (1360396861/2500000000 : ℝ)*x 1 + (5272303867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121962759/10000000000 : ℝ)^4137 ≤ (1592878951551/12500000000000 : ℝ)^3113 := by
    have hnat : (2121962759 : ℕ)^4137*12500000000000^3113 ≤ 1592878951551^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121962759 10000000000 1592878951551 12500000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360396861/2500000000 : ℝ)^4137 ≤ (5568066048117/12500000000000 : ℝ)^3113 := by
    have hnat : (1360396861 : ℕ)^4137*12500000000000^3113 ≤ 5568066048117^3113*2500000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360396861 2500000000 5568066048117 12500000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272303867/10000000000 : ℝ)^4137 ≤ (42712439989879/100000000000000 : ℝ)^3113 := by
    have hnat : (5272303867 : ℕ)^4137*100000000000000^3113 ≤ 42712439989879^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272303867 10000000000 42712439989879 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121962759/10000000000 : ℝ), (1360396861/2500000000 : ℝ), (5272303867/10000000000 : ℝ)] ![(1592878951551/12500000000000 : ℝ), (5568066048117/12500000000000 : ℝ), (42712439989879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121962759/10000000000 : ℝ)|^4137 ≤ (1592878951551/12500000000000 : ℝ)^3113
        have hw : |(-2121962759/10000000000 : ℝ)|=(2121962759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360396861/2500000000 : ℝ)|^4137 ≤ (5568066048117/12500000000000 : ℝ)^3113
        have hw : |(1360396861/2500000000 : ℝ)|=(1360396861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272303867/10000000000 : ℝ)|^4137 ≤ (42712439989879/100000000000000 : ℝ)^3113
        have hw : |(5272303867/10000000000 : ℝ)|=(5272303867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_13 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214782171/400000000 : ℝ)*x 0 + (-277401601/1250000000 : ℝ)*x 1 + (5272303599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214782171/400000000 : ℝ)^4137 ≤ (547032695833/1250000000000 : ℝ)^3113 := by
    have hnat : (214782171 : ℕ)^4137*1250000000000^3113 ≤ 547032695833^3113*400000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214782171 400000000 547032695833 1250000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277401601/1250000000 : ℝ)^4137 ≤ (13524947217287/100000000000000 : ℝ)^3113 := by
    have hnat : (277401601 : ℕ)^4137*100000000000000^3113 ≤ 13524947217287^3113*1250000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277401601 1250000000 13524947217287 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272303599/10000000000 : ℝ)^4137 ≤ (5339054638069/12500000000000 : ℝ)^3113 := by
    have hnat : (5272303599 : ℕ)^4137*12500000000000^3113 ≤ 5339054638069^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272303599 10000000000 5339054638069 12500000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214782171/400000000 : ℝ), (-277401601/1250000000 : ℝ), (5272303599/10000000000 : ℝ)] ![(547032695833/1250000000000 : ℝ), (13524947217287/100000000000000 : ℝ), (5339054638069/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214782171/400000000 : ℝ)|^4137 ≤ (547032695833/1250000000000 : ℝ)^3113
        have hw : |(214782171/400000000 : ℝ)|=(214782171/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277401601/1250000000 : ℝ)|^4137 ≤ (13524947217287/100000000000000 : ℝ)^3113
        have hw : |(-277401601/1250000000 : ℝ)|=(277401601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272303599/10000000000 : ℝ)|^4137 ≤ (5339054638069/12500000000000 : ℝ)^3113
        have hw : |(5272303599/10000000000 : ℝ)|=(5272303599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_14 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369553929/10000000000 : ℝ)*x 0 + (5272303509/10000000000 : ℝ)*x 1 + (-2219213389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369553929/10000000000 : ℝ)^4137 ≤ (43762611919089/100000000000000 : ℝ)^3113 := by
    have hnat : (5369553929 : ℕ)^4137*100000000000000^3113 ≤ 43762611919089^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369553929 10000000000 43762611919089 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272303509/10000000000 : ℝ)^4137 ≤ (21356218067799/50000000000000 : ℝ)^3113 := by
    have hnat : (5272303509 : ℕ)^4137*50000000000000^3113 ≤ 21356218067799^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272303509 10000000000 21356218067799 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2219213389/10000000000 : ℝ)^4137 ≤ (13524951922933/100000000000000 : ℝ)^3113 := by
    have hnat : (2219213389 : ℕ)^4137*100000000000000^3113 ≤ 13524951922933^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219213389 10000000000 13524951922933 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369553929/10000000000 : ℝ), (5272303509/10000000000 : ℝ), (-2219213389/10000000000 : ℝ)] ![(43762611919089/100000000000000 : ℝ), (21356218067799/50000000000000 : ℝ), (13524951922933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369553929/10000000000 : ℝ)|^4137 ≤ (43762611919089/100000000000000 : ℝ)^3113
        have hw : |(5369553929/10000000000 : ℝ)|=(5369553929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272303509/10000000000 : ℝ)|^4137 ≤ (21356218067799/50000000000000 : ℝ)^3113
        have hw : |(5272303509/10000000000 : ℝ)|=(5272303509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2219213389/10000000000 : ℝ)|^4137 ≤ (13524951922933/100000000000000 : ℝ)^3113
        have hw : |(-2219213389/10000000000 : ℝ)|=(2219213389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_box_15 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4246635889/10000000000 : ℝ)*x 0 + (2219350441/5000000000 : ℝ)*x 1 + (2219350653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4246635889/10000000000 : ℝ)^4137 ≤ (32040035450009/100000000000000 : ℝ)^3113 := by
    have hnat : (4246635889 : ℕ)^4137*100000000000000^3113 ≤ 32040035450009^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246635889 10000000000 32040035450009 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219350441/5000000000 : ℝ)^4137 ≤ (33979980108129/100000000000000 : ℝ)^3113 := by
    have hnat : (2219350441 : ℕ)^4137*100000000000000^3113 ≤ 33979980108129^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219350441 5000000000 33979980108129 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2219350653/5000000000 : ℝ)^4137 ≤ (1359199376869/4000000000000 : ℝ)^3113 := by
    have hnat : (2219350653 : ℕ)^4137*4000000000000^3113 ≤ 1359199376869^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219350653 5000000000 1359199376869 4000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4246635889/10000000000 : ℝ), (2219350441/5000000000 : ℝ), (2219350653/5000000000 : ℝ)] ![(32040035450009/100000000000000 : ℝ), (33979980108129/100000000000000 : ℝ), (1359199376869/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4246635889/10000000000 : ℝ)|^4137 ≤ (32040035450009/100000000000000 : ℝ)^3113
        have hw : |(4246635889/10000000000 : ℝ)|=(4246635889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2219350441/5000000000 : ℝ)|^4137 ≤ (33979980108129/100000000000000 : ℝ)^3113
        have hw : |(2219350441/5000000000 : ℝ)|=(2219350441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2219350653/5000000000 : ℝ)|^4137 ≤ (1359199376869/4000000000000 : ℝ)^3113
        have hw : |(2219350653/5000000000 : ℝ)|=(2219350653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1081_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14813/25000 : ℝ) ∧ (79619/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82987/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11273/100000 : ℝ) ^ (8273/2048 : ℝ) ≤ (14813764966840509/100000000000000000000 : ℝ) := by
    have hpowers : (11273/100000 : ℝ)^8273 ≤ (14813764966840509/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11273 : ℕ)^8273*100000000000000000000^2048 ≤ 14813764966840509^2048*100000^8273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11273 100000 14813764966840509 100000000000000000000 8273 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11273/100000 : ℝ)) (X := (14813764966840509/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3503/25000 : ℝ) ^ (8273/2048 : ℝ) ≤ (17832569783750107/50000000000000000000 : ℝ) := by
    have hpowers : (3503/25000 : ℝ)^8273 ≤ (17832569783750107/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3503 : ℕ)^8273*50000000000000000000^2048 ≤ 17832569783750107^2048*25000^8273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3503 25000 17832569783750107 50000000000000000000 8273 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3503/25000 : ℝ)) (X := (17832569783750107/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014813764966840509/50000000000000000000 : ℝ) ≤ (10000733354515191/10000000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (50014813764966840509/50000000000000000000 : ℝ)^2048 ≤ (10000733354515191/10000000000000000 : ℝ)^8273 := by
      have hnat : (50014813764966840509 : ℕ)^2048*10000000000000000^8273 ≤ 10000733354515191^8273*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014813764966840509 50000000000000000000 10000733354515191 10000000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000733354515191/10000000000000000 : ℝ)) (X := (50014813764966840509/50000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050478904534340723/100000000000000000000 : ℝ) ≤ (1250156172441747/1250000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (100050478904534340723/100000000000000000000 : ℝ)^2048 ≤ (1250156172441747/1250000000000000 : ℝ)^8273 := by
      have hnat : (100050478904534340723 : ℕ)^2048*1250000000000000^8273 ≤ 1250156172441747^8273*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050478904534340723 100000000000000000000 1250156172441747 1250000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250156172441747/1250000000000000 : ℝ)) (X := (100050478904534340723/100000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017832569783750107/25000000000000000000 : ℝ) ≤ (10001765404552761/10000000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (25017832569783750107/25000000000000000000 : ℝ)^2048 ≤ (10001765404552761/10000000000000000 : ℝ)^8273 := by
      have hnat : (25017832569783750107 : ℕ)^2048*10000000000000000^8273 ≤ 10001765404552761^8273*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017832569783750107 25000000000000000000 10001765404552761 10000000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001765404552761/10000000000000000 : ℝ)) (X := (25017832569783750107/25000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14813764966840509/100000000000000000000 : ℝ) ≤ ((9126791452647860513/9130000000000000000 : ℝ)+2*(34401667919/18260000000000 : ℝ)*(11273/100000 : ℝ))^(8273/2048 : ℝ) := by
    rw [show (9126791452647860513/9130000000000000000 : ℝ)+2*(34401667919/18260000000000 : ℝ)*(11273/100000 : ℝ)=(10000733354515191/10000000000000000 : ℝ) by norm_num, show 1+2*(14813764966840509/100000000000000000000 : ℝ)=(50014813764966840509/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17832569783750107/50000000000000000000 : ℝ)+(14813764966840509/100000000000000000000 : ℝ) ≤ ((9126791452647860513/9130000000000000000 : ℝ)+(34401667919/18260000000000 : ℝ)*((3503/25000 : ℝ)+(11273/100000 : ℝ)))^(8273/2048 : ℝ) := by
    rw [show (9126791452647860513/9130000000000000000 : ℝ)+(34401667919/18260000000000 : ℝ)*((3503/25000 : ℝ)+(11273/100000 : ℝ))=(1250156172441747/1250000000000000 : ℝ) by norm_num, show 1+(17832569783750107/50000000000000000000 : ℝ)+(14813764966840509/100000000000000000000 : ℝ)=(100050478904534340723/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17832569783750107/50000000000000000000 : ℝ) ≤ ((9126791452647860513/9130000000000000000 : ℝ)+2*(34401667919/18260000000000 : ℝ)*(3503/25000 : ℝ))^(8273/2048 : ℝ) := by
    rw [show (9126791452647860513/9130000000000000000 : ℝ)+2*(34401667919/18260000000000 : ℝ)*(3503/25000 : ℝ)=(10001765404552761/10000000000000000 : ℝ) by norm_num, show 1+2*(17832569783750107/50000000000000000000 : ℝ)=(25017832569783750107/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9126791452647860513/9130000000000000000 : ℝ)*(X 1 0+X 2 0)+(34401667919/18260000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (9126791452647860513/9130000000000000000 : ℝ)) (alpha := (34401667919/18260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9126791452647860513/9130000000000000000 : ℝ)*(X 0 1+X 2 1)+(34401667919/18260000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (9126791452647860513/9130000000000000000 : ℝ)) (alpha := (34401667919/18260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9126791452647860513/9130000000000000000 : ℝ)*(X 0 2+X 1 2)+(34401667919/18260000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (9126791452647860513/9130000000000000000 : ℝ)) (alpha := (34401667919/18260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-25843251/125000000 : ℝ)*X 0 0+(53771631/100000000 : ℝ)*X 0 1+(2688581409/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647685483/5000000000 : ℝ)*X 1 0+(-2178225339/10000000000 : ℝ)*X 1 1+(2688581441/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1059074141/2000000000 : ℝ)*X 2 0+(168036343/312500000 : ℝ)*X 2 1+(-1089112781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2240777307/5000000000 : ℝ)*X 0 0+(135043289/312500000 : ℝ)*X 0 1+(270086539/625000000 : ℝ)*X 0 2+(2240777307/5000000000 : ℝ)*X 1 0+(135043289/312500000 : ℝ)*X 1 1+(270086539/625000000 : ℝ)*X 1 2+(2240777307/5000000000 : ℝ)*X 2 0+(135043289/312500000 : ℝ)*X 2 1+(270086539/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-36355193/156250000 : ℝ)*X 0 0+(2640156151/5000000000 : ℝ)*X 0 1+(1056062463/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363890437/10000000000 : ℝ)*X 1 0+(-2216136471/10000000000 : ℝ)*X 1 1+(5280312359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681945129/5000000000 : ℝ)*X 2 0+(5280312221/10000000000 : ℝ)*X 2 1+(-1108068447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2132395711/5000000000 : ℝ)*X 0 0+(4429745139/10000000000 : ℝ)*X 0 1+(4429745263/10000000000 : ℝ)*X 0 2+(2132395711/5000000000 : ℝ)*X 1 0+(4429745139/10000000000 : ℝ)*X 1 1+(4429745263/10000000000 : ℝ)*X 1 2+(2132395711/5000000000 : ℝ)*X 2 0+(4429745139/10000000000 : ℝ)*X 2 1+(4429745263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1136294037/5000000000 : ℝ)*X 0 0+(5214563739/10000000000 : ℝ)*X 0 1+(2693382767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322143391/2500000000 : ℝ)*X 1 0+(-1087198207/5000000000 : ℝ)*X 1 1+(5386765377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322143409/2500000000 : ℝ)*X 2 0+(1077353101/2000000000 : ℝ)*X 2 1+(-1087198073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2251386387/5000000000 : ℝ)*X 0 0+(4310635173/10000000000 : ℝ)*X 0 1+(4310635493/10000000000 : ℝ)*X 0 2+(2251386387/5000000000 : ℝ)*X 1 0+(4310635173/10000000000 : ℝ)*X 1 1+(4310635493/10000000000 : ℝ)*X 1 2+(2251386387/5000000000 : ℝ)*X 2 0+(4310635173/10000000000 : ℝ)*X 2 1+(4310635493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2121962759/10000000000 : ℝ)*X 0 0+(1360396861/2500000000 : ℝ)*X 0 1+(5272303867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((214782171/400000000 : ℝ)*X 1 0+(-277401601/1250000000 : ℝ)*X 1 1+(5272303599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369553929/10000000000 : ℝ)*X 2 0+(5272303509/10000000000 : ℝ)*X 2 1+(-2219213389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4246635889/10000000000 : ℝ)*X 0 0+(2219350441/5000000000 : ℝ)*X 0 1+(2219350653/5000000000 : ℝ)*X 0 2+(4246635889/10000000000 : ℝ)*X 1 0+(2219350441/5000000000 : ℝ)*X 1 1+(2219350653/5000000000 : ℝ)*X 1 2+(4246635889/10000000000 : ℝ)*X 2 0+(2219350441/5000000000 : ℝ)*X 2 1+(2219350653/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-142023796370065587364394790516963/228250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14351157/10000000000000 : ℝ)*(upper1) + (18597387/100000000000000 : ℝ)*(upper2) + (132502361/50000000000000 : ℝ)*(lower4) + (31369867/50000000000000 : ℝ)*(upper5) + (3869334825957217/100000000000000 : ℝ)*(major0) + (3869334825957217/100000000000000 : ℝ)*(major1) + (3869334825957217/100000000000000 : ℝ)*(major2) + (5392569531/50000000000000 : ℝ)*(sp2) + (1693364089/25000000000000 : ℝ)*(sp3) + (321876172186273/6250000000000 : ℝ)*(sp4) + (5149811267613507/100000000000000 : ℝ)*(sp5) + (2575003984920653/50000000000000 : ℝ)*(sp6) + (652346273526237/25000000000000 : ℝ)*(sp7) + (103743683431/50000000000000 : ℝ)*(sp13) + (326173983445163/12500000000000 : ℝ)*(f.failure) + (321876172186273/6250000000000 : ℝ)*(f.sum) + (1361762494529/913000000000000000000000000 : ℝ)*base66 + (2911629701085172321/913000000000000000000000000000000 : ℝ)*base67 + (7165121229789172321/913000000000000000000000000000000 : ℝ)*base69 + (6606193574303827679/913000000000000000000000000000000 : ℝ)*base72 + (194764601019/114125000000000000000000000 : ℝ)*base73 + (1440850955286172321/913000000000000000000000000000000 : ℝ)*base75 + (5289641276959172321/913000000000000000000000000000000 : ℝ)*base77 + (1285319233259172321/913000000000000000000000000000000 : ℝ)*base79 + (3232835438357/913000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8541899/1250000000000000000000 : ℝ)*base90 + (8541899/1250000000000000000000 : ℝ)*base92 + (8541899/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14813/25000 : ℝ) ≤ (67624177684679033966693032426509/114125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1793539/3125000000000 : ℝ)*(lower0) + (54456971/100000000000000 : ℝ)*(upper2) + (253457/160000000000 : ℝ)*(upper3) + (111164287/100000000000000 : ℝ)*(lower5) + (1966246771919231/50000000000000 : ℝ)*(major0) + (1966246771919231/50000000000000 : ℝ)*(major1) + (1966246771919231/50000000000000 : ℝ)*(major2) + (519325091563697/10000000000000 : ℝ)*(sp0) + (649140070015051/12500000000000 : ℝ)*(sp1) + (1298309962640761/25000000000000 : ℝ)*(sp2) + (1325992003340331/50000000000000 : ℝ)*(sp3) + (335664719/50000000000000 : ℝ)*(sp7) + (65177758281/50000000000000 : ℝ)*(sp9) + (5532536963/50000000000000 : ℝ)*(sp10) + (26519846780101/1000000000000 : ℝ)*(f.failure) + (519325091563697/10000000000000 : ℝ)*(f.sum) + (3733519898413/456500000000000000000000000 : ℝ)*base65 + (3597014341842274497/456500000000000000000000000000000 : ℝ)*base68 + (4106829745588274497/456500000000000000000000000000000 : ℝ)*base70 + (2920396132465274497/456500000000000000000000000000000 : ℝ)*base72 + (3805880551909/228250000000000000000000000 : ℝ)*base74 + (6211198090843274497/456500000000000000000000000000000 : ℝ)*base76 + (2483616868555274497/456500000000000000000000000000000 : ℝ)*base78 + (10224630365126725503/456500000000000000000000000000000 : ℝ)*base79 + (101457068819/228250000000000000000000000 : ℝ)*base82 + (162373/100000000000000000000 : ℝ)*base90 + (162373/100000000000000000000 : ℝ)*base92 + (162373/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79619/100000 : ℝ) ≤ (181736902618878095389352997694839/228250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97054399/100000000000000 : ℝ)*(upper0) + (55772019/50000000000000 : ℝ)*(lower3) + (116345327/100000000000000 : ℝ)*(upper4) + (2200357219924701/50000000000000 : ℝ)*(major0) + (2200357219924701/50000000000000 : ℝ)*(major1) + (2200357219924701/50000000000000 : ℝ)*(major2) + (27045501537/50000000000000 : ℝ)*(sp1) + (81874778903/50000000000000 : ℝ)*(sp2) + (3541473631/6250000000000 : ℝ)*(sp3) + (118621171/4000000000000 : ℝ)*(sp4) + (5807143035779463/100000000000000 : ℝ)*(sp8) + (45367905549263/781250000000 : ℝ)*(sp9) + (1451745562937733/25000000000000 : ℝ)*(sp10) + (2967685593765027/100000000000000 : ℝ)*(sp11) + (2967742257343123/100000000000000 : ℝ)*(f.failure) + (5807146001308737/100000000000000 : ℝ)*(f.sum) + (3211522258851/456500000000000000000000000 : ℝ)*base66 + (2287022035561731613/456500000000000000000000000000000 : ℝ)*base67 + (3653375200287731613/456500000000000000000000000000000 : ℝ)*base69 + (5673867831522268387/456500000000000000000000000000000 : ℝ)*base72 + (9170027047677/913000000000000000000000000 : ℝ)*base73 + (269760568500768387/456500000000000000000000000000000 : ℝ)*base76 + (2361451791435268387/456500000000000000000000000000000 : ℝ)*base78 + (10065803191196768387/456500000000000000000000000000000 : ℝ)*base80 + (451228075263/182600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8007021/10000000000000000000000 : ℝ)*base89 + (8007021/10000000000000000000000 : ℝ)*base91 + (8007021/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-82987/100000 : ℝ) ≤ (-189411393341151615959295058034721/228250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8904857/25000000000000 : ℝ)*(lower0) + (57262141/100000000000000 : ℝ)*(upper1) + (431774511/100000000000000 : ℝ)*(lower4) + (2217674276970887/50000000000000 : ℝ)*(major0) + (2217674276970887/50000000000000 : ℝ)*(major1) + (2217674276970887/50000000000000 : ℝ)*(major2) + (1838158101/100000000000000 : ℝ)*(sp4) + (25603089517/20000000000000 : ℝ)*(sp5) + (105899229767/20000000000000 : ℝ)*(sp6) + (323974755601/100000000000000 : ℝ)*(sp7) + (2953628971545441/50000000000000 : ℝ)*(sp12) + (5907131765801397/100000000000000 : ℝ)*(sp13) + (5906730285100147/100000000000000 : ℝ)*(sp14) + (1495387372788043/50000000000000 : ℝ)*(sp15) + (1495549360165843/50000000000000 : ℝ)*(f.failure) + (2953629890624491/50000000000000 : ℝ)*(f.sum) + (758926746053/228250000000000000000000000 : ℝ)*base66 + (8892511617192114969/456500000000000000000000000000000 : ℝ)*base68 + (12635476266357614969/456500000000000000000000000000000 : ℝ)*base70 + (7372524746509614969/456500000000000000000000000000000 : ℝ)*base72 + (6781290033633/456500000000000000000000000 : ℝ)*base73 + (6146865751416114969/456500000000000000000000000000000 : ℝ)*base76 + (7161763340484114969/456500000000000000000000000000000 : ℝ)*base78 + (16907092326404114969/456500000000000000000000000000000 : ℝ)*base80 + (418401866659/114125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (37148461/5000000000000000000000 : ℝ)*base89 + (37148461/5000000000000000000000 : ℝ)*base91 + (37148461/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1081_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(14813/25000 : ℝ) else (79619/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82987/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1081_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1081_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(14813/25000 : ℝ) else (79619/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82987/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1081_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1081_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(14813/25000 : ℝ) else (79619/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82987/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1081_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
