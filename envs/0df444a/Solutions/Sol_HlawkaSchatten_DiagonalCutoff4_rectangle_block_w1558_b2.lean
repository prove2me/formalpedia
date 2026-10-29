-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1558_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:23:56.744492+00:00
-- url     : https://prove2.me/submissions/b3752b7d-cb91-489b-91af-3b8832e0b7e0

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
theorem support_rectangle_w1558_s6_0 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-901070877/5000000000 : ℝ)*x 0 + (2713655037/5000000000 : ℝ)*x 1 + (1304910299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901070877/5000000000 : ℝ)^4613 ≤ (1381539988803/12500000000000 : ℝ)^3589 := by
    have hnat : (901070877 : ℕ)^4613*12500000000000^3589 ≤ 1381539988803^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901070877 5000000000 1381539988803 12500000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713655037/5000000000 : ℝ)^4613 ≤ (45588711668081/100000000000000 : ℝ)^3589 := by
    have hnat : (2713655037 : ℕ)^4613*100000000000000^3589 ≤ 45588711668081^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713655037 5000000000 45588711668081 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304910299/2500000000 : ℝ)^4613 ≤ (21679484203481/50000000000000 : ℝ)^3589 := by
    have hnat : (1304910299 : ℕ)^4613*50000000000000^3589 ≤ 21679484203481^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304910299 2500000000 21679484203481 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-901070877/5000000000 : ℝ), (2713655037/5000000000 : ℝ), (1304910299/2500000000 : ℝ)] ![(1381539988803/12500000000000 : ℝ), (45588711668081/100000000000000 : ℝ), (21679484203481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-901070877/5000000000 : ℝ)|^4613 ≤ (1381539988803/12500000000000 : ℝ)^3589
        have hw : |(-901070877/5000000000 : ℝ)|=(901070877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713655037/5000000000 : ℝ)|^4613 ≤ (45588711668081/100000000000000 : ℝ)^3589
        have hw : |(2713655037/5000000000 : ℝ)|=(2713655037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304910299/2500000000 : ℝ)|^4613 ≤ (21679484203481/50000000000000 : ℝ)^3589
        have hw : |(1304910299/2500000000 : ℝ)|=(1304910299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s6_1 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42791357/80000000 : ℝ)*x 0 + (-238550659/1250000000 : ℝ)*x 1 + (1304910297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42791357/80000000 : ℝ)^4613 ≤ (44744119720839/100000000000000 : ℝ)^3589 := by
    have hnat : (42791357 : ℕ)^4613*100000000000000^3589 ≤ 44744119720839^3589*80000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42791357 80000000 44744119720839 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238550659/1250000000 : ℝ)^4613 ≤ (11896911944499/100000000000000 : ℝ)^3589 := by
    have hnat : (238550659 : ℕ)^4613*100000000000000^3589 ≤ 11896911944499^3589*1250000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238550659 1250000000 11896911944499 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304910297/2500000000 : ℝ)^4613 ≤ (21679484160773/50000000000000 : ℝ)^3589 := by
    have hnat : (1304910297 : ℕ)^4613*50000000000000^3589 ≤ 21679484160773^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304910297 2500000000 21679484160773 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42791357/80000000 : ℝ), (-238550659/1250000000 : ℝ), (1304910297/2500000000 : ℝ)] ![(44744119720839/100000000000000 : ℝ), (11896911944499/100000000000000 : ℝ), (21679484160773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42791357/80000000 : ℝ)|^4613 ≤ (44744119720839/100000000000000 : ℝ)^3589
        have hw : |(42791357/80000000 : ℝ)|=(42791357/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-238550659/1250000000 : ℝ)|^4613 ≤ (11896911944499/100000000000000 : ℝ)^3589
        have hw : |(-238550659/1250000000 : ℝ)|=(238550659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304910297/2500000000 : ℝ)|^4613 ≤ (21679484160773/50000000000000 : ℝ)^3589
        have hw : |(1304910297/2500000000 : ℝ)|=(1304910297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s6_2 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348919643/10000000000 : ℝ)*x 0 + (2609820587/5000000000 : ℝ)*x 1 + (-954202633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348919643/10000000000 : ℝ)^4613 ≤ (44744119914371/100000000000000 : ℝ)^3589 := by
    have hnat : (5348919643 : ℕ)^4613*100000000000000^3589 ≤ 44744119914371^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348919643 10000000000 44744119914371 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609820587/5000000000 : ℝ)^4613 ≤ (10839742043017/25000000000000 : ℝ)^3589 := by
    have hnat : (2609820587 : ℕ)^4613*25000000000000^3589 ≤ 10839742043017^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609820587 5000000000 10839742043017 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (954202633/5000000000 : ℝ)^4613 ≤ (1487113987053/12500000000000 : ℝ)^3589 := by
    have hnat : (954202633 : ℕ)^4613*12500000000000^3589 ≤ 1487113987053^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954202633 5000000000 1487113987053 12500000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348919643/10000000000 : ℝ), (2609820587/5000000000 : ℝ), (-954202633/5000000000 : ℝ)] ![(44744119914371/100000000000000 : ℝ), (10839742043017/25000000000000 : ℝ), (1487113987053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348919643/10000000000 : ℝ)|^4613 ≤ (44744119914371/100000000000000 : ℝ)^3589
        have hw : |(5348919643/10000000000 : ℝ)|=(5348919643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609820587/5000000000 : ℝ)|^4613 ≤ (10839742043017/25000000000000 : ℝ)^3589
        have hw : |(2609820587/5000000000 : ℝ)|=(2609820587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-954202633/5000000000 : ℝ)|^4613 ≤ (1487113987053/12500000000000 : ℝ)^3589
        have hw : |(-954202633/5000000000 : ℝ)|=(954202633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s6_3 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531102613/1250000000 : ℝ)*x 0 + (2005701383/5000000000 : ℝ)*x 1 + (4497613201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531102613/1250000000 : ℝ)^4613 ≤ (33281843061323/100000000000000 : ℝ)^3589 := by
    have hnat : (531102613 : ℕ)^4613*100000000000000^3589 ≤ 33281843061323^3589*1250000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531102613 1250000000 33281843061323 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005701383/5000000000 : ℝ)^4613 ≤ (3091080043529/10000000000000 : ℝ)^3589 := by
    have hnat : (2005701383 : ℕ)^4613*10000000000000^3589 ≤ 3091080043529^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005701383 5000000000 3091080043529 10000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497613201/10000000000 : ℝ)^4613 ≤ (17903678242559/50000000000000 : ℝ)^3589 := by
    have hnat : (4497613201 : ℕ)^4613*50000000000000^3589 ≤ 17903678242559^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497613201 10000000000 17903678242559 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531102613/1250000000 : ℝ), (2005701383/5000000000 : ℝ), (4497613201/10000000000 : ℝ)] ![(33281843061323/100000000000000 : ℝ), (3091080043529/10000000000000 : ℝ), (17903678242559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531102613/1250000000 : ℝ)|^4613 ≤ (33281843061323/100000000000000 : ℝ)^3589
        have hw : |(531102613/1250000000 : ℝ)|=(531102613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2005701383/5000000000 : ℝ)|^4613 ≤ (3091080043529/10000000000000 : ℝ)^3589
        have hw : |(2005701383/5000000000 : ℝ)|=(2005701383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497613201/10000000000 : ℝ)|^4613 ≤ (17903678242559/50000000000000 : ℝ)^3589
        have hw : |(4497613201/10000000000 : ℝ)|=(4497613201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s6_4 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-901084481/5000000000 : ℝ)*x 0 + (652590017/1250000000 : ℝ)*x 1 + (108524463/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901084481/5000000000 : ℝ)^4613 ≤ (5526267191569/50000000000000 : ℝ)^3589 := by
    have hnat : (901084481 : ℕ)^4613*50000000000000^3589 ≤ 5526267191569^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901084481 5000000000 5526267191569 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652590017/1250000000 : ℝ)^4613 ≤ (43370488563679/100000000000000 : ℝ)^3589 := by
    have hnat : (652590017 : ℕ)^4613*100000000000000^3589 ≤ 43370488563679^3589*1250000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652590017 1250000000 43370488563679 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108524463/200000000 : ℝ)^4613 ≤ (45576977036723/100000000000000 : ℝ)^3589 := by
    have hnat : (108524463 : ℕ)^4613*100000000000000^3589 ≤ 45576977036723^3589*200000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108524463 200000000 45576977036723 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-901084481/5000000000 : ℝ), (652590017/1250000000 : ℝ), (108524463/200000000 : ℝ)] ![(5526267191569/50000000000000 : ℝ), (43370488563679/100000000000000 : ℝ), (45576977036723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-901084481/5000000000 : ℝ)|^4613 ≤ (5526267191569/50000000000000 : ℝ)^3589
        have hw : |(-901084481/5000000000 : ℝ)|=(901084481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652590017/1250000000 : ℝ)|^4613 ≤ (43370488563679/100000000000000 : ℝ)^3589
        have hw : |(652590017/1250000000 : ℝ)|=(652590017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108524463/200000000 : ℝ)|^4613 ≤ (45576977036723/100000000000000 : ℝ)^3589
        have hw : |(108524463/200000000 : ℝ)|=(108524463/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_s6_5 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (424888457/1000000000 : ℝ)*x 0 + (899017413/2000000000 : ℝ)*x 1 + (2006973781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424888457/1000000000 : ℝ)^4613 ≤ (33282484060443/100000000000000 : ℝ)^3589 := by
    have hnat : (424888457 : ℕ)^4613*100000000000000^3589 ≤ 33282484060443^3589*1000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424888457 1000000000 33282484060443 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899017413/2000000000 : ℝ)^4613 ≤ (35781508774837/100000000000000 : ℝ)^3589 := by
    have hnat : (899017413 : ℕ)^4613*100000000000000^3589 ≤ 35781508774837^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899017413 2000000000 35781508774837 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006973781/5000000000 : ℝ)^4613 ≤ (30936007150097/100000000000000 : ℝ)^3589 := by
    have hnat : (2006973781 : ℕ)^4613*100000000000000^3589 ≤ 30936007150097^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006973781 5000000000 30936007150097 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(424888457/1000000000 : ℝ), (899017413/2000000000 : ℝ), (2006973781/5000000000 : ℝ)] ![(33282484060443/100000000000000 : ℝ), (35781508774837/100000000000000 : ℝ), (30936007150097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(424888457/1000000000 : ℝ)|^4613 ≤ (33282484060443/100000000000000 : ℝ)^3589
        have hw : |(424888457/1000000000 : ℝ)|=(424888457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899017413/2000000000 : ℝ)|^4613 ≤ (35781508774837/100000000000000 : ℝ)^3589
        have hw : |(899017413/2000000000 : ℝ)|=(899017413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2006973781/5000000000 : ℝ)|^4613 ≤ (30936007150097/100000000000000 : ℝ)^3589
        have hw : |(2006973781/5000000000 : ℝ)|=(2006973781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1558_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5541/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11081/100000 : ℝ) ^ (4611/1024 : ℝ) ≤ (498661928024393/10000000000000000000 : ℝ) := by
    have hpowers : (11081/100000 : ℝ)^4611 ≤ (498661928024393/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11081 : ℕ)^4611*10000000000000000000^1024 ≤ 498661928024393^1024*100000^4611 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11081 100000 498661928024393 10000000000000000000 4611 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11081/100000 : ℝ)) (X := (498661928024393/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4611/1024 : ℝ) ≤ (22502311721517179/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4611 ≤ (22502311721517179/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4611*100000000000000000000^1024 ≤ 22502311721517179^1024*20000^4611 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 22502311721517179 100000000000000000000 4611 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (22502311721517179/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000498661928024393/5000000000000000000 : ℝ) ≤ (2500055368684353/2500000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (5000498661928024393/5000000000000000000 : ℝ)^1024 ≤ (2500055368684353/2500000000000000 : ℝ)^4611 := by
      have hnat : (5000498661928024393 : ℕ)^1024*2500000000000000^4611 ≤ 2500055368684353^4611*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000498661928024393 5000000000000000000 2500055368684353 2500000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500055368684353/2500000000000000 : ℝ)) (X := (5000498661928024393/5000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027488931001761109/100000000000000000000 : ℝ) ≤ (10000610402432119/10000000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (100027488931001761109/100000000000000000000 : ℝ)^1024 ≤ (10000610402432119/10000000000000000 : ℝ)^4611 := by
      have hnat : (100027488931001761109 : ℕ)^1024*10000000000000000^4611 ≤ 10000610402432119^4611*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027488931001761109 100000000000000000000 10000610402432119 10000000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000610402432119/10000000000000000 : ℝ)) (X := (100027488931001761109/100000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022502311721517179/50000000000000000000 : ℝ) ≤ (5000499665063413/5000000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (50022502311721517179/50000000000000000000 : ℝ)^1024 ≤ (5000499665063413/5000000000000000 : ℝ)^4611 := by
      have hnat : (50022502311721517179 : ℕ)^1024*5000000000000000^4611 ≤ 5000499665063413^4611*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022502311721517179 50000000000000000000 5000499665063413 5000000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000499665063413/5000000000000000 : ℝ)) (X := (50022502311721517179/50000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(498661928024393/10000000000000000000 : ℝ) ≤ ((22016177979586732957/22020000000000000000 : ℝ)+2*(388927694707/440400000000000 : ℝ)*(11081/100000 : ℝ))^(4611/1024 : ℝ) := by
    rw [show (22016177979586732957/22020000000000000000 : ℝ)+2*(388927694707/440400000000000 : ℝ)*(11081/100000 : ℝ)=(2500055368684353/2500000000000000 : ℝ) by norm_num, show 1+2*(498661928024393/10000000000000000000 : ℝ)=(5000498661928024393/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22502311721517179/100000000000000000000 : ℝ)+(498661928024393/10000000000000000000 : ℝ) ≤ ((22016177979586732957/22020000000000000000 : ℝ)+(388927694707/440400000000000 : ℝ)*((3097/20000 : ℝ)+(11081/100000 : ℝ)))^(4611/1024 : ℝ) := by
    rw [show (22016177979586732957/22020000000000000000 : ℝ)+(388927694707/440400000000000 : ℝ)*((3097/20000 : ℝ)+(11081/100000 : ℝ))=(10000610402432119/10000000000000000 : ℝ) by norm_num, show 1+(22502311721517179/100000000000000000000 : ℝ)+(498661928024393/10000000000000000000 : ℝ)=(100027488931001761109/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22502311721517179/100000000000000000000 : ℝ) ≤ ((22016177979586732957/22020000000000000000 : ℝ)+2*(388927694707/440400000000000 : ℝ)*(3097/20000 : ℝ))^(4611/1024 : ℝ) := by
    rw [show (22016177979586732957/22020000000000000000 : ℝ)+2*(388927694707/440400000000000 : ℝ)*(3097/20000 : ℝ)=(5000499665063413/5000000000000000 : ℝ) by norm_num, show 1+2*(22502311721517179/100000000000000000000 : ℝ)=(50022502311721517179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22016177979586732957/22020000000000000000 : ℝ)*(X 1 0+X 2 0)+(388927694707/440400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (11081/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22016177979586732957/22020000000000000000 : ℝ)) (alpha := (388927694707/440400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22016177979586732957/22020000000000000000 : ℝ)*(X 0 1+X 2 1)+(388927694707/440400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (11081/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22016177979586732957/22020000000000000000 : ℝ)) (alpha := (388927694707/440400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22016177979586732957/22020000000000000000 : ℝ)*(X 0 2+X 1 2)+(388927694707/440400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (11081/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22016177979586732957/22020000000000000000 : ℝ)) (alpha := (388927694707/440400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-901070877/5000000000 : ℝ)*X 0 0+(2713655037/5000000000 : ℝ)*X 0 1+(1304910299/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42791357/80000000 : ℝ)*X 1 0+(-238550659/1250000000 : ℝ)*X 1 1+(1304910297/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348919643/10000000000 : ℝ)*X 2 0+(2609820587/5000000000 : ℝ)*X 2 1+(-954202633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((531102613/1250000000 : ℝ)*X 0 0+(2005701383/5000000000 : ℝ)*X 0 1+(4497613201/10000000000 : ℝ)*X 0 2+(531102613/1250000000 : ℝ)*X 1 0+(2005701383/5000000000 : ℝ)*X 1 1+(4497613201/10000000000 : ℝ)*X 1 2+(531102613/1250000000 : ℝ)*X 2 0+(2005701383/5000000000 : ℝ)*X 2 1+(4497613201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-901084481/5000000000 : ℝ)*X 0 0+(652590017/1250000000 : ℝ)*X 0 1+(108524463/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((424888457/1000000000 : ℝ)*X 0 0+(899017413/2000000000 : ℝ)*X 0 1+(2006973781/5000000000 : ℝ)*X 0 2+(424888457/1000000000 : ℝ)*X 1 0+(899017413/2000000000 : ℝ)*X 1 1+(2006973781/5000000000 : ℝ)*X 1 2+(424888457/1000000000 : ℝ)*X 2 0+(899017413/2000000000 : ℝ)*X 2 1+(2006973781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2027365906496489027234757699/367000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (458749943/50000000000000 : ℝ)*(base19) + (428729301/50000000000000 : ℝ)*(base23) + (637239/1562500000000 : ℝ)*(lower2) + (133008769/100000000000000 : ℝ)*(upper3) + (43139709/50000000000000 : ℝ)*(upper5) + (3436061671911007/100000000000000 : ℝ)*(major0) + (3436061671911007/100000000000000 : ℝ)*(major1) + (3436061671911007/100000000000000 : ℝ)*(major2) + (601921628856151/12500000000000 : ℝ)*(sp0) + (963077343900701/20000000000000 : ℝ)*(sp1) + (4815386779544789/100000000000000 : ℝ)*(sp2) + (411345728660601/20000000000000 : ℝ)*(sp3) + (1825769273/12500000000000 : ℝ)*(sp4) + (3439688511/50000000000000 : ℝ)*(sp5) + (2056735522680027/100000000000000 : ℝ)*(f.failure) + (4815387637003391/100000000000000 : ℝ)*(f.sum) + (31683863884451/22020000000000000000000000000 : ℝ)*base66 + (1789959105474469233/734000000000000000000000000000000 : ℝ)*base67 + (2362439685299530767/734000000000000000000000000000000 : ℝ)*base70 + (3168594598868469233/734000000000000000000000000000000 : ℝ)*base71 + (20377797938051/22020000000000000000000000000 : ℝ)*base74 + (143874459147530767/734000000000000000000000000000000 : ℝ)*base76 + (9335252399530767/734000000000000000000000000000000 : ℝ)*base78 + (1409379447105530767/734000000000000000000000000000000 : ℝ)*base80 + (27802426559951/22020000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (4050257/625000000000000000000 : ℝ)*base89 + (4050257/625000000000000000000 : ℝ)*base91 + (4050257/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1558_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5541/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1558_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1558_box_0 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1596388211/10000000000 : ℝ)*x 0 + (2698939351/5000000000 : ℝ)*x 1 + (2698939101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1596388211/10000000000 : ℝ)^4613 ≤ (4728800469521/50000000000000 : ℝ)^3589 := by
    have hnat : (1596388211 : ℕ)^4613*50000000000000^3589 ≤ 4728800469521^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596388211 10000000000 4728800469521 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698939351/5000000000 : ℝ)^4613 ≤ (45271202223031/100000000000000 : ℝ)^3589 := by
    have hnat : (2698939351 : ℕ)^4613*100000000000000^3589 ≤ 45271202223031^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698939351 5000000000 45271202223031 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698939101/5000000000 : ℝ)^4613 ≤ (45271196833153/100000000000000 : ℝ)^3589 := by
    have hnat : (2698939101 : ℕ)^4613*100000000000000^3589 ≤ 45271196833153^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698939101 5000000000 45271196833153 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1596388211/10000000000 : ℝ), (2698939351/5000000000 : ℝ), (2698939101/5000000000 : ℝ)] ![(4728800469521/50000000000000 : ℝ), (45271202223031/100000000000000 : ℝ), (45271196833153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1596388211/10000000000 : ℝ)|^4613 ≤ (4728800469521/50000000000000 : ℝ)^3589
        have hw : |(-1596388211/10000000000 : ℝ)|=(1596388211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698939351/5000000000 : ℝ)|^4613 ≤ (45271202223031/100000000000000 : ℝ)^3589
        have hw : |(2698939351/5000000000 : ℝ)|=(2698939351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698939101/5000000000 : ℝ)|^4613 ≤ (45271196833153/100000000000000 : ℝ)^3589
        have hw : |(2698939101/5000000000 : ℝ)|=(2698939101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_1 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271127227/10000000000 : ℝ)*x 0 + (-44312917/250000000 : ℝ)*x 1 + (5397878523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271127227/10000000000 : ℝ)^4613 ≤ (21954727640309/50000000000000 : ℝ)^3589 := by
    have hnat : (5271127227 : ℕ)^4613*50000000000000^3589 ≤ 21954727640309^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271127227 10000000000 21954727640309 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44312917/250000000 : ℝ)^4613 ≤ (2704836104469/25000000000000 : ℝ)^3589 := by
    have hnat : (44312917 : ℕ)^4613*25000000000000^3589 ≤ 2704836104469^3589*250000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44312917 250000000 2704836104469 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397878523/10000000000 : ℝ)^4613 ≤ (22635600146727/50000000000000 : ℝ)^3589 := by
    have hnat : (5397878523 : ℕ)^4613*50000000000000^3589 ≤ 22635600146727^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397878523 10000000000 22635600146727 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271127227/10000000000 : ℝ), (-44312917/250000000 : ℝ), (5397878523/10000000000 : ℝ)] ![(21954727640309/50000000000000 : ℝ), (2704836104469/25000000000000 : ℝ), (22635600146727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271127227/10000000000 : ℝ)|^4613 ≤ (21954727640309/50000000000000 : ℝ)^3589
        have hw : |(5271127227/10000000000 : ℝ)|=(5271127227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44312917/250000000 : ℝ)|^4613 ≤ (2704836104469/25000000000000 : ℝ)^3589
        have hw : |(-44312917/250000000 : ℝ)|=(44312917/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397878523/10000000000 : ℝ)|^4613 ≤ (22635600146727/50000000000000 : ℝ)^3589
        have hw : |(5397878523/10000000000 : ℝ)|=(5397878523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_2 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054225493/2000000000 : ℝ)*x 0 + (10542731/19531250 : ℝ)*x 1 + (-1772516699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054225493/2000000000 : ℝ)^4613 ≤ (42880329911/97656250000 : ℝ)^3589 := by
    have hnat : (1054225493 : ℕ)^4613*97656250000^3589 ≤ 42880329911^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054225493 2000000000 42880329911 97656250000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10542731/19531250 : ℝ)^4613 ≤ (5658899698467/12500000000000 : ℝ)^3589 := by
    have hnat : (10542731 : ℕ)^4613*12500000000000^3589 ≤ 5658899698467^3589*19531250^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10542731 19531250 5658899698467 12500000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1772516699/10000000000 : ℝ)^4613 ≤ (540967228347/5000000000000 : ℝ)^3589 := by
    have hnat : (1772516699 : ℕ)^4613*5000000000000^3589 ≤ 540967228347^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772516699 10000000000 540967228347 5000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054225493/2000000000 : ℝ), (10542731/19531250 : ℝ), (-1772516699/10000000000 : ℝ)] ![(42880329911/97656250000 : ℝ), (5658899698467/12500000000000 : ℝ), (540967228347/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054225493/2000000000 : ℝ)|^4613 ≤ (42880329911/97656250000 : ℝ)^3589
        have hw : |(1054225493/2000000000 : ℝ)|=(1054225493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10542731/19531250 : ℝ)|^4613 ≤ (5658899698467/12500000000000 : ℝ)^3589
        have hw : |(10542731/19531250 : ℝ)|=(10542731/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1772516699/10000000000 : ℝ)|^4613 ≤ (540967228347/5000000000000 : ℝ)^3589
        have hw : |(-1772516699/10000000000 : ℝ)|=(1772516699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_3 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4449960069/10000000000 : ℝ)*x 0 + (1038738379/2500000000 : ℝ)*x 1 + (830990697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4449960069/10000000000 : ℝ)^4613 ≤ (4415058009049/12500000000000 : ℝ)^3589 := by
    have hnat : (4449960069 : ℕ)^4613*12500000000000^3589 ≤ 4415058009049^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4449960069 10000000000 4415058009049 12500000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038738379/2500000000 : ℝ)^4613 ≤ (16169884055859/50000000000000 : ℝ)^3589 := by
    have hnat : (1038738379 : ℕ)^4613*50000000000000^3589 ≤ 16169884055859^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038738379 2500000000 16169884055859 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830990697/2000000000 : ℝ)^4613 ≤ (32339767801589/100000000000000 : ℝ)^3589 := by
    have hnat : (830990697 : ℕ)^4613*100000000000000^3589 ≤ 32339767801589^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830990697 2000000000 32339767801589 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4449960069/10000000000 : ℝ), (1038738379/2500000000 : ℝ), (830990697/2000000000 : ℝ)] ![(4415058009049/12500000000000 : ℝ), (16169884055859/50000000000000 : ℝ), (32339767801589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4449960069/10000000000 : ℝ)|^4613 ≤ (4415058009049/12500000000000 : ℝ)^3589
        have hw : |(4449960069/10000000000 : ℝ)|=(4449960069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1038738379/2500000000 : ℝ)|^4613 ≤ (16169884055859/50000000000000 : ℝ)^3589
        have hw : |(1038738379/2500000000 : ℝ)|=(1038738379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830990697/2000000000 : ℝ)|^4613 ≤ (32339767801589/100000000000000 : ℝ)^3589
        have hw : |(830990697/2000000000 : ℝ)|=(830990697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_4 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-251661659/1250000000 : ℝ)*x 0 + (2622414251/5000000000 : ℝ)*x 1 + (1048965733/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251661659/1250000000 : ℝ)^4613 ≤ (3185960761111/25000000000000 : ℝ)^3589 := by
    have hnat : (251661659 : ℕ)^4613*25000000000000^3589 ≤ 3185960761111^3589*1250000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251661659 1250000000 3185960761111 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622414251/5000000000 : ℝ)^4613 ≤ (10907019398767/25000000000000 : ℝ)^3589 := by
    have hnat : (2622414251 : ℕ)^4613*25000000000000^3589 ≤ 10907019398767^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622414251 5000000000 10907019398767 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048965733/2000000000 : ℝ)^4613 ≤ (43628079337807/100000000000000 : ℝ)^3589 := by
    have hnat : (1048965733 : ℕ)^4613*100000000000000^3589 ≤ 43628079337807^3589*2000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048965733 2000000000 43628079337807 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-251661659/1250000000 : ℝ), (2622414251/5000000000 : ℝ), (1048965733/2000000000 : ℝ)] ![(3185960761111/25000000000000 : ℝ), (10907019398767/25000000000000 : ℝ), (43628079337807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-251661659/1250000000 : ℝ)|^4613 ≤ (3185960761111/25000000000000 : ℝ)^3589
        have hw : |(-251661659/1250000000 : ℝ)|=(251661659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622414251/5000000000 : ℝ)|^4613 ≤ (10907019398767/25000000000000 : ℝ)^3589
        have hw : |(2622414251/5000000000 : ℝ)|=(2622414251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048965733/2000000000 : ℝ)|^4613 ≤ (43628079337807/100000000000000 : ℝ)^3589
        have hw : |(1048965733/2000000000 : ℝ)|=(1048965733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_5 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377312637/10000000000 : ℝ)*x 0 + (-918149457/5000000000 : ℝ)*x 1 + (262241433/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377312637/10000000000 : ℝ)^4613 ≤ (45049625683517/100000000000000 : ℝ)^3589 := by
    have hnat : (5377312637 : ℕ)^4613*100000000000000^3589 ≤ 45049625683517^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377312637 10000000000 45049625683517 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (918149457/5000000000 : ℝ)^4613 ≤ (11322295006001/100000000000000 : ℝ)^3589 := by
    have hnat : (918149457 : ℕ)^4613*100000000000000^3589 ≤ 11322295006001^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918149457 5000000000 11322295006001 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262241433/500000000 : ℝ)^4613 ≤ (43628079284349/100000000000000 : ℝ)^3589 := by
    have hnat : (262241433 : ℕ)^4613*100000000000000^3589 ≤ 43628079284349^3589*500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262241433 500000000 43628079284349 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377312637/10000000000 : ℝ), (-918149457/5000000000 : ℝ), (262241433/500000000 : ℝ)] ![(45049625683517/100000000000000 : ℝ), (11322295006001/100000000000000 : ℝ), (43628079284349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377312637/10000000000 : ℝ)|^4613 ≤ (45049625683517/100000000000000 : ℝ)^3589
        have hw : |(5377312637/10000000000 : ℝ)|=(5377312637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-918149457/5000000000 : ℝ)|^4613 ≤ (11322295006001/100000000000000 : ℝ)^3589
        have hw : |(-918149457/5000000000 : ℝ)|=(918149457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262241433/500000000 : ℝ)|^4613 ≤ (43628079284349/100000000000000 : ℝ)^3589
        have hw : |(262241433/500000000 : ℝ)|=(262241433/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_6 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688656111/5000000000 : ℝ)*x 0 + (5244828851/10000000000 : ℝ)*x 1 + (-918149611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688656111/5000000000 : ℝ)^4613 ≤ (45049621214789/100000000000000 : ℝ)^3589 := by
    have hnat : (2688656111 : ℕ)^4613*100000000000000^3589 ≤ 45049621214789^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688656111 5000000000 45049621214789 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244828851/10000000000 : ℝ)^4613 ≤ (21814040663227/50000000000000 : ℝ)^3589 := by
    have hnat : (5244828851 : ℕ)^4613*50000000000000^3589 ≤ 21814040663227^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244828851 10000000000 21814040663227 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (918149611/5000000000 : ℝ)^4613 ≤ (11322297446911/100000000000000 : ℝ)^3589 := by
    have hnat : (918149611 : ℕ)^4613*100000000000000^3589 ≤ 11322297446911^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918149611 5000000000 11322297446911 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688656111/5000000000 : ℝ), (5244828851/10000000000 : ℝ), (-918149611/5000000000 : ℝ)] ![(45049621214789/100000000000000 : ℝ), (21814040663227/50000000000000 : ℝ), (11322297446911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688656111/5000000000 : ℝ)|^4613 ≤ (45049621214789/100000000000000 : ℝ)^3589
        have hw : |(2688656111/5000000000 : ℝ)|=(2688656111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244828851/10000000000 : ℝ)|^4613 ≤ (21814040663227/50000000000000 : ℝ)^3589
        have hw : |(5244828851/10000000000 : ℝ)|=(5244828851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-918149611/5000000000 : ℝ)|^4613 ≤ (11322297446911/100000000000000 : ℝ)^3589
        have hw : |(-918149611/5000000000 : ℝ)|=(918149611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_7 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1011261413/2500000000 : ℝ)*x 0 + (13616507/31250000 : ℝ)*x 1 + (4357281673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1011261413/2500000000 : ℝ)^4613 ≤ (6248881538317/20000000000000 : ℝ)^3589 := by
    have hnat : (1011261413 : ℕ)^4613*20000000000000^3589 ≤ 6248881538317^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011261413 2500000000 6248881538317 20000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13616507/31250000 : ℝ)^4613 ≤ (34377799020991/100000000000000 : ℝ)^3589 := by
    have hnat : (13616507 : ℕ)^4613*100000000000000^3589 ≤ 34377799020991^3589*31250000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13616507 31250000 34377799020991 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4357281673/10000000000 : ℝ)^4613 ≤ (8594448317789/25000000000000 : ℝ)^3589 := by
    have hnat : (4357281673 : ℕ)^4613*25000000000000^3589 ≤ 8594448317789^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357281673 10000000000 8594448317789 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1011261413/2500000000 : ℝ), (13616507/31250000 : ℝ), (4357281673/10000000000 : ℝ)] ![(6248881538317/20000000000000 : ℝ), (34377799020991/100000000000000 : ℝ), (8594448317789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1011261413/2500000000 : ℝ)|^4613 ≤ (6248881538317/20000000000000 : ℝ)^3589
        have hw : |(1011261413/2500000000 : ℝ)|=(1011261413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13616507/31250000 : ℝ)|^4613 ≤ (34377799020991/100000000000000 : ℝ)^3589
        have hw : |(13616507/31250000 : ℝ)|=(13616507/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4357281673/10000000000 : ℝ)|^4613 ≤ (8594448317789/25000000000000 : ℝ)^3589
        have hw : |(4357281673/10000000000 : ℝ)|=(4357281673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_8 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-962486881/5000000000 : ℝ)*x 0 + (5137122567/10000000000 : ℝ)*x 1 + (2709094223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962486881/5000000000 : ℝ)^4613 ≤ (12029832765639/100000000000000 : ℝ)^3589 := by
    have hnat : (962486881 : ℕ)^4613*100000000000000^3589 ≤ 12029832765639^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962486881 5000000000 12029832765639 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137122567/10000000000 : ℝ)^4613 ≤ (42479913525631/100000000000000 : ℝ)^3589 := by
    have hnat : (5137122567 : ℕ)^4613*100000000000000^3589 ≤ 42479913525631^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137122567 10000000000 42479913525631 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709094223/5000000000 : ℝ)^4613 ≤ (45490253703043/100000000000000 : ℝ)^3589 := by
    have hnat : (2709094223 : ℕ)^4613*100000000000000^3589 ≤ 45490253703043^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709094223 5000000000 45490253703043 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-962486881/5000000000 : ℝ), (5137122567/10000000000 : ℝ), (2709094223/5000000000 : ℝ)] ![(12029832765639/100000000000000 : ℝ), (42479913525631/100000000000000 : ℝ), (45490253703043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-962486881/5000000000 : ℝ)|^4613 ≤ (12029832765639/100000000000000 : ℝ)^3589
        have hw : |(-962486881/5000000000 : ℝ)|=(962486881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137122567/10000000000 : ℝ)|^4613 ≤ (42479913525631/100000000000000 : ℝ)^3589
        have hw : |(5137122567/10000000000 : ℝ)|=(5137122567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709094223/5000000000 : ℝ)|^4613 ≤ (45490253703043/100000000000000 : ℝ)^3589
        have hw : |(2709094223/5000000000 : ℝ)|=(2709094223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_9 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262851623/500000000 : ℝ)*x 0 + (-176381779/1000000000 : ℝ)*x 1 + (541818843/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262851623/500000000 : ℝ)^4613 ≤ (43758601345323/100000000000000 : ℝ)^3589 := by
    have hnat : (262851623 : ℕ)^4613*100000000000000^3589 ≤ 43758601345323^3589*500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262851623 500000000 43758601345323 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176381779/1000000000 : ℝ)^4613 ≤ (10751145115643/100000000000000 : ℝ)^3589 := by
    have hnat : (176381779 : ℕ)^4613*100000000000000^3589 ≤ 10751145115643^3589*1000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176381779 1000000000 10751145115643 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541818843/1000000000 : ℝ)^4613 ≤ (22745126765191/50000000000000 : ℝ)^3589 := by
    have hnat : (541818843 : ℕ)^4613*50000000000000^3589 ≤ 22745126765191^3589*1000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541818843 1000000000 22745126765191 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262851623/500000000 : ℝ), (-176381779/1000000000 : ℝ), (541818843/1000000000 : ℝ)] ![(43758601345323/100000000000000 : ℝ), (10751145115643/100000000000000 : ℝ), (22745126765191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262851623/500000000 : ℝ)|^4613 ≤ (43758601345323/100000000000000 : ℝ)^3589
        have hw : |(262851623/500000000 : ℝ)|=(262851623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-176381779/1000000000 : ℝ)|^4613 ≤ (10751145115643/100000000000000 : ℝ)^3589
        have hw : |(-176381779/1000000000 : ℝ)|=(176381779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541818843/1000000000 : ℝ)|^4613 ≤ (22745126765191/50000000000000 : ℝ)^3589
        have hw : |(541818843/1000000000 : ℝ)|=(541818843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_10 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257032381/10000000000 : ℝ)*x 0 + (5418188397/10000000000 : ℝ)*x 1 + (-1763817943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257032381/10000000000 : ℝ)^4613 ≤ (21879300250061/50000000000000 : ℝ)^3589 := by
    have hnat : (5257032381 : ℕ)^4613*50000000000000^3589 ≤ 21879300250061^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257032381 10000000000 21879300250061 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418188397/10000000000 : ℝ)^4613 ≤ (11372563293567/25000000000000 : ℝ)^3589 := by
    have hnat : (5418188397 : ℕ)^4613*25000000000000^3589 ≤ 11372563293567^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418188397 10000000000 11372563293567 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1763817943/10000000000 : ℝ)^4613 ≤ (10751146314321/100000000000000 : ℝ)^3589 := by
    have hnat : (1763817943 : ℕ)^4613*100000000000000^3589 ≤ 10751146314321^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763817943 10000000000 10751146314321 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257032381/10000000000 : ℝ), (5418188397/10000000000 : ℝ), (-1763817943/10000000000 : ℝ)] ![(21879300250061/50000000000000 : ℝ), (11372563293567/25000000000000 : ℝ), (10751146314321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257032381/10000000000 : ℝ)|^4613 ≤ (21879300250061/50000000000000 : ℝ)^3589
        have hw : |(5257032381/10000000000 : ℝ)|=(5257032381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418188397/10000000000 : ℝ)|^4613 ≤ (11372563293567/25000000000000 : ℝ)^3589
        have hw : |(5418188397/10000000000 : ℝ)|=(5418188397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1763817943/10000000000 : ℝ)|^4613 ≤ (10751146314321/100000000000000 : ℝ)^3589
        have hw : |(-1763817943/10000000000 : ℝ)|=(1763817943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_11 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1125636603/2500000000 : ℝ)*x 0 + (4128070351/10000000000 : ℝ)*x 1 + (4128071153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1125636603/2500000000 : ℝ)^4613 ≤ (896446140059/2500000000000 : ℝ)^3589 := by
    have hnat : (1125636603 : ℕ)^4613*2500000000000^3589 ≤ 896446140059^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125636603 2500000000 896446140059 2500000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128070351/10000000000 : ℝ)^4613 ≤ (32071073189923/100000000000000 : ℝ)^3589 := by
    have hnat : (4128070351 : ℕ)^4613*100000000000000^3589 ≤ 32071073189923^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128070351 10000000000 32071073189923 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4128071153/10000000000 : ℝ)^4613 ≤ (2004442574901/6250000000000 : ℝ)^3589 := by
    have hnat : (4128071153 : ℕ)^4613*6250000000000^3589 ≤ 2004442574901^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128071153 10000000000 2004442574901 6250000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1125636603/2500000000 : ℝ), (4128070351/10000000000 : ℝ), (4128071153/10000000000 : ℝ)] ![(896446140059/2500000000000 : ℝ), (32071073189923/100000000000000 : ℝ), (2004442574901/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1125636603/2500000000 : ℝ)|^4613 ≤ (896446140059/2500000000000 : ℝ)^3589
        have hw : |(1125636603/2500000000 : ℝ)|=(1125636603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128070351/10000000000 : ℝ)|^4613 ≤ (32071073189923/100000000000000 : ℝ)^3589
        have hw : |(4128070351/10000000000 : ℝ)|=(4128070351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4128071153/10000000000 : ℝ)|^4613 ≤ (2004442574901/6250000000000 : ℝ)^3589
        have hw : |(4128071153/10000000000 : ℝ)|=(4128071153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_12 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-842212351/5000000000 : ℝ)*x 0 + (2751133293/5000000000 : ℝ)*x 1 + (2614890157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842212351/5000000000 : ℝ)^4613 ≤ (1266647269027/12500000000000 : ℝ)^3589 := by
    have hnat : (842212351 : ℕ)^4613*12500000000000^3589 ≤ 1266647269027^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842212351 5000000000 1266647269027 12500000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2751133293/5000000000 : ℝ)^4613 ≤ (23199784159723/50000000000000 : ℝ)^3589 := by
    have hnat : (2751133293 : ℕ)^4613*50000000000000^3589 ≤ 23199784159723^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751133293 5000000000 23199784159723 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614890157/5000000000 : ℝ)^4613 ≤ (10866813379153/25000000000000 : ℝ)^3589 := by
    have hnat : (2614890157 : ℕ)^4613*25000000000000^3589 ≤ 10866813379153^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614890157 5000000000 10866813379153 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-842212351/5000000000 : ℝ), (2751133293/5000000000 : ℝ), (2614890157/5000000000 : ℝ)] ![(1266647269027/12500000000000 : ℝ), (23199784159723/50000000000000 : ℝ), (10866813379153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-842212351/5000000000 : ℝ)|^4613 ≤ (1266647269027/12500000000000 : ℝ)^3589
        have hw : |(-842212351/5000000000 : ℝ)|=(842212351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2751133293/5000000000 : ℝ)|^4613 ≤ (23199784159723/50000000000000 : ℝ)^3589
        have hw : |(2751133293/5000000000 : ℝ)|=(2751133293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614890157/5000000000 : ℝ)|^4613 ≤ (10866813379153/25000000000000 : ℝ)^3589
        have hw : |(2614890157/5000000000 : ℝ)|=(2614890157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_13 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2693876881/5000000000 : ℝ)*x 0 + (-921199619/5000000000 : ℝ)*x 1 + (2614889981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2693876881/5000000000 : ℝ)^4613 ≤ (1806483482641/4000000000000 : ℝ)^3589 := by
    have hnat : (2693876881 : ℕ)^4613*4000000000000^3589 ≤ 1806483482641^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693876881 5000000000 1806483482641 4000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921199619/5000000000 : ℝ)^4613 ≤ (2842665792353/25000000000000 : ℝ)^3589 := by
    have hnat : (921199619 : ℕ)^4613*25000000000000^3589 ≤ 2842665792353^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921199619 5000000000 2842665792353 25000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614889981/5000000000 : ℝ)^4613 ≤ (8693449951247/20000000000000 : ℝ)^3589 := by
    have hnat : (2614889981 : ℕ)^4613*20000000000000^3589 ≤ 8693449951247^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614889981 5000000000 8693449951247 20000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2693876881/5000000000 : ℝ), (-921199619/5000000000 : ℝ), (2614889981/5000000000 : ℝ)] ![(1806483482641/4000000000000 : ℝ), (2842665792353/25000000000000 : ℝ), (8693449951247/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2693876881/5000000000 : ℝ)|^4613 ≤ (1806483482641/4000000000000 : ℝ)^3589
        have hw : |(2693876881/5000000000 : ℝ)|=(2693876881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-921199619/5000000000 : ℝ)|^4613 ≤ (2842665792353/25000000000000 : ℝ)^3589
        have hw : |(-921199619/5000000000 : ℝ)|=(921199619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614889981/5000000000 : ℝ)|^4613 ≤ (8693449951247/20000000000000 : ℝ)^3589
        have hw : |(2614889981/5000000000 : ℝ)|=(2614889981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_14 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215510207/400000000 : ℝ)*x 0 + (2614889367/5000000000 : ℝ)*x 1 + (-460599743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215510207/400000000 : ℝ)^4613 ≤ (22581051144831/50000000000000 : ℝ)^3589 := by
    have hnat : (215510207 : ℕ)^4613*50000000000000^3589 ≤ 22581051144831^3589*400000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215510207 400000000 22581051144831 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614889367/5000000000 : ℝ)^4613 ≤ (43467236637647/100000000000000 : ℝ)^3589 := by
    have hnat : (2614889367 : ℕ)^4613*100000000000000^3589 ≤ 43467236637647^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614889367 5000000000 43467236637647 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460599743/2500000000 : ℝ)^4613 ≤ (11370661059357/100000000000000 : ℝ)^3589 := by
    have hnat : (460599743 : ℕ)^4613*100000000000000^3589 ≤ 11370661059357^3589*2500000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460599743 2500000000 11370661059357 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215510207/400000000 : ℝ), (2614889367/5000000000 : ℝ), (-460599743/2500000000 : ℝ)] ![(22581051144831/50000000000000 : ℝ), (43467236637647/100000000000000 : ℝ), (11370661059357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215510207/400000000 : ℝ)|^4613 ≤ (22581051144831/50000000000000 : ℝ)^3589
        have hw : |(215510207/400000000 : ℝ)|=(215510207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614889367/5000000000 : ℝ)|^4613 ≤ (43467236637647/100000000000000 : ℝ)^3589
        have hw : |(2614889367/5000000000 : ℝ)|=(2614889367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-460599743/2500000000 : ℝ)|^4613 ≤ (11370661059357/100000000000000 : ℝ)^3589
        have hw : |(-460599743/2500000000 : ℝ)|=(460599743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1558_box_15 (p : ℝ) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (250273151/625000000 : ℝ)*x 0 + (4377151489/10000000000 : ℝ)*x 1 + (2188575373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250273151/625000000 : ℝ)^4613 ≤ (15420583663431/50000000000000 : ℝ)^3589 := by
    have hnat : (250273151 : ℕ)^4613*50000000000000^3589 ≤ 15420583663431^3589*625000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250273151 625000000 15420583663431 50000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4377151489/10000000000 : ℝ)^4613 ≤ (34579420104947/100000000000000 : ℝ)^3589 := by
    have hnat : (4377151489 : ℕ)^4613*100000000000000^3589 ≤ 34579420104947^3589*10000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377151489 10000000000 34579420104947 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188575373/5000000000 : ℝ)^4613 ≤ (34579412560543/100000000000000 : ℝ)^3589 := by
    have hnat : (2188575373 : ℕ)^4613*100000000000000^3589 ≤ 34579412560543^3589*5000000000^4613 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188575373 5000000000 34579412560543 100000000000000 4613 3589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4613/1024 : ℝ)) 4613 3589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(250273151/625000000 : ℝ), (4377151489/10000000000 : ℝ), (2188575373/5000000000 : ℝ)] ![(15420583663431/50000000000000 : ℝ), (34579420104947/100000000000000 : ℝ), (34579412560543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(250273151/625000000 : ℝ)|^4613 ≤ (15420583663431/50000000000000 : ℝ)^3589
        have hw : |(250273151/625000000 : ℝ)|=(250273151/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4377151489/10000000000 : ℝ)|^4613 ≤ (34579420104947/100000000000000 : ℝ)^3589
        have hw : |(4377151489/10000000000 : ℝ)|=(4377151489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2188575373/5000000000 : ℝ)|^4613 ≤ (34579412560543/100000000000000 : ℝ)^3589
        have hw : |(2188575373/5000000000 : ℝ)|=(2188575373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1558_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5541/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1994/3125 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11769/20000 : ℝ) ∧ (80799/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21573/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5541/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5541/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5541/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5541/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5541/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5541/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5541/50000 : ℝ) ^ (4611/1024 : ℝ) ≤ (4988645987708089/100000000000000000000 : ℝ) := by
    have hpowers : (5541/50000 : ℝ)^4611 ≤ (4988645987708089/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5541 : ℕ)^4611*100000000000000000000^1024 ≤ 4988645987708089^1024*50000^4611 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5541 50000 4988645987708089 100000000000000000000 4611 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5541/50000 : ℝ)) (X := (4988645987708089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4611/1024 : ℝ) ≤ (22502311721517179/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4611 ≤ (22502311721517179/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4611*100000000000000000000^1024 ≤ 22502311721517179^1024*20000^4611 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 22502311721517179 100000000000000000000 4611 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (22502311721517179/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004988645987708089/50000000000000000000 : ℝ) ≤ (1000022156474771/1000000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (50004988645987708089/50000000000000000000 : ℝ)^1024 ≤ (1000022156474771/1000000000000000 : ℝ)^4611 := by
      have hnat : (50004988645987708089 : ℕ)^1024*1000000000000000^4611 ≤ 1000022156474771^4611*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004988645987708089 50000000000000000000 1000022156474771 1000000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000022156474771/1000000000000000 : ℝ)) (X := (50004988645987708089/50000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006872739427306317/25000000000000000000 : ℝ) ≤ (10000610447431137/10000000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (25006872739427306317/25000000000000000000 : ℝ)^1024 ≤ (10000610447431137/10000000000000000 : ℝ)^4611 := by
      have hnat : (25006872739427306317 : ℕ)^1024*10000000000000000^4611 ≤ 10000610447431137^4611*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006872739427306317 25000000000000000000 10000610447431137 10000000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000610447431137/10000000000000000 : ℝ)) (X := (25006872739427306317/25000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022502311721517179/50000000000000000000 : ℝ) ≤ (2500249832528641/2500000000000000 : ℝ) ^ (4611/1024 : ℝ) := by
    have hpowers : (50022502311721517179/50000000000000000000 : ℝ)^1024 ≤ (2500249832528641/2500000000000000 : ℝ)^4611 := by
      have hnat : (50022502311721517179 : ℕ)^1024*2500000000000000^4611 ≤ 2500249832528641^4611*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022502311721517179 50000000000000000000 2500249832528641 2500000000000000 1024 4611 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500249832528641/2500000000000000 : ℝ)) (X := (50022502311721517179/50000000000000000000 : ℝ)) (by norm_num) 4611 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4988645987708089/100000000000000000000 : ℝ) ≤ ((3144454025270620793/3145000000000000000 : ℝ)+2*(55554669061/62900000000000 : ℝ)*(5541/50000 : ℝ))^(4611/1024 : ℝ) := by
    rw [show (3144454025270620793/3145000000000000000 : ℝ)+2*(55554669061/62900000000000 : ℝ)*(5541/50000 : ℝ)=(1000022156474771/1000000000000000 : ℝ) by norm_num, show 1+2*(4988645987708089/100000000000000000000 : ℝ)=(50004988645987708089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22502311721517179/100000000000000000000 : ℝ)+(4988645987708089/100000000000000000000 : ℝ) ≤ ((3144454025270620793/3145000000000000000 : ℝ)+(55554669061/62900000000000 : ℝ)*((3097/20000 : ℝ)+(5541/50000 : ℝ)))^(4611/1024 : ℝ) := by
    rw [show (3144454025270620793/3145000000000000000 : ℝ)+(55554669061/62900000000000 : ℝ)*((3097/20000 : ℝ)+(5541/50000 : ℝ))=(10000610447431137/10000000000000000 : ℝ) by norm_num, show 1+(22502311721517179/100000000000000000000 : ℝ)+(4988645987708089/100000000000000000000 : ℝ)=(25006872739427306317/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22502311721517179/100000000000000000000 : ℝ) ≤ ((3144454025270620793/3145000000000000000 : ℝ)+2*(55554669061/62900000000000 : ℝ)*(3097/20000 : ℝ))^(4611/1024 : ℝ) := by
    rw [show (3144454025270620793/3145000000000000000 : ℝ)+2*(55554669061/62900000000000 : ℝ)*(3097/20000 : ℝ)=(2500249832528641/2500000000000000 : ℝ) by norm_num, show 1+2*(22502311721517179/100000000000000000000 : ℝ)=(50022502311721517179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3144454025270620793/3145000000000000000 : ℝ)*(X 1 0+X 2 0)+(55554669061/62900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (5541/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (3144454025270620793/3145000000000000000 : ℝ)) (alpha := (55554669061/62900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3144454025270620793/3145000000000000000 : ℝ)*(X 0 1+X 2 1)+(55554669061/62900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (5541/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (3144454025270620793/3145000000000000000 : ℝ)) (alpha := (55554669061/62900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3144454025270620793/3145000000000000000 : ℝ)*(X 0 2+X 1 2)+(55554669061/62900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4611/1024 : ℝ)) (lo := (5541/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (3144454025270620793/3145000000000000000 : ℝ)) (alpha := (55554669061/62900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1596388211/10000000000 : ℝ)*X 0 0+(2698939351/5000000000 : ℝ)*X 0 1+(2698939101/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271127227/10000000000 : ℝ)*X 1 0+(-44312917/250000000 : ℝ)*X 1 1+(5397878523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1054225493/2000000000 : ℝ)*X 2 0+(10542731/19531250 : ℝ)*X 2 1+(-1772516699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4449960069/10000000000 : ℝ)*X 0 0+(1038738379/2500000000 : ℝ)*X 0 1+(830990697/2000000000 : ℝ)*X 0 2+(4449960069/10000000000 : ℝ)*X 1 0+(1038738379/2500000000 : ℝ)*X 1 1+(830990697/2000000000 : ℝ)*X 1 2+(4449960069/10000000000 : ℝ)*X 2 0+(1038738379/2500000000 : ℝ)*X 2 1+(830990697/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-251661659/1250000000 : ℝ)*X 0 0+(2622414251/5000000000 : ℝ)*X 0 1+(1048965733/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5377312637/10000000000 : ℝ)*X 1 0+(-918149457/5000000000 : ℝ)*X 1 1+(262241433/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2688656111/5000000000 : ℝ)*X 2 0+(5244828851/10000000000 : ℝ)*X 2 1+(-918149611/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1011261413/2500000000 : ℝ)*X 0 0+(13616507/31250000 : ℝ)*X 0 1+(4357281673/10000000000 : ℝ)*X 0 2+(1011261413/2500000000 : ℝ)*X 1 0+(13616507/31250000 : ℝ)*X 1 1+(4357281673/10000000000 : ℝ)*X 1 2+(1011261413/2500000000 : ℝ)*X 2 0+(13616507/31250000 : ℝ)*X 2 1+(4357281673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-962486881/5000000000 : ℝ)*X 0 0+(5137122567/10000000000 : ℝ)*X 0 1+(2709094223/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((262851623/500000000 : ℝ)*X 1 0+(-176381779/1000000000 : ℝ)*X 1 1+(541818843/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5257032381/10000000000 : ℝ)*X 2 0+(5418188397/10000000000 : ℝ)*X 2 1+(-1763817943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1125636603/2500000000 : ℝ)*X 0 0+(4128070351/10000000000 : ℝ)*X 0 1+(4128071153/10000000000 : ℝ)*X 0 2+(1125636603/2500000000 : ℝ)*X 1 0+(4128070351/10000000000 : ℝ)*X 1 1+(4128071153/10000000000 : ℝ)*X 1 2+(1125636603/2500000000 : ℝ)*X 2 0+(4128070351/10000000000 : ℝ)*X 2 1+(4128071153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-842212351/5000000000 : ℝ)*X 0 0+(2751133293/5000000000 : ℝ)*X 0 1+(2614890157/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2693876881/5000000000 : ℝ)*X 1 0+(-921199619/5000000000 : ℝ)*X 1 1+(2614889981/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((215510207/400000000 : ℝ)*X 2 0+(2614889367/5000000000 : ℝ)*X 2 1+(-460599743/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((250273151/625000000 : ℝ)*X 0 0+(4377151489/10000000000 : ℝ)*X 0 1+(2188575373/5000000000 : ℝ)*X 0 2+(250273151/625000000 : ℝ)*X 1 0+(4377151489/10000000000 : ℝ)*X 1 1+(2188575373/5000000000 : ℝ)*X 1 2+(250273151/625000000 : ℝ)*X 2 0+(4377151489/10000000000 : ℝ)*X 2 1+(2188575373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1558_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1994/3125 : ℝ) ≤ (-5016710718446285257585120315587/7862500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9659561/20000000000000 : ℝ)*(lower0) + (108003993/100000000000000 : ℝ)*(upper1) + (220957/10000000000000 : ℝ)*(upper3) + (79276269/50000000000000 : ℝ)*(lower4) + (4452523/100000000000000 : ℝ)*(lower5) + (114525263405553/5000000000000 : ℝ)*(major0) + (114525263405553/5000000000000 : ℝ)*(major1) + (114525263405553/5000000000000 : ℝ)*(major2) + (161562162701407/5000000000000 : ℝ)*(sp4) + (1615587013121667/50000000000000 : ℝ)*(sp5) + (807799364242391/25000000000000 : ℝ)*(sp6) + (1371035796103653/100000000000000 : ℝ)*(sp7) + (34613892403/50000000000000 : ℝ)*(sp13) + (45797058577/100000000000000 : ℝ)*(sp14) + (1371035796103653/100000000000000 : ℝ)*(f.failure) + (161562162701407/5000000000000 : ℝ)*(f.sum) + (20070354527/9828125000000000000000000 : ℝ)*base65 + (178209894395113529/15725000000000000000000000000000 : ℝ)*base67 + (6732075427411471/15725000000000000000000000000000 : ℝ)*base70 + (127818350582763529/15725000000000000000000000000000 : ℝ)*base71 + (1462538487617/157250000000000000000000000 : ℝ)*base73 + (198080125776388529/15725000000000000000000000000000 : ℝ)*base75 + (38567013520661471/15725000000000000000000000000000 : ℝ)*base78 + (318776515368663529/15725000000000000000000000000000 : ℝ)*base79 + (6733217239639/629000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2866623/625000000000000000000 : ℝ)*base89 + (2866623/625000000000000000000 : ℝ)*base91 + (2866623/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11769/20000 : ℝ) ≤ (92538188343843768697694817/157250000000000000000000000 : ℝ) := by norm_num
    linear_combination (10902117/25000000000000 : ℝ)*(lower1) + (57358791/100000000000000 : ℝ)*(upper4) + (10383229/25000000000000 : ℝ)*(lower5) + (236991665272303/10000000000000 : ℝ)*(major0) + (236991665272303/10000000000000 : ℝ)*(major1) + (236991665272303/10000000000000 : ℝ)*(major2) + (1650821657430393/50000000000000 : ℝ)*(sp0) + (412705571022961/12500000000000 : ℝ)*(sp1) + (1650823283303367/50000000000000 : ℝ)*(sp2) + (88660468192629/6250000000000 : ℝ)*(sp3) + (862783613/25000000000000 : ℝ)*(sp5) + (726355703/50000000000000 : ℝ)*(sp6) + (1856870153/100000000000000 : ℝ)*(sp7) + (940891471/20000000000000 : ℝ)*(sp8) + (1418569347952217/100000000000000 : ℝ)*(f.failure) + (3301648019318141/100000000000000 : ℝ)*(f.sum) + (663324872351/314500000000000000000000000 : ℝ)*base65 + (416995800168503721/31450000000000000000000000000000 : ℝ)*base68 + (66311830118003721/31450000000000000000000000000000 : ℝ)*base70 + (8848407981453721/31450000000000000000000000000000 : ℝ)*base72 + (4095376187569/314500000000000000000000000 : ℝ)*base74 + (29220059561096279/31450000000000000000000000000000 : ℝ)*base75 + (7373176762646279/31450000000000000000000000000000 : ℝ)*base77 + (89693637180846279/31450000000000000000000000000000 : ℝ)*base79 + (1322954884153/629000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4735547/625000000000000000000 : ℝ)*base89 + (4735547/625000000000000000000 : ℝ)*base91 + (4735547/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80799/100000 : ℝ) ≤ (31765224923623626794541327257937/39312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86256027/100000000000000 : ℝ)*(upper2) + (127439349/100000000000000 : ℝ)*(lower3) + (37576097/100000000000000 : ℝ)*(lower4) + (1278989896980203/50000000000000 : ℝ)*(major0) + (1278989896980203/50000000000000 : ℝ)*(major1) + (1278989896980203/50000000000000 : ℝ)*(major2) + (19036619049/25000000000000 : ℝ)*(sp1) + (1028892899/12500000000000 : ℝ)*(sp2) + (14900054327/100000000000000 : ℝ)*(sp3) + (949068289/50000000000000 : ℝ)*(sp4) + (1778942388896561/50000000000000 : ℝ)*(sp8) + (55590789522711/1562500000000 : ℝ)*(sp9) + (889469611196627/25000000000000 : ℝ)*(sp10) + (1531124063935829/100000000000000 : ℝ)*(sp11) + (382784740997539/25000000000000 : ℝ)*(f.failure) + (35578866759297/1000000000000 : ℝ)*(f.sum) + (18041356495771/3145000000000000000000000000 : ℝ)*base65 + (632997930636939021/157250000000000000000000000000000 : ℝ)*base68 + (983554911091189021/157250000000000000000000000000000 : ℝ)*base70 + (918368864148560979/157250000000000000000000000000000 : ℝ)*base71 + (5301312666471/3145000000000000000000000000 : ℝ)*base73 + (155919926224689021/157250000000000000000000000000000 : ℝ)*base76 + (253954337597439021/157250000000000000000000000000000 : ℝ)*base78 + (654783592519439021/157250000000000000000000000000000 : ℝ)*base80 + (2578384376333/1572500000000000000000000000 : ℝ)*base81 + (115649/156250000000000000000 : ℝ)*base89 + (115649/156250000000000000000 : ℝ)*base91 + (115649/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-21573/25000 : ℝ) ≤ (-42403333388282544189630261/49140625000000000000000000 : ℝ) := by norm_num
    linear_combination (160583693/50000000000000 : ℝ)*(lower2) + (13345779/12500000000000 : ℝ)*(upper3) + (10204973/5000000000000 : ℝ)*(upper5) + (2598166937576559/100000000000000 : ℝ)*(major0) + (2598166937576559/100000000000000 : ℝ)*(major1) + (2598166937576559/100000000000000 : ℝ)*(major2) + (3227322297/100000000000000 : ℝ)*(sp0) + (192838896153/100000000000000 : ℝ)*(sp5) + (23863906047/6250000000000 : ℝ)*(sp6) + (5774454197/20000000000000 : ℝ)*(sp7) + (458737497665531/12500000000000 : ℝ)*(sp12) + (458713796218799/12500000000000 : ℝ)*(sp13) + (1834760693074897/50000000000000 : ℝ)*(sp14) + (777582525823939/50000000000000 : ℝ)*(sp15) + (1555193923918863/100000000000000 : ℝ)*(f.failure) + (733980641729309/20000000000000 : ℝ)*(f.sum) + (1646055790563/1572500000000000000000000000 : ℝ)*base66 + (2267760329428258713/314500000000000000000000000000000 : ℝ)*base68 + (1599675672244241287/314500000000000000000000000000000 : ℝ)*base69 + (2314960044871241287/314500000000000000000000000000000 : ℝ)*base71 + (13966706723481/3145000000000000000000000000 : ℝ)*base74 + (1789864446683241287/314500000000000000000000000000000 : ℝ)*base75 + (1105864861399258713/314500000000000000000000000000000 : ℝ)*base78 + (781772022655258713/314500000000000000000000000000000 : ℝ)*base80 + (587867824073/1572500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1005267/625000000000000000000 : ℝ)*base90 + (1005267/625000000000000000000 : ℝ)*base92 + (1005267/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1558_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5541/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1994/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(11769/20000 : ℝ) else (80799/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21573/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1558_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1558_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1994/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(11769/20000 : ℝ) else (80799/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21573/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1558_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1558_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4611/1024 : ℝ) ≤ p) (hpb : p ≤ (4613/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (10441491/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1994/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(11769/20000 : ℝ) else (80799/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21573/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1558_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
