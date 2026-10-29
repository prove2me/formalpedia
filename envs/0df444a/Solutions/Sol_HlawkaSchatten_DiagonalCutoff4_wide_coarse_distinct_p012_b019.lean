-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b019
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:23:47.318295+00:00
-- url     : https://prove2.me/submissions/6e2e2ac5-6486-4a8d-8872-be849885cec2

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c312038_s0_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-40036343/500000000 : ℝ)*x 0 + (-2265835361/5000000000 : ℝ)*x 1 + (-416503509/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40036343/500000000 : ℝ)^37 ≤ (3990224529181/100000000000000 : ℝ)^29 := by
    have hnat : (40036343 : ℕ)^37*100000000000000^29 ≤ 3990224529181^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40036343 500000000 3990224529181 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265835361/5000000000 : ℝ)^37 ≤ (7285561987017/20000000000000 : ℝ)^29 := by
    have hnat : (2265835361 : ℕ)^37*20000000000000^29 ≤ 7285561987017^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265835361 5000000000 7285561987017 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416503509/625000000 : ℝ)^37 ≤ (29790982761777/50000000000000 : ℝ)^29 := by
    have hnat : (416503509 : ℕ)^37*50000000000000^29 ≤ 29790982761777^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416503509 625000000 29790982761777 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40036343/500000000 : ℝ), (-2265835361/5000000000 : ℝ), (-416503509/625000000 : ℝ)] ![(3990224529181/100000000000000 : ℝ), (7285561987017/20000000000000 : ℝ), (29790982761777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40036343/500000000 : ℝ)|^37 ≤ (3990224529181/100000000000000 : ℝ)^29
        have hw : |(-40036343/500000000 : ℝ)|=(40036343/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2265835361/5000000000 : ℝ)|^37 ≤ (7285561987017/20000000000000 : ℝ)^29
        have hw : |(-2265835361/5000000000 : ℝ)|=(2265835361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416503509/625000000 : ℝ)|^37 ≤ (29790982761777/50000000000000 : ℝ)^29
        have hw : |(-416503509/625000000 : ℝ)|=(416503509/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5081617701/10000000000 : ℝ)*x 0 + (274628249/625000000 : ℝ)*x 1 + (-3140692289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5081617701/10000000000 : ℝ)^37 ≤ (843197063379/2000000000000 : ℝ)^29 := by
    have hnat : (5081617701 : ℕ)^37*2000000000000^29 ≤ 843197063379^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081617701 10000000000 843197063379 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274628249/625000000 : ℝ)^37 ≤ (35022346712207/100000000000000 : ℝ)^29 := by
    have hnat : (274628249 : ℕ)^37*100000000000000^29 ≤ 35022346712207^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274628249 625000000 35022346712207 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3140692289/10000000000 : ℝ)^37 ≤ (22817800106761/100000000000000 : ℝ)^29 := by
    have hnat : (3140692289 : ℕ)^37*100000000000000^29 ≤ 22817800106761^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3140692289 10000000000 22817800106761 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5081617701/10000000000 : ℝ), (274628249/625000000 : ℝ), (-3140692289/10000000000 : ℝ)] ![(843197063379/2000000000000 : ℝ), (35022346712207/100000000000000 : ℝ), (22817800106761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5081617701/10000000000 : ℝ)|^37 ≤ (843197063379/2000000000000 : ℝ)^29
        have hw : |(5081617701/10000000000 : ℝ)|=(5081617701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274628249/625000000 : ℝ)|^37 ≤ (35022346712207/100000000000000 : ℝ)^29
        have hw : |(274628249/625000000 : ℝ)|=(274628249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3140692289/10000000000 : ℝ)|^37 ≤ (22817800106761/100000000000000 : ℝ)^29
        have hw : |(-3140692289/10000000000 : ℝ)|=(3140692289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5081617631/10000000000 : ℝ)*x 0 + (-1098513007/2500000000 : ℝ)*x 1 + (19629327/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5081617631/10000000000 : ℝ)^37 ≤ (42159852427983/100000000000000 : ℝ)^29 := by
    have hnat : (5081617631 : ℕ)^37*100000000000000^29 ≤ 42159852427983^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081617631 10000000000 42159852427983 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098513007/2500000000 : ℝ)^37 ≤ (1094448348739/3125000000000 : ℝ)^29 := by
    have hnat : (1098513007 : ℕ)^37*3125000000000^29 ≤ 1094448348739^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098513007 2500000000 1094448348739 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19629327/62500000 : ℝ)^37 ≤ (178264065579/781250000000 : ℝ)^29 := by
    have hnat : (19629327 : ℕ)^37*781250000000^29 ≤ 178264065579^29*62500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19629327 62500000 178264065579 781250000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5081617631/10000000000 : ℝ), (-1098513007/2500000000 : ℝ), (19629327/62500000 : ℝ)] ![(42159852427983/100000000000000 : ℝ), (1094448348739/3125000000000 : ℝ), (178264065579/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5081617631/10000000000 : ℝ)|^37 ≤ (42159852427983/100000000000000 : ℝ)^29
        have hw : |(5081617631/10000000000 : ℝ)|=(5081617631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1098513007/2500000000 : ℝ)|^37 ≤ (1094448348739/3125000000000 : ℝ)^29
        have hw : |(-1098513007/2500000000 : ℝ)|=(1098513007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19629327/62500000 : ℝ)|^37 ≤ (178264065579/781250000000 : ℝ)^29
        have hw : |(19629327/62500000 : ℝ)|=(19629327/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_3 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^37 ≤ (1 : ℝ)^29 := by
    have hnat : (1 : ℕ)^37*1^29 ≤ 1^29*1^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^37 ≤ (0 : ℝ)^29 := by
    have hnat : (0 : ℕ)^37*1^29 ≤ 0^29*1^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^37 ≤ (0 : ℝ)^29 := by
    have hnat : (0 : ℕ)^37*1^29 ≤ 0^29*1^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^37 ≤ (1 : ℝ)^29
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^37 ≤ (0 : ℝ)^29
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^37 ≤ (0 : ℝ)^29
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-590524353/10000000000 : ℝ)*x 0 + (-1031655791/2000000000 : ℝ)*x 1 + (-1239664697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (590524353/10000000000 : ℝ)^37 ≤ (2705633285693/100000000000000 : ℝ)^29 := by
    have hnat : (590524353 : ℕ)^37*100000000000000^29 ≤ 2705633285693^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590524353 10000000000 2705633285693 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031655791/2000000000 : ℝ)^37 ≤ (10743253399147/25000000000000 : ℝ)^29 := by
    have hnat : (1031655791 : ℕ)^37*25000000000000^29 ≤ 10743253399147^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031655791 2000000000 10743253399147 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1239664697/2000000000 : ℝ)^37 ≤ (54321353114343/100000000000000 : ℝ)^29 := by
    have hnat : (1239664697 : ℕ)^37*100000000000000^29 ≤ 54321353114343^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239664697 2000000000 54321353114343 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-590524353/10000000000 : ℝ), (-1031655791/2000000000 : ℝ), (-1239664697/2000000000 : ℝ)] ![(2705633285693/100000000000000 : ℝ), (10743253399147/25000000000000 : ℝ), (54321353114343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-590524353/10000000000 : ℝ)|^37 ≤ (2705633285693/100000000000000 : ℝ)^29
        have hw : |(-590524353/10000000000 : ℝ)|=(590524353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031655791/2000000000 : ℝ)|^37 ≤ (10743253399147/25000000000000 : ℝ)^29
        have hw : |(-1031655791/2000000000 : ℝ)|=(1031655791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1239664697/2000000000 : ℝ)|^37 ≤ (54321353114343/100000000000000 : ℝ)^29
        have hw : |(-1239664697/2000000000 : ℝ)|=(1239664697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4949780627/10000000000 : ℝ)*x 0 + (2666229889/5000000000 : ℝ)*x 1 + (-218919217/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4949780627/10000000000 : ℝ)^37 ≤ (40769351205637/100000000000000 : ℝ)^29 := by
    have hnat : (4949780627 : ℕ)^37*100000000000000^29 ≤ 40769351205637^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4949780627 10000000000 40769351205637 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2666229889/5000000000 : ℝ)^37 ≤ (44832944997487/100000000000000 : ℝ)^29 := by
    have hnat : (2666229889 : ℕ)^37*100000000000000^29 ≤ 44832944997487^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2666229889 5000000000 44832944997487 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218919217/1000000000 : ℝ)^37 ≤ (14397703778547/100000000000000 : ℝ)^29 := by
    have hnat : (218919217 : ℕ)^37*100000000000000^29 ≤ 14397703778547^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218919217 1000000000 14397703778547 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4949780627/10000000000 : ℝ), (2666229889/5000000000 : ℝ), (-218919217/1000000000 : ℝ)] ![(40769351205637/100000000000000 : ℝ), (44832944997487/100000000000000 : ℝ), (14397703778547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4949780627/10000000000 : ℝ)|^37 ≤ (40769351205637/100000000000000 : ℝ)^29
        have hw : |(4949780627/10000000000 : ℝ)|=(4949780627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2666229889/5000000000 : ℝ)|^37 ≤ (44832944997487/100000000000000 : ℝ)^29
        have hw : |(2666229889/5000000000 : ℝ)|=(2666229889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-218919217/1000000000 : ℝ)|^37 ≤ (14397703778547/100000000000000 : ℝ)^29
        have hw : |(-218919217/1000000000 : ℝ)|=(218919217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2518536667/5000000000 : ℝ)*x 0 + (-3345579317/10000000000 : ℝ)*x 1 + (2125651943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2518536667/5000000000 : ℝ)^37 ≤ (1667556461237/4000000000000 : ℝ)^29 := by
    have hnat : (2518536667 : ℕ)^37*4000000000000^29 ≤ 1667556461237^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518536667 5000000000 1667556461237 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3345579317/10000000000 : ℝ)^37 ≤ (386465770297/1562500000000 : ℝ)^29 := by
    have hnat : (3345579317 : ℕ)^37*1562500000000^29 ≤ 386465770297^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3345579317 10000000000 386465770297 1562500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125651943/5000000000 : ℝ)^37 ≤ (8394319789643/25000000000000 : ℝ)^29 := by
    have hnat : (2125651943 : ℕ)^37*25000000000000^29 ≤ 8394319789643^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125651943 5000000000 8394319789643 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2518536667/5000000000 : ℝ), (-3345579317/10000000000 : ℝ), (2125651943/5000000000 : ℝ)] ![(1667556461237/4000000000000 : ℝ), (386465770297/1562500000000 : ℝ), (8394319789643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2518536667/5000000000 : ℝ)|^37 ≤ (1667556461237/4000000000000 : ℝ)^29
        have hw : |(2518536667/5000000000 : ℝ)|=(2518536667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3345579317/10000000000 : ℝ)|^37 ≤ (386465770297/1562500000000 : ℝ)^29
        have hw : |(-3345579317/10000000000 : ℝ)|=(3345579317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125651943/5000000000 : ℝ)|^37 ≤ (8394319789643/25000000000000 : ℝ)^29
        have hw : |(2125651943/5000000000 : ℝ)|=(2125651943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1428816991/2000000000 : ℝ)*x 0 + (-1029690967/10000000000 : ℝ)*x 1 + (-95743841/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1428816991/2000000000 : ℝ)^37 ≤ (3255562403907/5000000000000 : ℝ)^29 := by
    have hnat : (1428816991 : ℕ)^37*5000000000000^29 ≤ 3255562403907^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428816991 2000000000 3255562403907 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029690967/10000000000 : ℝ)^37 ≤ (549984166103/10000000000000 : ℝ)^29 := by
    have hnat : (1029690967 : ℕ)^37*10000000000000^29 ≤ 549984166103^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029690967 10000000000 549984166103 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95743841/250000000 : ℝ)^37 ≤ (918403445059/3125000000000 : ℝ)^29 := by
    have hnat : (95743841 : ℕ)^37*3125000000000^29 ≤ 918403445059^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95743841 250000000 918403445059 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1428816991/2000000000 : ℝ), (-1029690967/10000000000 : ℝ), (-95743841/250000000 : ℝ)] ![(3255562403907/5000000000000 : ℝ), (549984166103/10000000000000 : ℝ), (918403445059/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1428816991/2000000000 : ℝ)|^37 ≤ (3255562403907/5000000000000 : ℝ)^29
        have hw : |(1428816991/2000000000 : ℝ)|=(1428816991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1029690967/10000000000 : ℝ)|^37 ≤ (549984166103/10000000000000 : ℝ)^29
        have hw : |(-1029690967/10000000000 : ℝ)|=(1029690967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-95743841/250000000 : ℝ)|^37 ≤ (918403445059/3125000000000 : ℝ)^29
        have hw : |(-95743841/250000000 : ℝ)|=(95743841/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3728463/2000000000 : ℝ)*x 0 + (-4218126161/10000000000 : ℝ)*x 1 + (-7282389969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3728463/2000000000 : ℝ)^37 ≤ (32925644227/100000000000000 : ℝ)^29 := by
    have hnat : (3728463 : ℕ)^37*100000000000000^29 ≤ 32925644227^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3728463 2000000000 32925644227 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4218126161/10000000000 : ℝ)^37 ≤ (6648662200881/20000000000000 : ℝ)^29 := by
    have hnat : (4218126161 : ℕ)^37*20000000000000^29 ≤ 6648662200881^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218126161 10000000000 6648662200881 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7282389969/10000000000 : ℝ)^37 ≤ (8340470417501/12500000000000 : ℝ)^29 := by
    have hnat : (7282389969 : ℕ)^37*12500000000000^29 ≤ 8340470417501^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7282389969 10000000000 8340470417501 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3728463/2000000000 : ℝ), (-4218126161/10000000000 : ℝ), (-7282389969/10000000000 : ℝ)] ![(32925644227/100000000000000 : ℝ), (6648662200881/20000000000000 : ℝ), (8340470417501/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3728463/2000000000 : ℝ)|^37 ≤ (32925644227/100000000000000 : ℝ)^29
        have hw : |(-3728463/2000000000 : ℝ)|=(3728463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4218126161/10000000000 : ℝ)|^37 ≤ (6648662200881/20000000000000 : ℝ)^29
        have hw : |(-4218126161/10000000000 : ℝ)|=(4218126161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7282389969/10000000000 : ℝ)|^37 ≤ (8340470417501/12500000000000 : ℝ)^29
        have hw : |(-7282389969/10000000000 : ℝ)|=(7282389969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2251591877/5000000000 : ℝ)*x 0 + (927762479/2000000000 : ℝ)*x 1 + (-3514058079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251591877/5000000000 : ℝ)^37 ≤ (1445436040413/4000000000000 : ℝ)^29 := by
    have hnat : (2251591877 : ℕ)^37*4000000000000^29 ≤ 1445436040413^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251591877 5000000000 1445436040413 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (927762479/2000000000 : ℝ)^37 ≤ (18765109603583/50000000000000 : ℝ)^29 := by
    have hnat : (927762479 : ℕ)^37*50000000000000^29 ≤ 18765109603583^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927762479 2000000000 18765109603583 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3514058079/10000000000 : ℝ)^37 ≤ (26333879756421/100000000000000 : ℝ)^29 := by
    have hnat : (3514058079 : ℕ)^37*100000000000000^29 ≤ 26333879756421^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3514058079 10000000000 26333879756421 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2251591877/5000000000 : ℝ), (927762479/2000000000 : ℝ), (-3514058079/10000000000 : ℝ)] ![(1445436040413/4000000000000 : ℝ), (18765109603583/50000000000000 : ℝ), (26333879756421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2251591877/5000000000 : ℝ)|^37 ≤ (1445436040413/4000000000000 : ℝ)^29
        have hw : |(2251591877/5000000000 : ℝ)|=(2251591877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(927762479/2000000000 : ℝ)|^37 ≤ (18765109603583/50000000000000 : ℝ)^29
        have hw : |(927762479/2000000000 : ℝ)|=(927762479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3514058079/10000000000 : ℝ)|^37 ≤ (26333879756421/100000000000000 : ℝ)^29
        have hw : |(-3514058079/10000000000 : ℝ)|=(3514058079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5930958581/10000000000 : ℝ)*x 0 + (-3747878223/10000000000 : ℝ)*x 1 + (1419572579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5930958581/10000000000 : ℝ)^37 ≤ (12837446978653/25000000000000 : ℝ)^29 := by
    have hnat : (5930958581 : ℕ)^37*25000000000000^29 ≤ 12837446978653^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5930958581 10000000000 12837446978653 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3747878223/10000000000 : ℝ)^37 ≤ (3573707984943/12500000000000 : ℝ)^29 := by
    have hnat : (3747878223 : ℕ)^37*12500000000000^29 ≤ 3573707984943^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3747878223 10000000000 3573707984943 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1419572579/5000000000 : ℝ)^37 ≤ (2507568523759/12500000000000 : ℝ)^29 := by
    have hnat : (1419572579 : ℕ)^37*12500000000000^29 ≤ 2507568523759^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419572579 5000000000 2507568523759 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5930958581/10000000000 : ℝ), (-3747878223/10000000000 : ℝ), (1419572579/5000000000 : ℝ)] ![(12837446978653/25000000000000 : ℝ), (3573707984943/12500000000000 : ℝ), (2507568523759/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5930958581/10000000000 : ℝ)|^37 ≤ (12837446978653/25000000000000 : ℝ)^29
        have hw : |(5930958581/10000000000 : ℝ)|=(5930958581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3747878223/10000000000 : ℝ)|^37 ≤ (3573707984943/12500000000000 : ℝ)^29
        have hw : |(-3747878223/10000000000 : ℝ)|=(3747878223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1419572579/5000000000 : ℝ)|^37 ≤ (2507568523759/12500000000000 : ℝ)^29
        have hw : |(1419572579/5000000000 : ℝ)|=(1419572579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_19 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4470635849/5000000000 : ℝ)*x 0 + (-173655353/2000000000 : ℝ)*x 1 + (-374759417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4470635849/5000000000 : ℝ)^37 ≤ (10836828816391/12500000000000 : ℝ)^29 := by
    have hnat : (4470635849 : ℕ)^37*12500000000000^29 ≤ 10836828816391^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4470635849 5000000000 10836828816391 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173655353/2000000000 : ℝ)^37 ≤ (2212301090207/50000000000000 : ℝ)^29 := by
    have hnat : (173655353 : ℕ)^37*50000000000000^29 ≤ 2212301090207^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173655353 2000000000 2212301090207 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374759417/2500000000 : ℝ)^37 ≤ (69380994401/781250000000 : ℝ)^29 := by
    have hnat : (374759417 : ℕ)^37*781250000000^29 ≤ 69380994401^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374759417 2500000000 69380994401 781250000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4470635849/5000000000 : ℝ), (-173655353/2000000000 : ℝ), (-374759417/2500000000 : ℝ)] ![(10836828816391/12500000000000 : ℝ), (2212301090207/50000000000000 : ℝ), (69380994401/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4470635849/5000000000 : ℝ)|^37 ≤ (10836828816391/12500000000000 : ℝ)^29
        have hw : |(4470635849/5000000000 : ℝ)|=(4470635849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-173655353/2000000000 : ℝ)|^37 ≤ (2212301090207/50000000000000 : ℝ)^29
        have hw : |(-173655353/2000000000 : ℝ)|=(173655353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-374759417/2500000000 : ℝ)|^37 ≤ (69380994401/781250000000 : ℝ)^29
        have hw : |(-374759417/2500000000 : ℝ)|=(374759417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2845709/1250000000 : ℝ)*x 0 + (-972630447/2000000000 : ℝ)*x 1 + (-6709103773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2845709/1250000000 : ℝ)^37 ≤ (42486836787/100000000000000 : ℝ)^29 := by
    have hnat : (2845709 : ℕ)^37*100000000000000^29 ≤ 42486836787^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2845709 1250000000 42486836787 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (972630447/2000000000 : ℝ)^37 ≤ (39861200964633/100000000000000 : ℝ)^29 := by
    have hnat : (972630447 : ℕ)^37*100000000000000^29 ≤ 39861200964633^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972630447 2000000000 39861200964633 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6709103773/10000000000 : ℝ)^37 ≤ (60096312184933/100000000000000 : ℝ)^29 := by
    have hnat : (6709103773 : ℕ)^37*100000000000000^29 ≤ 60096312184933^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6709103773 10000000000 60096312184933 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2845709/1250000000 : ℝ), (-972630447/2000000000 : ℝ), (-6709103773/10000000000 : ℝ)] ![(42486836787/100000000000000 : ℝ), (39861200964633/100000000000000 : ℝ), (60096312184933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2845709/1250000000 : ℝ)|^37 ≤ (42486836787/100000000000000 : ℝ)^29
        have hw : |(-2845709/1250000000 : ℝ)|=(2845709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-972630447/2000000000 : ℝ)|^37 ≤ (39861200964633/100000000000000 : ℝ)^29
        have hw : |(-972630447/2000000000 : ℝ)|=(972630447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6709103773/10000000000 : ℝ)|^37 ≤ (60096312184933/100000000000000 : ℝ)^29
        have hw : |(-6709103773/10000000000 : ℝ)|=(6709103773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5926835157/10000000000 : ℝ)*x 0 + (2009175169/5000000000 : ℝ)*x 1 + (-2545021557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5926835157/10000000000 : ℝ)^37 ≤ (1026084872719/2000000000000 : ℝ)^29 := by
    have hnat : (5926835157 : ℕ)^37*2000000000000^29 ≤ 1026084872719^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5926835157 10000000000 1026084872719 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009175169/5000000000 : ℝ)^37 ≤ (6249562271469/20000000000000 : ℝ)^29 := by
    have hnat : (2009175169 : ℕ)^37*20000000000000^29 ≤ 6249562271469^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009175169 5000000000 6249562271469 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2545021557/10000000000 : ℝ)^37 ≤ (8723972494149/50000000000000 : ℝ)^29 := by
    have hnat : (2545021557 : ℕ)^37*50000000000000^29 ≤ 8723972494149^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545021557 10000000000 8723972494149 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5926835157/10000000000 : ℝ), (2009175169/5000000000 : ℝ), (-2545021557/10000000000 : ℝ)] ![(1026084872719/2000000000000 : ℝ), (6249562271469/20000000000000 : ℝ), (8723972494149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5926835157/10000000000 : ℝ)|^37 ≤ (1026084872719/2000000000000 : ℝ)^29
        have hw : |(5926835157/10000000000 : ℝ)|=(5926835157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2009175169/5000000000 : ℝ)|^37 ≤ (6249562271469/20000000000000 : ℝ)^29
        have hw : |(2009175169/5000000000 : ℝ)|=(2009175169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2545021557/10000000000 : ℝ)|^37 ≤ (8723972494149/50000000000000 : ℝ)^29
        have hw : |(-2545021557/10000000000 : ℝ)|=(2545021557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4477086591/10000000000 : ℝ)*x 0 + (-2493105289/5000000000 : ℝ)*x 1 + (394751961/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4477086591/10000000000 : ℝ)^37 ≤ (2241807957487/6250000000000 : ℝ)^29 := by
    have hnat : (4477086591 : ℕ)^37*6250000000000^29 ≤ 2241807957487^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477086591 10000000000 2241807957487 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2493105289/5000000000 : ℝ)^37 ≤ (41152572856027/100000000000000 : ℝ)^29 := by
    have hnat : (2493105289 : ℕ)^37*100000000000000^29 ≤ 41152572856027^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2493105289 5000000000 41152572856027 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394751961/1250000000 : ℝ)^37 ≤ (22978499806009/100000000000000 : ℝ)^29 := by
    have hnat : (394751961 : ℕ)^37*100000000000000^29 ≤ 22978499806009^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394751961 1250000000 22978499806009 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4477086591/10000000000 : ℝ), (-2493105289/5000000000 : ℝ), (394751961/1250000000 : ℝ)] ![(2241807957487/6250000000000 : ℝ), (41152572856027/100000000000000 : ℝ), (22978499806009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4477086591/10000000000 : ℝ)|^37 ≤ (2241807957487/6250000000000 : ℝ)^29
        have hw : |(4477086591/10000000000 : ℝ)|=(4477086591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2493105289/5000000000 : ℝ)|^37 ≤ (41152572856027/100000000000000 : ℝ)^29
        have hw : |(-2493105289/5000000000 : ℝ)|=(2493105289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(394751961/1250000000 : ℝ)|^37 ≤ (22978499806009/100000000000000 : ℝ)^29
        have hw : |(394751961/1250000000 : ℝ)|=(394751961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s0_25 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (450114583/500000000 : ℝ)*x 0 + (-956287683/10000000000 : ℝ)*x 1 + (-1319274617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450114583/500000000 : ℝ)^37 ≤ (43725101836353/50000000000000 : ℝ)^29 := by
    have hnat : (450114583 : ℕ)^37*50000000000000^29 ≤ 43725101836353^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450114583 500000000 43725101836353 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956287683/10000000000 : ℝ)^37 ≤ (5004625837243/100000000000000 : ℝ)^29 := by
    have hnat : (956287683 : ℕ)^37*100000000000000^29 ≤ 5004625837243^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956287683 10000000000 5004625837243 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1319274617/10000000000 : ℝ)^37 ≤ (188629261923/2500000000000 : ℝ)^29 := by
    have hnat : (1319274617 : ℕ)^37*2500000000000^29 ≤ 188629261923^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319274617 10000000000 188629261923 2500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(450114583/500000000 : ℝ), (-956287683/10000000000 : ℝ), (-1319274617/10000000000 : ℝ)] ![(43725101836353/50000000000000 : ℝ), (5004625837243/100000000000000 : ℝ), (188629261923/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(450114583/500000000 : ℝ)|^37 ≤ (43725101836353/50000000000000 : ℝ)^29
        have hw : |(450114583/500000000 : ℝ)|=(450114583/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-956287683/10000000000 : ℝ)|^37 ≤ (5004625837243/100000000000000 : ℝ)^29
        have hw : |(-956287683/10000000000 : ℝ)|=(956287683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1319274617/10000000000 : ℝ)|^37 ≤ (188629261923/2500000000000 : ℝ)^29
        have hw : |(-1319274617/10000000000 : ℝ)|=(1319274617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-117064783/500000000 : ℝ)*x 0 + (-178066557/400000000 : ℝ)*x 1 + (-5690142113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117064783/500000000 : ℝ)^37 ≤ (7843017133601/50000000000000 : ℝ)^29 := by
    have hnat : (117064783 : ℕ)^37*50000000000000^29 ≤ 7843017133601^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117064783 500000000 7843017133601 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178066557/400000000 : ℝ)^37 ≤ (35609266179021/100000000000000 : ℝ)^29 := by
    have hnat : (178066557 : ℕ)^37*100000000000000^29 ≤ 35609266179021^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178066557 400000000 35609266179021 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5690142113/10000000000 : ℝ)^37 ≤ (4870469953999/10000000000000 : ℝ)^29 := by
    have hnat : (5690142113 : ℕ)^37*10000000000000^29 ≤ 4870469953999^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5690142113 10000000000 4870469953999 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117064783/500000000 : ℝ), (-178066557/400000000 : ℝ), (-5690142113/10000000000 : ℝ)] ![(7843017133601/50000000000000 : ℝ), (35609266179021/100000000000000 : ℝ), (4870469953999/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117064783/500000000 : ℝ)|^37 ≤ (7843017133601/50000000000000 : ℝ)^29
        have hw : |(-117064783/500000000 : ℝ)|=(117064783/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-178066557/400000000 : ℝ)|^37 ≤ (35609266179021/100000000000000 : ℝ)^29
        have hw : |(-178066557/400000000 : ℝ)|=(178066557/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5690142113/10000000000 : ℝ)|^37 ≤ (4870469953999/10000000000000 : ℝ)^29
        have hw : |(-5690142113/10000000000 : ℝ)|=(5690142113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2378951547/5000000000 : ℝ)*x 0 + (2173255037/5000000000 : ℝ)*x 1 + (-1775966803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2378951547/5000000000 : ℝ)^37 ≤ (7752767962807/20000000000000 : ℝ)^29 := by
    have hnat : (2378951547 : ℕ)^37*20000000000000^29 ≤ 7752767962807^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2378951547 5000000000 7752767962807 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173255037/5000000000 : ℝ)^37 ≤ (17269805130411/50000000000000 : ℝ)^29 := by
    have hnat : (2173255037 : ℕ)^37*50000000000000^29 ≤ 17269805130411^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173255037 5000000000 17269805130411 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1775966803/5000000000 : ℝ)^37 ≤ (13348274957837/50000000000000 : ℝ)^29 := by
    have hnat : (1775966803 : ℕ)^37*50000000000000^29 ≤ 13348274957837^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775966803 5000000000 13348274957837 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2378951547/5000000000 : ℝ), (2173255037/5000000000 : ℝ), (-1775966803/5000000000 : ℝ)] ![(7752767962807/20000000000000 : ℝ), (17269805130411/50000000000000 : ℝ), (13348274957837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2378951547/5000000000 : ℝ)|^37 ≤ (7752767962807/20000000000000 : ℝ)^29
        have hw : |(2378951547/5000000000 : ℝ)|=(2378951547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2173255037/5000000000 : ℝ)|^37 ≤ (17269805130411/50000000000000 : ℝ)^29
        have hw : |(2173255037/5000000000 : ℝ)|=(2173255037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1775966803/5000000000 : ℝ)|^37 ≤ (13348274957837/50000000000000 : ℝ)^29
        have hw : |(-1775966803/5000000000 : ℝ)|=(1775966803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (59539261/125000000 : ℝ)*x 0 + (-34747843/80000000 : ℝ)*x 1 + (22184111/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59539261/125000000 : ℝ)^37 ≤ (7763658732953/20000000000000 : ℝ)^29 := by
    have hnat : (59539261 : ℕ)^37*20000000000000^29 ≤ 7763658732953^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59539261 125000000 7763658732953 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34747843/80000000 : ℝ)^37 ≤ (17254448066467/50000000000000 : ℝ)^29 := by
    have hnat : (34747843 : ℕ)^37*50000000000000^29 ≤ 17254448066467^29*80000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34747843 80000000 17254448066467 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22184111/62500000 : ℝ)^37 ≤ (26672810179371/100000000000000 : ℝ)^29 := by
    have hnat : (22184111 : ℕ)^37*100000000000000^29 ≤ 26672810179371^29*62500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22184111 62500000 26672810179371 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(59539261/125000000 : ℝ), (-34747843/80000000 : ℝ), (22184111/62500000 : ℝ)] ![(7763658732953/20000000000000 : ℝ), (17254448066467/50000000000000 : ℝ), (26672810179371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(59539261/125000000 : ℝ)|^37 ≤ (7763658732953/20000000000000 : ℝ)^29
        have hw : |(59539261/125000000 : ℝ)|=(59539261/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34747843/80000000 : ℝ)|^37 ≤ (17254448066467/50000000000000 : ℝ)^29
        have hw : |(-34747843/80000000 : ℝ)|=(34747843/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22184111/62500000 : ℝ)|^37 ≤ (26672810179371/100000000000000 : ℝ)^29
        have hw : |(22184111/62500000 : ℝ)|=(22184111/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312038_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1470803551/2500000000 : ℝ)*x 0 + (-2917490011/10000000000 : ℝ)*x 1 + (-3729152303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1470803551/2500000000 : ℝ)^37 ≤ (3176435946633/6250000000000 : ℝ)^29 := by
    have hnat : (1470803551 : ℕ)^37*6250000000000^29 ≤ 3176435946633^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1470803551 2500000000 3176435946633 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2917490011/10000000000 : ℝ)^37 ≤ (415389728633/2000000000000 : ℝ)^29 := by
    have hnat : (2917490011 : ℕ)^37*2000000000000^29 ≤ 415389728633^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2917490011 10000000000 415389728633 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3729152303/10000000000 : ℝ)^37 ≤ (1775471150091/6250000000000 : ℝ)^29 := by
    have hnat : (3729152303 : ℕ)^37*6250000000000^29 ≤ 1775471150091^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3729152303 10000000000 1775471150091 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1470803551/2500000000 : ℝ), (-2917490011/10000000000 : ℝ), (-3729152303/10000000000 : ℝ)] ![(3176435946633/6250000000000 : ℝ), (415389728633/2000000000000 : ℝ), (1775471150091/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1470803551/2500000000 : ℝ)|^37 ≤ (3176435946633/6250000000000 : ℝ)^29
        have hw : |(1470803551/2500000000 : ℝ)|=(1470803551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2917490011/10000000000 : ℝ)|^37 ≤ (415389728633/2000000000000 : ℝ)^29
        have hw : |(-2917490011/10000000000 : ℝ)|=(2917490011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3729152303/10000000000 : ℝ)|^37 ≤ (1775471150091/6250000000000 : ℝ)^29
        have hw : |(-3729152303/10000000000 : ℝ)|=(3729152303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312038 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have s0_pow0 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-40036343/500000000 : ℝ)*X 0 0+(-2265835361/5000000000 : ℝ)*X 0 1+(-416503509/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5081617701/10000000000 : ℝ)*X 1 0+(274628249/625000000 : ℝ)*X 1 1+(-3140692289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5081617631/10000000000 : ℝ)*X 2 0+(-1098513007/2500000000 : ℝ)*X 2 1+(19629327/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-590524353/10000000000 : ℝ)*X 0 0+(-1031655791/2000000000 : ℝ)*X 0 1+(-1239664697/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4949780627/10000000000 : ℝ)*X 1 0+(2666229889/5000000000 : ℝ)*X 1 1+(-218919217/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2518536667/5000000000 : ℝ)*X 2 0+(-3345579317/10000000000 : ℝ)*X 2 1+(2125651943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1428816991/2000000000 : ℝ)*X 0 0+(-1029690967/10000000000 : ℝ)*X 0 1+(-95743841/250000000 : ℝ)*X 0 2+(1428816991/2000000000 : ℝ)*X 1 0+(-1029690967/10000000000 : ℝ)*X 1 1+(-95743841/250000000 : ℝ)*X 1 2+(1428816991/2000000000 : ℝ)*X 2 0+(-1029690967/10000000000 : ℝ)*X 2 1+(-95743841/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-3728463/2000000000 : ℝ)*X 0 0+(-4218126161/10000000000 : ℝ)*X 0 1+(-7282389969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2251591877/5000000000 : ℝ)*X 1 0+(927762479/2000000000 : ℝ)*X 1 1+(-3514058079/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((5930958581/10000000000 : ℝ)*X 2 0+(-3747878223/10000000000 : ℝ)*X 2 1+(1419572579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((4470635849/5000000000 : ℝ)*X 0 0+(-173655353/2000000000 : ℝ)*X 0 1+(-374759417/2500000000 : ℝ)*X 0 2+(4470635849/5000000000 : ℝ)*X 1 0+(-173655353/2000000000 : ℝ)*X 1 1+(-374759417/2500000000 : ℝ)*X 1 2+(4470635849/5000000000 : ℝ)*X 2 0+(-173655353/2000000000 : ℝ)*X 2 1+(-374759417/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-2845709/1250000000 : ℝ)*X 0 0+(-972630447/2000000000 : ℝ)*X 0 1+(-6709103773/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((5926835157/10000000000 : ℝ)*X 1 0+(2009175169/5000000000 : ℝ)*X 1 1+(-2545021557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4477086591/10000000000 : ℝ)*X 2 0+(-2493105289/5000000000 : ℝ)*X 2 1+(394751961/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((450114583/500000000 : ℝ)*X 0 0+(-956287683/10000000000 : ℝ)*X 0 1+(-1319274617/10000000000 : ℝ)*X 0 2+(450114583/500000000 : ℝ)*X 1 0+(-956287683/10000000000 : ℝ)*X 1 1+(-1319274617/10000000000 : ℝ)*X 1 2+(450114583/500000000 : ℝ)*X 2 0+(-956287683/10000000000 : ℝ)*X 2 1+(-1319274617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((14883/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14883/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2707019841196211716611/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (233507411141/200000000000 : ℝ)*(base39) + (10086610753/250000000000 : ℝ)*(base50) + (2179670787/6250000000 : ℝ)*(base59) + (824808638361/250000000000 : ℝ)*(major_s0_0) + (824808638361/250000000000 : ℝ)*(major_s0_1) + (824808638361/250000000000 : ℝ)*(major_s0_2) + (11747789/500000000000 : ℝ)*(sp_s0_2) + (1155457899011/250000000000 : ℝ)*(sp_s0_7) + (4621767729139/1000000000000 : ℝ)*(sp_s0_8) + (2310888933479/500000000000 : ℝ)*(sp_s0_9) + (1976619288757/1000000000000 : ℝ)*(sp_s0_13) + (9900187/125000000000 : ℝ)*(sp_s0_15) + (15334591/1000000000000 : ℝ)*(sp_s0_20) + (45568099/1000000000000 : ℝ)*(sp_s0_22) + (1976619288757/1000000000000 : ℝ)*(f.failure) + (924369386127/200000000000 : ℝ)*(f.sum) + (423134107656963/625000000000000000000000000 : ℝ)*base63 + (175011189280389/2500000000000000000000000000 : ℝ)*base64 + (426462913969611/2500000000000000000000000000 : ℝ)*base66 + (737862676844463/1250000000000000000000000000 : ℝ)*base69 + (297041190658537/2500000000000000000000000000 : ℝ)*base71 + (517341096780389/2500000000000000000000000000 : ℝ)*base72 + (1002636669094463/1250000000000000000000000000 : ℝ)*base75 + (350539050280537/1250000000000000000000000000 : ℝ)*base76 + (55126431/500000000000000000000 : ℝ)*base79 + (102859/100000000000000000 : ℝ)*base86 + (102859/100000000000000000 : ℝ)*base88 + (102859/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9109/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-9109/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (288461004696835318539/25000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18593/781250000 : ℝ)*(base12) + (993590146329/1000000000000 : ℝ)*(base39) + (194968520943/250000000000 : ℝ)*(base59) + (2490754530157/250000000000 : ℝ)*(major_s0_0) + (4999650276293/1000000000000 : ℝ)*(major_s0_1) + (4999650276293/1000000000000 : ℝ)*(major_s0_2) + (3701661/62500000000 : ℝ)*(sp_s0_0) + (3002383/100000000000 : ℝ)*(sp_s0_1) + (992673568867/200000000000 : ℝ)*(sp_s0_3) + (25553347/1000000000000 : ℝ)*(sp_s0_9) + (1400770132317/200000000000 : ℝ)*(sp_s0_14) + (7003903663371/1000000000000 : ℝ)*(sp_s0_15) + (3501954066927/500000000000 : ℝ)*(sp_s0_16) + (2995363019233/1000000000000 : ℝ)*(sp_s0_19) + (2995363019233/1000000000000 : ℝ)*(f.failure) + (7003933687201/1000000000000 : ℝ)*(f.sum) + (847062220168819/2500000000000000000000000000 : ℝ)*base63 + (1588606456332543/10000000000000000000000000000 : ℝ)*base65 + (717140298667457/10000000000000000000000000000 : ℝ)*base67 + (1094225370918819/5000000000000000000000000000 : ℝ)*base69 + (2491769999735209/10000000000000000000000000000 : ℝ)*base70 + (928762357213593/2500000000000000000000000000 : ℝ)*base72 + (847145116918819/5000000000000000000000000000 : ℝ)*base75 + (36071806008469/1250000000000000000000000000 : ℝ)*base76 + (1099891627237383/2000000000000000000000000000 : ℝ)*base78 + (62271/100000000000000000 : ℝ)*base86 + (62271/100000000000000000 : ℝ)*base88 + (62271/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-44847/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-44847/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9640480189531099297881/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (384139716621/250000000000 : ℝ)*(base39) + (745701034363/1000000000000 : ℝ)*(base59) + (722030157599/100000000000 : ℝ)*(major_s0_0) + (615482084843/125000000000 : ℝ)*(major_s0_1) + (615482084843/125000000000 : ℝ)*(major_s0_2) + (1148222448623/500000000000 : ℝ)*(sp_s0_3) + (4835913/250000000000 : ℝ)*(sp_s0_7) + (348413/125000000000 : ℝ)*(sp_s0_8) + (8381841/1000000000000 : ℝ)*(sp_s0_16) + (8417557/1000000000000 : ℝ)*(sp_s0_19) + (6897738753163/1000000000000 : ℝ)*(sp_s0_20) + (689775530951/100000000000 : ℝ)*(sp_s0_21) + (3448874857487/500000000000 : ℝ)*(sp_s0_22) + (1474972778857/500000000000 : ℝ)*(sp_s0_25) + (2949953975271/1000000000000 : ℝ)*(f.failure) + (3448879048407/500000000000 : ℝ)*(f.sum) + (16588246615969/312500000000000000000000000 : ℝ)*base63 + (362443859828593/1250000000000000000000000000 : ℝ)*base65 + (1023399460796407/1250000000000000000000000000 : ℝ)*base67 + (45644568196531/625000000000000000000000000 : ℝ)*base68 + (699037384591729/2500000000000000000000000000 : ℝ)*base70 + (631304397226349/1000000000000000000000000000 : ℝ)*base73 + (379746979259031/625000000000000000000000000 : ℝ)*base74 + (308951436100217/500000000000000000000000000 : ℝ)*base77 + (929800542817373/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (8423/100000000000000000 : ℝ)*base87 + (8423/100000000000000000 : ℝ)*base89 + (8423/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (14883/100000 : ℝ) ^ (9/2 : ℝ) ≤ (4732026592634163/25000000000000000000 : ℝ) := by
    have hpowers : (14883/100000 : ℝ)^9 ≤ (4732026592634163/25000000000000000000 : ℝ)^2 := by
      have hnat : (14883 : ℕ)^9*25000000000000000000^2 ≤ 4732026592634163^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14883 100000 4732026592634163 25000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14883/100000 : ℝ)) (X := (4732026592634163/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25004732026592634163/25000000000000000000 : ℝ) ≤ (5000210296813801/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (25004732026592634163/25000000000000000000 : ℝ)^2 ≤ (5000210296813801/5000000000000000 : ℝ)^9 := by
      have hnat : (25004732026592634163 : ℕ)^2*5000000000000000^9 ≤ 5000210296813801^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004732026592634163 25000000000000000000 5000210296813801 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000210296813801/5000000000000000 : ℝ)) (X := (25004732026592634163/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12504732026592634163/12500000000000000000 : ℝ) ≤ (10000841125352271/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (12504732026592634163/12500000000000000000 : ℝ)^2 ≤ (10000841125352271/10000000000000000 : ℝ)^9 := by
      have hnat : (12504732026592634163 : ℕ)^2*10000000000000000^9 ≤ 10000841125352271^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504732026592634163 12500000000000000000 10000841125352271 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000841125352271/10000000000000000 : ℝ)) (X := (12504732026592634163/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(210296813801/744150000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(420531724669/1488300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (14883/100000 : ℝ)) (alpha := (210296813801/744150000000000 : ℝ)) (beta := (420531724669/1488300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (14883/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(210296813801/744150000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(420531724669/1488300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (9109/20000 : ℝ) ^ (9/2 : ℝ) ≤ (2903910177662382971/100000000000000000000 : ℝ) := by
    have hpowers : (9109/20000 : ℝ)^9 ≤ (2903910177662382971/100000000000000000000 : ℝ)^2 := by
      have hnat : (9109 : ℕ)^9*100000000000000000000^2 ≤ 2903910177662382971^2*20000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9109 20000 2903910177662382971 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9109/20000 : ℝ)) (X := (2903910177662382971/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (102903910177662382971/100000000000000000000 : ℝ) ≤ (402552595162501/400000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (102903910177662382971/100000000000000000000 : ℝ)^2 ≤ (402552595162501/400000000000000 : ℝ)^9 := by
      have hnat : (102903910177662382971 : ℕ)^2*400000000000000^9 ≤ 402552595162501^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102903910177662382971 100000000000000000000 402552595162501 400000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (402552595162501/400000000000000 : ℝ)) (X := (102903910177662382971/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (52903910177662382971/50000000000000000000 : ℝ) ≤ (10126244117433619/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (52903910177662382971/50000000000000000000 : ℝ)^2 ≤ (10126244117433619/10000000000000000 : ℝ)^9 := by
      have hnat : (52903910177662382971 : ℕ)^2*10000000000000000^9 ≤ 10126244117433619^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52903910177662382971 50000000000000000000 10126244117433619 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10126244117433619/10000000000000000 : ℝ)) (X := (52903910177662382971/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(2552595162501/182180000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(31214619185547/2277250000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (9109/20000 : ℝ)) (alpha := (2552595162501/182180000000000 : ℝ)) (beta := (31214619185547/2277250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (9109/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(2552595162501/182180000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(31214619185547/2277250000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (44847/100000 : ℝ) ^ (9/2 : ℝ) ≤ (2708945605988997289/100000000000000000000 : ℝ) := by
    have hpowers : (44847/100000 : ℝ)^9 ≤ (2708945605988997289/100000000000000000000 : ℝ)^2 := by
      have hnat : (44847 : ℕ)^9*100000000000000000000^2 ≤ 2708945605988997289^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44847 100000 2708945605988997289 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44847/100000 : ℝ)) (X := (2708945605988997289/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (102708945605988997289/100000000000000000000 : ℝ) ≤ (2514893650638869/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (102708945605988997289/100000000000000000000 : ℝ)^2 ≤ (2514893650638869/2500000000000000 : ℝ)^9 := by
      have hnat : (102708945605988997289 : ℕ)^2*2500000000000000^9 ≤ 2514893650638869^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102708945605988997289 100000000000000000000 2514893650638869 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514893650638869/2500000000000000 : ℝ)) (X := (102708945605988997289/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (52708945605988997289/50000000000000000000 : ℝ) ≤ (2529484839131663/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (52708945605988997289/50000000000000000000 : ℝ)^2 ≤ (2529484839131663/2500000000000000 : ℝ)^9 := by
      have hnat : (52708945605988997289 : ℕ)^2*2500000000000000^9 ≤ 2529484839131663^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52708945605988997289 50000000000000000000 2529484839131663 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2529484839131663/2500000000000000 : ℝ)) (X := (52708945605988997289/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(14893650638869/1121175000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(270207194311/20762500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (44847/100000 : ℝ)) (alpha := (14893650638869/1121175000000000 : ℝ)) (beta := (270207194311/20762500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (44847/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(14893650638869/1121175000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(270207194311/20762500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-117064783/500000000 : ℝ)*X 0 0+(-178066557/400000000 : ℝ)*X 0 1+(-5690142113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2378951547/5000000000 : ℝ)*X 1 0+(2173255037/5000000000 : ℝ)*X 1 1+(-1775966803/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((59539261/125000000 : ℝ)*X 2 0+(-34747843/80000000 : ℝ)*X 2 1+(22184111/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1470803551/2500000000 : ℝ)*X 0 0+(-2917490011/10000000000 : ℝ)*X 0 1+(-3729152303/10000000000 : ℝ)*X 0 2+(1470803551/2500000000 : ℝ)*X 1 0+(-2917490011/10000000000 : ℝ)*X 1 1+(-3729152303/10000000000 : ℝ)*X 1 2+(1470803551/2500000000 : ℝ)*X 2 0+(-2917490011/10000000000 : ℝ)*X 2 1+(-3729152303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312038_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-350739/50000 : ℝ) < ((-166913/100000 : ℝ)*P 0+(-166913/100000 : ℝ)*P 1+(-166913/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-350739/50000 : ℝ) < (-2135518311970160129838832161465719/307064344455000000000000000000000 : ℝ) := by norm_num
    linear_combination (316211/1000000000000 : ℝ)*(base5) + (27841/200000000000 : ℝ)*(base8) + (718609/1000000000000 : ℝ)*(base10) + (842330259587/1000000000000 : ℝ)*(base39) + (46249946469/125000000000 : ℝ)*(base40) + (3293/10000000000 : ℝ)*(base50) + (323669592371/1000000000000 : ℝ)*(base59) + (116577/1000000000000 : ℝ)*(base60) + (166913/100000 : ℝ)*(major_s1_0) + (166913/100000 : ℝ)*(major_s1_1) + (166913/100000 : ℝ)*(major_s1_2) + (463641700361/200000000000 : ℝ)*(sp_s1_0) + (115910467981/50000000000 : ℝ)*(sp_s1_1) + (231820967583/100000000000 : ℝ)*(sp_s1_2) + (999999683789/1000000000000 : ℝ)*(sp_s1_6) + (115910467981/50000000000 : ℝ)*(f.sum) + (205474717553907257/255319576875000000000000000000 : ℝ)*base63 + (1198820432441/1038125000000000000000000 : ℝ)*base64 + (4125753843/5693125000000000000000000 : ℝ)*base67 + (30807018218777/112117500000000000000000000 : ℝ)*base69 + (24104241796153933/22473330000000000000000000000 : ℝ)*base70 + (12756878627921/148830000000000000000000000 : ℝ)*base73 + (18264461359049/22772500000000000000000000 : ℝ)*base75 + (87215962312693/148830000000000000000000000 : ℝ)*base76 + (634590244044013949/1355692470000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p012_b019 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 38 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=38 := by omega
  rcases hc with rfl
  · exact collision_c312038 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 38 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b019 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
