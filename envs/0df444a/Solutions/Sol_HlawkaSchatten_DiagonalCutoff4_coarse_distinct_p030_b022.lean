-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b022
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:32:40.293895+00:00
-- url     : https://prove2.me/submissions/82ee02c9-9d95-4459-bd9a-0b26835653e9

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
theorem collision_support_c330051_s0_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-3171915037/10000000000 : ℝ)*x 0 + (63438299/200000000 : ℝ)*x 1 + (5572855081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3171915037/10000000000 : ℝ)^6 ≤ (25210755174877/100000000000000 : ℝ)^5 := by
    have hnat : (3171915037 : ℕ)^6*100000000000000^5 ≤ 25210755174877^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3171915037 10000000000 25210755174877 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63438299/200000000 : ℝ)^6 ≤ (12605377172547/50000000000000 : ℝ)^5 := by
    have hnat : (63438299 : ℕ)^6*50000000000000^5 ≤ 12605377172547^5*200000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63438299 200000000 12605377172547 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5572855081/10000000000 : ℝ)^6 ≤ (49578490468929/100000000000000 : ℝ)^5 := by
    have hnat : (5572855081 : ℕ)^6*100000000000000^5 ≤ 49578490468929^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5572855081 10000000000 49578490468929 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3171915037/10000000000 : ℝ), (63438299/200000000 : ℝ), (5572855081/10000000000 : ℝ)] ![(25210755174877/100000000000000 : ℝ), (12605377172547/50000000000000 : ℝ), (49578490468929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3171915037/10000000000 : ℝ)|^6 ≤ (25210755174877/100000000000000 : ℝ)^5
        have hw : |(-3171915037/10000000000 : ℝ)|=(3171915037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63438299/200000000 : ℝ)|^6 ≤ (12605377172547/50000000000000 : ℝ)^5
        have hw : |(63438299/200000000 : ℝ)|=(63438299/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5572855081/10000000000 : ℝ)|^6 ≤ (49578490468929/100000000000000 : ℝ)^5
        have hw : |(5572855081/10000000000 : ℝ)|=(5572855081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (47714919/200000000 : ℝ)*x 0 + (-1192872939/5000000000 : ℝ)*x 1 + (6909949971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47714919/200000000 : ℝ)^6 ≤ (8956102156123/50000000000000 : ℝ)^5 := by
    have hnat : (47714919 : ℕ)^6*50000000000000^5 ≤ 8956102156123^5*200000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47714919 200000000 8956102156123 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1192872939/5000000000 : ℝ)^6 ≤ (8956101831777/50000000000000 : ℝ)^5 := by
    have hnat : (1192872939 : ℕ)^6*50000000000000^5 ≤ 8956101831777^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192872939 5000000000 8956101831777 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6909949971/10000000000 : ℝ)^6 ≤ (32087796003351/50000000000000 : ℝ)^5 := by
    have hnat : (6909949971 : ℕ)^6*50000000000000^5 ≤ 32087796003351^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6909949971 10000000000 32087796003351 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(47714919/200000000 : ℝ), (-1192872939/5000000000 : ℝ), (6909949971/10000000000 : ℝ)] ![(8956102156123/50000000000000 : ℝ), (8956101831777/50000000000000 : ℝ), (32087796003351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(47714919/200000000 : ℝ)|^6 ≤ (8956102156123/50000000000000 : ℝ)^5
        have hw : |(47714919/200000000 : ℝ)|=(47714919/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1192872939/5000000000 : ℝ)|^6 ≤ (8956101831777/50000000000000 : ℝ)^5
        have hw : |(-1192872939/5000000000 : ℝ)|=(1192872939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6909949971/10000000000 : ℝ)|^6 ≤ (32087796003351/50000000000000 : ℝ)^5
        have hw : |(6909949971/10000000000 : ℝ)|=(6909949971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2915045713/5000000000 : ℝ)*x 0 + (2663498367/5000000000 : ℝ)*x 1 + (-79767227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2915045713/5000000000 : ℝ)^6 ≤ (13084298610043/25000000000000 : ℝ)^5 := by
    have hnat : (2915045713 : ℕ)^6*25000000000000^5 ≤ 13084298610043^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2915045713 5000000000 13084298610043 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2663498367/5000000000 : ℝ)^6 ≤ (11741374090953/25000000000000 : ℝ)^5 := by
    have hnat : (2663498367 : ℕ)^6*25000000000000^5 ≤ 11741374090953^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663498367 5000000000 11741374090953 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79767227/5000000000 : ℝ)^6 ≤ (697309189147/100000000000000 : ℝ)^5 := by
    have hnat : (79767227 : ℕ)^6*100000000000000^5 ≤ 697309189147^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79767227 5000000000 697309189147 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2915045713/5000000000 : ℝ), (2663498367/5000000000 : ℝ), (-79767227/5000000000 : ℝ)] ![(13084298610043/25000000000000 : ℝ), (11741374090953/25000000000000 : ℝ), (697309189147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2915045713/5000000000 : ℝ)|^6 ≤ (13084298610043/25000000000000 : ℝ)^5
        have hw : |(2915045713/5000000000 : ℝ)|=(2915045713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2663498367/5000000000 : ℝ)|^6 ≤ (11741374090953/25000000000000 : ℝ)^5
        have hw : |(2663498367/5000000000 : ℝ)|=(2663498367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79767227/5000000000 : ℝ)|^6 ≤ (697309189147/100000000000000 : ℝ)^5
        have hw : |(-79767227/5000000000 : ℝ)|=(79767227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_7 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-2895525589/10000000000 : ℝ)*x 0 + (922547073/5000000000 : ℝ)*x 1 + (1728996517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2895525589/10000000000 : ℝ)^6 ≤ (22598150091659/100000000000000 : ℝ)^5 := by
    have hnat : (2895525589 : ℕ)^6*100000000000000^5 ≤ 22598150091659^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2895525589 10000000000 22598150091659 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922547073/5000000000 : ℝ)^6 ≤ (13158980311871/100000000000000 : ℝ)^5 := by
    have hnat : (922547073 : ℕ)^6*100000000000000^5 ≤ 13158980311871^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922547073 5000000000 13158980311871 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1728996517/2500000000 : ℝ)^6 ≤ (32121434793531/50000000000000 : ℝ)^5 := by
    have hnat : (1728996517 : ℕ)^6*50000000000000^5 ≤ 32121434793531^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728996517 2500000000 32121434793531 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2895525589/10000000000 : ℝ), (922547073/5000000000 : ℝ), (1728996517/2500000000 : ℝ)] ![(22598150091659/100000000000000 : ℝ), (13158980311871/100000000000000 : ℝ), (32121434793531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2895525589/10000000000 : ℝ)|^6 ≤ (22598150091659/100000000000000 : ℝ)^5
        have hw : |(-2895525589/10000000000 : ℝ)|=(2895525589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922547073/5000000000 : ℝ)|^6 ≤ (13158980311871/100000000000000 : ℝ)^5
        have hw : |(922547073/5000000000 : ℝ)|=(922547073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1728996517/2500000000 : ℝ)|^6 ≤ (32121434793531/50000000000000 : ℝ)^5
        have hw : |(1728996517/2500000000 : ℝ)|=(1728996517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_8 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1772461841/10000000000 : ℝ)*x 0 + (-1053816189/10000000000 : ℝ)*x 1 + (104589531/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1772461841/10000000000 : ℝ)^6 ≤ (250796960373/2000000000000 : ℝ)^5 := by
    have hnat : (1772461841 : ℕ)^6*2000000000000^5 ≤ 250796960373^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772461841 10000000000 250796960373 2000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053816189/10000000000 : ℝ)^6 ≤ (3359602096301/50000000000000 : ℝ)^5 := by
    have hnat : (1053816189 : ℕ)^6*50000000000000^5 ≤ 3359602096301^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053816189 10000000000 3359602096301 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104589531/125000000 : ℝ)^6 ≤ (20185236942939/25000000000000 : ℝ)^5 := by
    have hnat : (104589531 : ℕ)^6*25000000000000^5 ≤ 20185236942939^5*125000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104589531 125000000 20185236942939 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1772461841/10000000000 : ℝ), (-1053816189/10000000000 : ℝ), (104589531/125000000 : ℝ)] ![(250796960373/2000000000000 : ℝ), (3359602096301/50000000000000 : ℝ), (20185236942939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1772461841/10000000000 : ℝ)|^6 ≤ (250796960373/2000000000000 : ℝ)^5
        have hw : |(1772461841/10000000000 : ℝ)|=(1772461841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1053816189/10000000000 : ℝ)|^6 ≤ (3359602096301/50000000000000 : ℝ)^5
        have hw : |(-1053816189/10000000000 : ℝ)|=(1053816189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104589531/125000000 : ℝ)|^6 ≤ (20185236942939/25000000000000 : ℝ)^5
        have hw : |(104589531/125000000 : ℝ)|=(104589531/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_9 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2176723721/5000000000 : ℝ)*x 0 + (3378209271/5000000000 : ℝ)*x 1 + (-153904993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176723721/5000000000 : ℝ)^6 ≤ (4607973574467/12500000000000 : ℝ)^5 := by
    have hnat : (2176723721 : ℕ)^6*12500000000000^5 ≤ 4607973574467^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176723721 5000000000 4607973574467 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3378209271/5000000000 : ℝ)^6 ≤ (62468323996561/100000000000000 : ℝ)^5 := by
    have hnat : (3378209271 : ℕ)^6*100000000000000^5 ≤ 62468323996561^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3378209271 5000000000 62468323996561 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153904993/10000000000 : ℝ)^6 ≤ (667887401537/100000000000000 : ℝ)^5 := by
    have hnat : (153904993 : ℕ)^6*100000000000000^5 ≤ 667887401537^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153904993 10000000000 667887401537 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176723721/5000000000 : ℝ), (3378209271/5000000000 : ℝ), (-153904993/10000000000 : ℝ)] ![(4607973574467/12500000000000 : ℝ), (62468323996561/100000000000000 : ℝ), (667887401537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176723721/5000000000 : ℝ)|^6 ≤ (4607973574467/12500000000000 : ℝ)^5
        have hw : |(2176723721/5000000000 : ℝ)|=(2176723721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3378209271/5000000000 : ℝ)|^6 ≤ (62468323996561/100000000000000 : ℝ)^5
        have hw : |(3378209271/5000000000 : ℝ)|=(3378209271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153904993/10000000000 : ℝ)|^6 ≤ (667887401537/100000000000000 : ℝ)^5
        have hw : |(-153904993/10000000000 : ℝ)|=(153904993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_13 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (3015210701/10000000000 : ℝ)*x 0 + (7927194231/10000000000 : ℝ)*x 1 + (141328143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3015210701/10000000000 : ℝ)^6 ≤ (5930908276597/25000000000000 : ℝ)^5 := by
    have hnat : (3015210701 : ℕ)^6*25000000000000^5 ≤ 5930908276597^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015210701 10000000000 5930908276597 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7927194231/10000000000 : ℝ)^6 ≤ (1182397288809/1562500000000 : ℝ)^5 := by
    have hnat : (7927194231 : ℕ)^6*1562500000000^5 ≤ 1182397288809^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7927194231 10000000000 1182397288809 1562500000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141328143/10000000000 : ℝ)^6 ≤ (120588079529/20000000000000 : ℝ)^5 := by
    have hnat : (141328143 : ℕ)^6*20000000000000^5 ≤ 120588079529^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141328143 10000000000 120588079529 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3015210701/10000000000 : ℝ), (7927194231/10000000000 : ℝ), (141328143/10000000000 : ℝ)] ![(5930908276597/25000000000000 : ℝ), (1182397288809/1562500000000 : ℝ), (120588079529/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3015210701/10000000000 : ℝ)|^6 ≤ (5930908276597/25000000000000 : ℝ)^5
        have hw : |(3015210701/10000000000 : ℝ)|=(3015210701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7927194231/10000000000 : ℝ)|^6 ≤ (1182397288809/1562500000000 : ℝ)^5
        have hw : |(7927194231/10000000000 : ℝ)|=(7927194231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141328143/10000000000 : ℝ)|^6 ≤ (120588079529/20000000000000 : ℝ)^5
        have hw : |(141328143/10000000000 : ℝ)|=(141328143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_14 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-241357773/1250000000 : ℝ)*x 0 + (358235799/1250000000 : ℝ)*x 1 + (3437342711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (241357773/1250000000 : ℝ)^6 ≤ (6948187613863/50000000000000 : ℝ)^5 := by
    have hnat : (241357773 : ℕ)^6*50000000000000^5 ≤ 6948187613863^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241357773 1250000000 6948187613863 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (358235799/1250000000 : ℝ)^6 ≤ (22320851821713/100000000000000 : ℝ)^5 := by
    have hnat : (358235799 : ℕ)^6*100000000000000^5 ≤ 22320851821713^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358235799 1250000000 22320851821713 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3437342711/5000000000 : ℝ)^6 ≤ (1993211654309/3125000000000 : ℝ)^5 := by
    have hnat : (3437342711 : ℕ)^6*3125000000000^5 ≤ 1993211654309^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3437342711 5000000000 1993211654309 3125000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-241357773/1250000000 : ℝ), (358235799/1250000000 : ℝ), (3437342711/5000000000 : ℝ)] ![(6948187613863/50000000000000 : ℝ), (22320851821713/100000000000000 : ℝ), (1993211654309/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-241357773/1250000000 : ℝ)|^6 ≤ (6948187613863/50000000000000 : ℝ)^5
        have hw : |(-241357773/1250000000 : ℝ)|=(241357773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(358235799/1250000000 : ℝ)|^6 ≤ (22320851821713/100000000000000 : ℝ)^5
        have hw : |(358235799/1250000000 : ℝ)|=(358235799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3437342711/5000000000 : ℝ)|^6 ≤ (1993211654309/3125000000000 : ℝ)^5
        have hw : |(3437342711/5000000000 : ℝ)|=(3437342711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_15 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1299309257/10000000000 : ℝ)*x 0 + (-483211339/2500000000 : ℝ)*x 1 + (8081778303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299309257/10000000000 : ℝ)^6 ≤ (4319416107497/50000000000000 : ℝ)^5 := by
    have hnat : (1299309257 : ℕ)^6*50000000000000^5 ≤ 4319416107497^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299309257 10000000000 4319416107497 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (483211339/2500000000 : ℝ)^6 ≤ (13913504403857/100000000000000 : ℝ)^5 := by
    have hnat : (483211339 : ℕ)^6*100000000000000^5 ≤ 13913504403857^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483211339 2500000000 13913504403857 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8081778303/10000000000 : ℝ)^6 ≤ (77447663362491/100000000000000 : ℝ)^5 := by
    have hnat : (8081778303 : ℕ)^6*100000000000000^5 ≤ 77447663362491^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8081778303 10000000000 77447663362491 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299309257/10000000000 : ℝ), (-483211339/2500000000 : ℝ), (8081778303/10000000000 : ℝ)] ![(4319416107497/50000000000000 : ℝ), (13913504403857/100000000000000 : ℝ), (77447663362491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299309257/10000000000 : ℝ)|^6 ≤ (4319416107497/50000000000000 : ℝ)^5
        have hw : |(1299309257/10000000000 : ℝ)|=(1299309257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-483211339/2500000000 : ℝ)|^6 ≤ (13913504403857/100000000000000 : ℝ)^5
        have hw : |(-483211339/2500000000 : ℝ)|=(483211339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8081778303/10000000000 : ℝ)|^6 ≤ (77447663362491/100000000000000 : ℝ)^5
        have hw : |(8081778303/10000000000 : ℝ)|=(8081778303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_16 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (7134519653/10000000000 : ℝ)*x 0 + (1981465959/5000000000 : ℝ)*x 1 + (-19297987/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7134519653/10000000000 : ℝ)^6 ≤ (66686463455329/100000000000000 : ℝ)^5 := by
    have hnat : (7134519653 : ℕ)^6*100000000000000^5 ≤ 66686463455329^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7134519653 10000000000 66686463455329 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1981465959/5000000000 : ℝ)^6 ≤ (32932138530083/100000000000000 : ℝ)^5 := by
    have hnat : (1981465959 : ℕ)^6*100000000000000^5 ≤ 32932138530083^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981465959 5000000000 32932138530083 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19297987/2000000000 : ℝ)^6 ≤ (190699002317/50000000000000 : ℝ)^5 := by
    have hnat : (19297987 : ℕ)^6*50000000000000^5 ≤ 190699002317^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19297987 2000000000 190699002317 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7134519653/10000000000 : ℝ), (1981465959/5000000000 : ℝ), (-19297987/2000000000 : ℝ)] ![(66686463455329/100000000000000 : ℝ), (32932138530083/100000000000000 : ℝ), (190699002317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7134519653/10000000000 : ℝ)|^6 ≤ (66686463455329/100000000000000 : ℝ)^5
        have hw : |(7134519653/10000000000 : ℝ)|=(7134519653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1981465959/5000000000 : ℝ)|^6 ≤ (32932138530083/100000000000000 : ℝ)^5
        have hw : |(1981465959/5000000000 : ℝ)|=(1981465959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19297987/2000000000 : ℝ)|^6 ≤ (190699002317/50000000000000 : ℝ)^5
        have hw : |(-19297987/2000000000 : ℝ)|=(19297987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_20 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (7065858971/10000000000 : ℝ)*x 0 + (4006182863/10000000000 : ℝ)*x 1 + (81830779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7065858971/10000000000 : ℝ)^6 ≤ (32958539795549/50000000000000 : ℝ)^5 := by
    have hnat : (7065858971 : ℕ)^6*50000000000000^5 ≤ 32958539795549^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7065858971 10000000000 32958539795549 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4006182863/10000000000 : ℝ)^6 ≤ (33363908589203/100000000000000 : ℝ)^5 := by
    have hnat : (4006182863 : ℕ)^6*100000000000000^5 ≤ 33363908589203^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006182863 10000000000 33363908589203 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81830779/5000000000 : ℝ)^6 ≤ (719011799337/100000000000000 : ℝ)^5 := by
    have hnat : (81830779 : ℕ)^6*100000000000000^5 ≤ 719011799337^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81830779 5000000000 719011799337 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7065858971/10000000000 : ℝ), (4006182863/10000000000 : ℝ), (81830779/5000000000 : ℝ)] ![(32958539795549/50000000000000 : ℝ), (33363908589203/100000000000000 : ℝ), (719011799337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7065858971/10000000000 : ℝ)|^6 ≤ (32958539795549/50000000000000 : ℝ)^5
        have hw : |(7065858971/10000000000 : ℝ)|=(7065858971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4006182863/10000000000 : ℝ)|^6 ≤ (33363908589203/100000000000000 : ℝ)^5
        have hw : |(4006182863/10000000000 : ℝ)|=(4006182863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81830779/5000000000 : ℝ)|^6 ≤ (719011799337/100000000000000 : ℝ)^5
        have hw : |(81830779/5000000000 : ℝ)|=(81830779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_21 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-4313573707/10000000000 : ℝ)*x 0 + (856649067/2000000000 : ℝ)*x 1 + (169937351/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313573707/10000000000 : ℝ)^6 ≤ (3645899289501/10000000000000 : ℝ)^5 := by
    have hnat : (4313573707 : ℕ)^6*10000000000000^5 ≤ 3645899289501^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313573707 10000000000 3645899289501 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (856649067/2000000000 : ℝ)^6 ≤ (18075800731477/50000000000000 : ℝ)^5 := by
    have hnat : (856649067 : ℕ)^6*50000000000000^5 ≤ 18075800731477^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856649067 2000000000 18075800731477 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169937351/500000000 : ℝ)^6 ≤ (27389405624981/100000000000000 : ℝ)^5 := by
    have hnat : (169937351 : ℕ)^6*100000000000000^5 ≤ 27389405624981^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169937351 500000000 27389405624981 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4313573707/10000000000 : ℝ), (856649067/2000000000 : ℝ), (169937351/500000000 : ℝ)] ![(3645899289501/10000000000000 : ℝ), (18075800731477/50000000000000 : ℝ), (27389405624981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4313573707/10000000000 : ℝ)|^6 ≤ (3645899289501/10000000000000 : ℝ)^5
        have hw : |(-4313573707/10000000000 : ℝ)|=(4313573707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(856649067/2000000000 : ℝ)|^6 ≤ (18075800731477/50000000000000 : ℝ)^5
        have hw : |(856649067/2000000000 : ℝ)|=(856649067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169937351/500000000 : ℝ)|^6 ≤ (27389405624981/100000000000000 : ℝ)^5
        have hw : |(169937351/500000000 : ℝ)|=(169937351/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_22 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (714494171/5000000000 : ℝ)*x 0 + (-182414397/1250000000 : ℝ)*x 1 + (2084119803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (714494171/5000000000 : ℝ)^6 ≤ (9683546065719/100000000000000 : ℝ)^5 := by
    have hnat : (714494171 : ℕ)^6*100000000000000^5 ≤ 9683546065719^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714494171 5000000000 9683546065719 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182414397/1250000000 : ℝ)^6 ≤ (9930678422017/100000000000000 : ℝ)^5 := by
    have hnat : (182414397 : ℕ)^6*100000000000000^5 ≤ 9930678422017^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182414397 1250000000 9930678422017 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084119803/2500000000 : ℝ)^6 ≤ (16077155099807/20000000000000 : ℝ)^5 := by
    have hnat : (2084119803 : ℕ)^6*20000000000000^5 ≤ 16077155099807^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084119803 2500000000 16077155099807 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(714494171/5000000000 : ℝ), (-182414397/1250000000 : ℝ), (2084119803/2500000000 : ℝ)] ![(9683546065719/100000000000000 : ℝ), (9930678422017/100000000000000 : ℝ), (16077155099807/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(714494171/5000000000 : ℝ)|^6 ≤ (9683546065719/100000000000000 : ℝ)^5
        have hw : |(714494171/5000000000 : ℝ)|=(714494171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182414397/1250000000 : ℝ)|^6 ≤ (9930678422017/100000000000000 : ℝ)^5
        have hw : |(-182414397/1250000000 : ℝ)|=(182414397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084119803/2500000000 : ℝ)|^6 ≤ (16077155099807/20000000000000 : ℝ)^5
        have hw : |(2084119803/2500000000 : ℝ)|=(2084119803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_23 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (6567287911/10000000000 : ℝ)*x 0 + (4574262769/10000000000 : ℝ)*x 1 + (-121993977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6567287911/10000000000 : ℝ)^6 ≤ (60375851319279/100000000000000 : ℝ)^5 := by
    have hnat : (6567287911 : ℕ)^6*100000000000000^5 ≤ 60375851319279^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6567287911 10000000000 60375851319279 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4574262769/10000000000 : ℝ)^6 ≤ (39118782606657/100000000000000 : ℝ)^5 := by
    have hnat : (4574262769 : ℕ)^6*100000000000000^5 ≤ 39118782606657^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574262769 10000000000 39118782606657 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121993977/10000000000 : ℝ)^6 ≤ (25268302753/5000000000000 : ℝ)^5 := by
    have hnat : (121993977 : ℕ)^6*5000000000000^5 ≤ 25268302753^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121993977 10000000000 25268302753 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6567287911/10000000000 : ℝ), (4574262769/10000000000 : ℝ), (-121993977/10000000000 : ℝ)] ![(60375851319279/100000000000000 : ℝ), (39118782606657/100000000000000 : ℝ), (25268302753/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6567287911/10000000000 : ℝ)|^6 ≤ (60375851319279/100000000000000 : ℝ)^5
        have hw : |(6567287911/10000000000 : ℝ)|=(6567287911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4574262769/10000000000 : ℝ)|^6 ≤ (39118782606657/100000000000000 : ℝ)^5
        have hw : |(4574262769/10000000000 : ℝ)|=(4574262769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121993977/10000000000 : ℝ)|^6 ≤ (25268302753/5000000000000 : ℝ)^5
        have hw : |(-121993977/10000000000 : ℝ)|=(121993977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s0_27 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (602652223/2500000000 : ℝ)*x 0 + (210695299/250000000 : ℝ)*x 1 + (2613013/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (602652223/2500000000 : ℝ)^6 ≤ (18136442571647/100000000000000 : ℝ)^5 := by
    have hnat : (602652223 : ℕ)^6*100000000000000^5 ≤ 18136442571647^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602652223 2500000000 18136442571647 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210695299/250000000 : ℝ)^6 ≤ (10180469744673/12500000000000 : ℝ)^5 := by
    have hnat : (210695299 : ℕ)^6*12500000000000^5 ≤ 10180469744673^5*250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210695299 250000000 10180469744673 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613013/250000000 : ℝ)^6 ≤ (419799458513/100000000000000 : ℝ)^5 := by
    have hnat : (2613013 : ℕ)^6*100000000000000^5 ≤ 419799458513^5*250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613013 250000000 419799458513 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(602652223/2500000000 : ℝ), (210695299/250000000 : ℝ), (2613013/250000000 : ℝ)] ![(18136442571647/100000000000000 : ℝ), (10180469744673/12500000000000 : ℝ), (419799458513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(602652223/2500000000 : ℝ)|^6 ≤ (18136442571647/100000000000000 : ℝ)^5
        have hw : |(602652223/2500000000 : ℝ)|=(602652223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210695299/250000000 : ℝ)|^6 ≤ (10180469744673/12500000000000 : ℝ)^5
        have hw : |(210695299/250000000 : ℝ)|=(210695299/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613013/250000000 : ℝ)|^6 ≤ (419799458513/100000000000000 : ℝ)^5
        have hw : |(2613013/250000000 : ℝ)|=(2613013/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s1_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-699821841/2000000000 : ℝ)*x 0 + (437148283/1250000000 : ℝ)*x 1 + (4977550937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (699821841/2000000000 : ℝ)^6 ≤ (709069826201/2500000000000 : ℝ)^5 := by
    have hnat : (699821841 : ℕ)^6*2500000000000^5 ≤ 709069826201^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699821841 2000000000 709069826201 2500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437148283/1250000000 : ℝ)^6 ≤ (28344089894727/100000000000000 : ℝ)^5 := by
    have hnat : (437148283 : ℕ)^6*100000000000000^5 ≤ 28344089894727^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437148283 1250000000 28344089894727 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4977550937/10000000000 : ℝ)^6 ≤ (346344936411/800000000000 : ℝ)^5 := by
    have hnat : (4977550937 : ℕ)^6*800000000000^5 ≤ 346344936411^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4977550937 10000000000 346344936411 800000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-699821841/2000000000 : ℝ), (437148283/1250000000 : ℝ), (4977550937/10000000000 : ℝ)] ![(709069826201/2500000000000 : ℝ), (28344089894727/100000000000000 : ℝ), (346344936411/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-699821841/2000000000 : ℝ)|^6 ≤ (709069826201/2500000000000 : ℝ)^5
        have hw : |(-699821841/2000000000 : ℝ)|=(699821841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(437148283/1250000000 : ℝ)|^6 ≤ (28344089894727/100000000000000 : ℝ)^5
        have hw : |(437148283/1250000000 : ℝ)|=(437148283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4977550937/10000000000 : ℝ)|^6 ≤ (346344936411/800000000000 : ℝ)^5
        have hw : |(4977550937/10000000000 : ℝ)|=(4977550937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s1_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (735726683/2500000000 : ℝ)*x 0 + (-2941289453/10000000000 : ℝ)*x 1 + (1494393943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (735726683/2500000000 : ℝ)^6 ≤ (23042616831371/100000000000000 : ℝ)^5 := by
    have hnat : (735726683 : ℕ)^6*100000000000000^5 ≤ 23042616831371^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735726683 2500000000 23042616831371 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2941289453/10000000000 : ℝ)^6 ≤ (23027421939209/100000000000000 : ℝ)^5 := by
    have hnat : (2941289453 : ℕ)^6*100000000000000^5 ≤ 23027421939209^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2941289453 10000000000 23027421939209 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1494393943/2500000000 : ℝ)^6 ≤ (2696498060713/5000000000000 : ℝ)^5 := by
    have hnat : (1494393943 : ℕ)^6*5000000000000^5 ≤ 2696498060713^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1494393943 2500000000 2696498060713 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(735726683/2500000000 : ℝ), (-2941289453/10000000000 : ℝ), (1494393943/2500000000 : ℝ)] ![(23042616831371/100000000000000 : ℝ), (23027421939209/100000000000000 : ℝ), (2696498060713/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(735726683/2500000000 : ℝ)|^6 ≤ (23042616831371/100000000000000 : ℝ)^5
        have hw : |(735726683/2500000000 : ℝ)|=(735726683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2941289453/10000000000 : ℝ)|^6 ≤ (23027421939209/100000000000000 : ℝ)^5
        have hw : |(-2941289453/10000000000 : ℝ)|=(2941289453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1494393943/2500000000 : ℝ)|^6 ≤ (2696498060713/5000000000000 : ℝ)^5
        have hw : |(1494393943/2500000000 : ℝ)|=(1494393943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s1_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2570681659/5000000000 : ℝ)*x 0 + (5144143403/10000000000 : ℝ)*x 1 + (-1462160137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2570681659/5000000000 : ℝ)^6 ≤ (45008439287573/100000000000000 : ℝ)^5 := by
    have hnat : (2570681659 : ℕ)^6*100000000000000^5 ≤ 45008439287573^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570681659 5000000000 45008439287573 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5144143403/10000000000 : ℝ)^6 ≤ (45037645716503/100000000000000 : ℝ)^5 := by
    have hnat : (5144143403 : ℕ)^6*100000000000000^5 ≤ 45037645716503^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144143403 10000000000 45037645716503 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1462160137/10000000000 : ℝ)^6 ≤ (622119686921/6250000000000 : ℝ)^5 := by
    have hnat : (1462160137 : ℕ)^6*6250000000000^5 ≤ 622119686921^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1462160137 10000000000 622119686921 6250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2570681659/5000000000 : ℝ), (5144143403/10000000000 : ℝ), (-1462160137/10000000000 : ℝ)] ![(45008439287573/100000000000000 : ℝ), (45037645716503/100000000000000 : ℝ), (622119686921/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2570681659/5000000000 : ℝ)|^6 ≤ (45008439287573/100000000000000 : ℝ)^5
        have hw : |(2570681659/5000000000 : ℝ)|=(2570681659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5144143403/10000000000 : ℝ)|^6 ≤ (45037645716503/100000000000000 : ℝ)^5
        have hw : |(5144143403/10000000000 : ℝ)|=(5144143403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1462160137/10000000000 : ℝ)|^6 ≤ (622119686921/6250000000000 : ℝ)^5
        have hw : |(-1462160137/10000000000 : ℝ)|=(1462160137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330051_s1_6 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4924462999/10000000000 : ℝ)*x 0 + (24635629/50000000 : ℝ)*x 1 + (499926211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4924462999/10000000000 : ℝ)^6 ≤ (42739619788193/100000000000000 : ℝ)^5 := by
    have hnat : (4924462999 : ℕ)^6*100000000000000^5 ≤ 42739619788193^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4924462999 10000000000 42739619788193 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24635629/50000000 : ℝ)^6 ≤ (4276735396071/10000000000000 : ℝ)^5 := by
    have hnat : (24635629 : ℕ)^6*10000000000000^5 ≤ 4276735396071^5*50000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24635629 50000000 4276735396071 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499926211/2500000000 : ℝ)^6 ≤ (14493026234643/100000000000000 : ℝ)^5 := by
    have hnat : (499926211 : ℕ)^6*100000000000000^5 ≤ 14493026234643^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499926211 2500000000 14493026234643 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4924462999/10000000000 : ℝ), (24635629/50000000 : ℝ), (499926211/2500000000 : ℝ)] ![(42739619788193/100000000000000 : ℝ), (4276735396071/10000000000000 : ℝ), (14493026234643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4924462999/10000000000 : ℝ)|^6 ≤ (42739619788193/100000000000000 : ℝ)^5
        have hw : |(4924462999/10000000000 : ℝ)|=(4924462999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(24635629/50000000 : ℝ)|^6 ≤ (4276735396071/10000000000000 : ℝ)^5
        have hw : |(24635629/50000000 : ℝ)|=(24635629/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(499926211/2500000000 : ℝ)|^6 ≤ (14493026234643/100000000000000 : ℝ)^5
        have hw : |(499926211/2500000000 : ℝ)|=(499926211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c330051 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (41553/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (41553/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (41553/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (41553/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (31839/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1238278459541601/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1238278459541601/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3171915037/10000000000 : ℝ)*X 0 0+(63438299/200000000 : ℝ)*X 0 1+(5572855081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((47714919/200000000 : ℝ)*X 1 0+(-1192872939/5000000000 : ℝ)*X 1 1+(6909949971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2915045713/5000000000 : ℝ)*X 2 0+(2663498367/5000000000 : ℝ)*X 2 1+(-79767227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2895525589/10000000000 : ℝ)*X 0 0+(922547073/5000000000 : ℝ)*X 0 1+(1728996517/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1772461841/10000000000 : ℝ)*X 1 0+(-1053816189/10000000000 : ℝ)*X 1 1+(104589531/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2176723721/5000000000 : ℝ)*X 2 0+(3378209271/5000000000 : ℝ)*X 2 1+(-153904993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3015210701/10000000000 : ℝ)*X 0 0+(7927194231/10000000000 : ℝ)*X 0 1+(141328143/10000000000 : ℝ)*X 0 2+(3015210701/10000000000 : ℝ)*X 1 0+(7927194231/10000000000 : ℝ)*X 1 1+(141328143/10000000000 : ℝ)*X 1 2+(3015210701/10000000000 : ℝ)*X 2 0+(7927194231/10000000000 : ℝ)*X 2 1+(141328143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-241357773/1250000000 : ℝ)*X 0 0+(358235799/1250000000 : ℝ)*X 0 1+(3437342711/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1299309257/10000000000 : ℝ)*X 1 0+(-483211339/2500000000 : ℝ)*X 1 1+(8081778303/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7134519653/10000000000 : ℝ)*X 2 0+(1981465959/5000000000 : ℝ)*X 2 1+(-19297987/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7065858971/10000000000 : ℝ)*X 0 0+(4006182863/10000000000 : ℝ)*X 0 1+(81830779/5000000000 : ℝ)*X 0 2+(7065858971/10000000000 : ℝ)*X 1 0+(4006182863/10000000000 : ℝ)*X 1 1+(81830779/5000000000 : ℝ)*X 1 2+(7065858971/10000000000 : ℝ)*X 2 0+(4006182863/10000000000 : ℝ)*X 2 1+(81830779/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-4313573707/10000000000 : ℝ)*X 0 0+(856649067/2000000000 : ℝ)*X 0 1+(169937351/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((714494171/5000000000 : ℝ)*X 1 0+(-182414397/1250000000 : ℝ)*X 1 1+(2084119803/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((6567287911/10000000000 : ℝ)*X 2 0+(4574262769/10000000000 : ℝ)*X 2 1+(-121993977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((602652223/2500000000 : ℝ)*X 0 0+(210695299/250000000 : ℝ)*X 0 1+(2613013/250000000 : ℝ)*X 0 2+(602652223/2500000000 : ℝ)*X 1 0+(210695299/250000000 : ℝ)*X 1 1+(2613013/250000000 : ℝ)*X 1 2+(602652223/2500000000 : ℝ)*X 2 0+(210695299/250000000 : ℝ)*X 2 1+(2613013/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((27377/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27377/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (214814004021471668913/12500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1026612738419/1000000000000 : ℝ)*(base7) + (21456115311/1000000000000 : ℝ)*(base39) + (16988897339/500000000000 : ℝ)*(base49) + (41976589083/250000000000 : ℝ)*(base60) + (198757187239/100000000000 : ℝ)*(major_s0_0) + (198757187239/100000000000 : ℝ)*(major_s0_1) + (198757187239/100000000000 : ℝ)*(major_s0_2) + (4883557/1000000000000 : ℝ)*(sp_s0_2) + (51153570121/20000000000 : ℝ)*(sp_s0_7) + (2557504318841/1000000000000 : ℝ)*(sp_s0_8) + (2557673622493/1000000000000 : ℝ)*(sp_s0_9) + (75970004303/40000000000 : ℝ)*(sp_s0_13) + (174187209/1000000000000 : ℝ)*(sp_s0_22) + (25045777/500000000000 : ℝ)*(sp_s0_27) + (87268746071/100000000000 : ℝ)*(f.failure) + (51153570121/20000000000 : ℝ)*(f.sum) + (2038655207/10000000000000000000000 : ℝ)*base63 + (583302356110799/1000000000000000000000000000 : ℝ)*base64 + (586352810889201/1000000000000000000000000000 : ℝ)*base66 + (168878267029639/1000000000000000000000000000 : ℝ)*base68 + (5063447149529/25000000000000000000000000 : ℝ)*base70 + (298061088910799/1000000000000000000000000000 : ℝ)*base72 + (654149276270361/1000000000000000000000000000 : ℝ)*base74 + (946359304070361/1000000000000000000000000000 : ℝ)*base76 + (136354561/5000000000000000000000 : ℝ)*base79 + (8463/10000000000000000 : ℝ)*base87 + (8463/10000000000000000 : ℝ)*base89 + (8463/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10803/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10803/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (100960109540731023/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (197236988657/1000000000000 : ℝ)*(base5) + (40471252643/40000000000 : ℝ)*(base7) + (446164471/500000000000 : ℝ)*(base49) + (2352578371/7812500000 : ℝ)*(base60) + (555547794321/250000000000 : ℝ)*(major_s0_0) + (555547794321/250000000000 : ℝ)*(major_s0_1) + (555547794321/250000000000 : ℝ)*(major_s0_2) + (2775351/250000000000 : ℝ)*(sp_s0_0) + (11106799/1000000000000 : ℝ)*(sp_s0_1) + (72100033/1000000000000 : ℝ)*(sp_s0_7) + (586337680619/200000000000 : ℝ)*(sp_s0_14) + (1465880248867/500000000000 : ℝ)*(sp_s0_15) + (312900859319/100000000000 : ℝ)*(sp_s0_16) + (895123295699/500000000000 : ℝ)*(sp_s0_20) + (975702263981/1000000000000 : ℝ)*(f.failure) + (2931771604533/1000000000000 : ℝ)*(f.sum) + (3447015593/10000000000000000000000 : ℝ)*base62 + (749662323006839/2500000000000000000000000000 : ℝ)*base65 + (1602706308493161/2500000000000000000000000000 : ℝ)*base67 + (164135422452079/2500000000000000000000000000 : ℝ)*base69 + (7444586623631/62500000000000000000000000 : ℝ)*base70 + (298261327256839/2500000000000000000000000000 : ℝ)*base73 + (625398659047921/2500000000000000000000000000 : ℝ)*base75 + (602259567547921/2500000000000000000000000000 : ℝ)*base77 + (520767717/5000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (64693/100000000000000000 : ℝ)*base87 + (64693/100000000000000000 : ℝ)*base89 + (64693/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2163/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2163/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (652553855934583361331/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (30901930193/250000000000 : ℝ)*(base7) + (270915789793/500000000000 : ℝ)*(base39) + (566688144717/1000000000000 : ℝ)*(base49) + (159647/1000000000000 : ℝ)*(base60) + (932284510007/500000000000 : ℝ)*(major_s0_0) + (932284510007/500000000000 : ℝ)*(major_s0_1) + (932284510007/500000000000 : ℝ)*(major_s0_2) + (42243901/1000000000000 : ℝ)*(sp_s0_1) + (3251611/62500000000 : ℝ)*(sp_s0_13) + (9377383/1000000000000 : ℝ)*(sp_s0_15) + (2844861789181/1000000000000 : ℝ)*(sp_s0_21) + (2844810167897/1000000000000 : ℝ)*(sp_s0_22) + (2844861789181/1000000000000 : ℝ)*(sp_s0_23) + (942236028521/1000000000000 : ℝ)*(sp_s0_27) + (32747213341/40000000000 : ℝ)*(f.failure) + (2844861789181/1000000000000 : ℝ)*(f.sum) + (1872573741/10000000000000000000000 : ℝ)*base62 + (2217590310047713/5000000000000000000000000000 : ℝ)*base65 + (942866910452287/5000000000000000000000000000 : ℝ)*base67 + (961647951198793/5000000000000000000000000000 : ℝ)*base69 + (8748797346223/125000000000000000000000000 : ℝ)*base71 + (2336945349547713/5000000000000000000000000000 : ℝ)*base73 + (2852697817801207/5000000000000000000000000000 : ℝ)*base75 + (3498906314801207/5000000000000000000000000000 : ℝ)*base77 + (2534202051/10000000000000000000000 : ℝ)*base78 + (3227/4000000000000000 : ℝ)*base86 + (3227/4000000000000000 : ℝ)*base88 + (3227/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (27377/50000 : ℝ) ^ (95/16 : ℝ) ≤ (1398988431976388771/50000000000000000000 : ℝ) := by
    have hpowers : (27377/50000 : ℝ)^95 ≤ (1398988431976388771/50000000000000000000 : ℝ)^16 := by
      have hnat : (27377 : ℕ)^95*50000000000000000000^16 ≤ 1398988431976388771^16*50000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27377 50000 1398988431976388771 50000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27377/50000 : ℝ)) (X := (1398988431976388771/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (51398988431976388771/50000000000000000000 : ℝ) ≤ (5023292390081719/5000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (51398988431976388771/50000000000000000000 : ℝ)^16 ≤ (5023292390081719/5000000000000000 : ℝ)^95 := by
      have hnat : (51398988431976388771 : ℕ)^16*5000000000000000^95 ≤ 5023292390081719^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51398988431976388771 50000000000000000000 5023292390081719 5000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5023292390081719/5000000000000000 : ℝ)) (X := (51398988431976388771/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (26398988431976388771/25000000000000000000 : ℝ) ≤ (504606340958793/500000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (26398988431976388771/25000000000000000000 : ℝ)^16 ≤ (504606340958793/500000000000000 : ℝ)^95 := by
      have hnat : (26398988431976388771 : ℕ)^16*500000000000000^95 ≤ 504606340958793^95*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26398988431976388771 25000000000000000000 504606340958793 500000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (504606340958793/500000000000000 : ℝ)) (X := (26398988431976388771/25000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(23292390081719/2737700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(22771019506211/2737700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (27377/50000 : ℝ)) (alpha := (23292390081719/2737700000000000 : ℝ)) (beta := (22771019506211/2737700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (27377/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(23292390081719/2737700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(22771019506211/2737700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (10803/20000 : ℝ) ^ (95/16 : ℝ) ≤ (516219171482225633/20000000000000000000 : ℝ) := by
    have hpowers : (10803/20000 : ℝ)^95 ≤ (516219171482225633/20000000000000000000 : ℝ)^16 := by
      have hnat : (10803 : ℕ)^95*20000000000000000000^16 ≤ 516219171482225633^16*20000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10803 20000 516219171482225633 20000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10803/20000 : ℝ)) (X := (516219171482225633/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20516219171482225633/20000000000000000000 : ℝ) ≤ (2008602355926127/2000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (20516219171482225633/20000000000000000000 : ℝ)^16 ≤ (2008602355926127/2000000000000000 : ℝ)^95 := by
      have hnat : (20516219171482225633 : ℕ)^16*2000000000000000^95 ≤ 2008602355926127^95*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20516219171482225633 20000000000000000000 2008602355926127 2000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2008602355926127/2000000000000000 : ℝ)) (X := (20516219171482225633/20000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10516219171482225633/10000000000000000000 : ℝ) ≤ (10085132808307521/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (10516219171482225633/10000000000000000000 : ℝ)^16 ≤ (10085132808307521/10000000000000000 : ℝ)^95 := by
      have hnat : (10516219171482225633 : ℕ)^16*10000000000000000^95 ≤ 10085132808307521^95*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10516219171482225633 10000000000000000000 10085132808307521 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10085132808307521/10000000000000000 : ℝ)) (X := (10516219171482225633/10000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(8602355926127/1080300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(21060514338443/2700750000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (10803/20000 : ℝ)) (alpha := (8602355926127/1080300000000000 : ℝ)) (beta := (21060514338443/2700750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (10803/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(8602355926127/1080300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(21060514338443/2700750000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2163/12500 : ℝ) ^ (95/16 : ℝ) ≤ (374459536103551/12500000000000000000 : ℝ) := by
    have hpowers : (2163/12500 : ℝ)^95 ≤ (374459536103551/12500000000000000000 : ℝ)^16 := by
      have hnat : (2163 : ℕ)^95*12500000000000000000^16 ≤ 374459536103551^16*12500^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2163 12500 374459536103551 12500000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2163/12500 : ℝ)) (X := (374459536103551/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (12500374459536103551/12500000000000000000 : ℝ) ≤ (10000050452866969/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (12500374459536103551/12500000000000000000 : ℝ)^16 ≤ (10000050452866969/10000000000000000 : ℝ)^95 := by
      have hnat : (12500374459536103551 : ℕ)^16*10000000000000000^95 ≤ 10000050452866969^95*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500374459536103551 12500000000000000000 10000050452866969 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000050452866969/10000000000000000 : ℝ)) (X := (12500374459536103551/12500000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (6250374459536103551/6250000000000000000 : ℝ) ≤ (5000050452238569/5000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (6250374459536103551/6250000000000000000 : ℝ)^16 ≤ (5000050452238569/5000000000000000 : ℝ)^95 := by
      have hnat : (6250374459536103551 : ℕ)^16*5000000000000000^95 ≤ 5000050452238569^95*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250374459536103551 6250000000000000000 5000050452238569 5000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000050452238569/5000000000000000 : ℝ)) (X := (6250374459536103551/6250000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(16817622323/576800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(50451610169/1730400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (2163/12500 : ℝ)) (alpha := (16817622323/576800000000000 : ℝ)) (beta := (50451610169/1730400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (2163/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(16817622323/576800000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(50451610169/1730400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-699821841/2000000000 : ℝ)*X 0 0+(437148283/1250000000 : ℝ)*X 0 1+(4977550937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((735726683/2500000000 : ℝ)*X 1 0+(-2941289453/10000000000 : ℝ)*X 1 1+(1494393943/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2570681659/5000000000 : ℝ)*X 2 0+(5144143403/10000000000 : ℝ)*X 2 1+(-1462160137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4924462999/10000000000 : ℝ)*X 0 0+(24635629/50000000 : ℝ)*X 0 1+(499926211/2500000000 : ℝ)*X 0 2+(4924462999/10000000000 : ℝ)*X 1 0+(24635629/50000000 : ℝ)*X 1 1+(499926211/2500000000 : ℝ)*X 1 2+(4924462999/10000000000 : ℝ)*X 2 0+(24635629/50000000 : ℝ)*X 2 1+(499926211/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330051_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-533259/50000 : ℝ) < ((-227753/100000 : ℝ)*P 0+(-227753/100000 : ℝ)*P 1+(-227753/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-533259/50000 : ℝ) < (-840555893956057562153281547459/79886800000000000000000000000 : ℝ) := by norm_num
    linear_combination (104129/1000000000000 : ℝ)*(base11) + (571271/1000000000000 : ℝ)*(base19) + (453/500000000000 : ℝ)*(base40) + (4321/40000000000 : ℝ)*(base43) + (6280662903/20000000000 : ℝ)*(base49) + (483617/1000000000000 : ℝ)*(base53) + (194535047877/1000000000000 : ℝ)*(base59) + (752858099891/1000000000000 : ℝ)*(base60) + (227753/100000 : ℝ)*(major_s1_0) + (91101195679/40000000000 : ℝ)*(major_s1_1) + (2277529516383/1000000000000 : ℝ)*(major_s1_2) + (175363916443/50000000000 : ℝ)*(sp_s1_0) + (219204873109/62500000000 : ℝ)*(sp_s1_1) + (1753639458303/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (438409878079/125000000000 : ℝ)*(f.sum) + (180385403723719979/479320800000000000000000000000 : ℝ)*base62 + (213210256605709/576800000000000000000000000 : ℝ)*base65 + (3639787056211/8310000000000000000000000 : ℝ)*base67 + (260018124967149/576800000000000000000000000 : ℝ)*base68 + (63910170736125541/2255864800000000000000000000000 : ℝ)*base70 + (25360116557/133676757812500000000000 : ℝ)*base72 + (3194457937009/16620000000000000000000000 : ℝ)*base75 + (67499649090907/136885000000000000000000000 : ℝ)*base77 + (52189280009642201/227502870000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p030_b022 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 52)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=51 := by omega
  rcases hc with rfl
  · exact collision_c330051 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 52)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b022 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
