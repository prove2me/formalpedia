-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b025
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:27:19.066428+00:00
-- url     : https://prove2.me/submissions/32482ecb-beb3-4c63-84c5-2d124b769895

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329053_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329053_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329053_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329054_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329054_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329054_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329055_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329055_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329055_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
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
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c329053 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : False := by
  have h0 := collision_c329053_s0 p hpa hpb X hX
  have h1 := collision_c329053_s1 p hpa hpb X hX h0
  exact collision_c329053_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c329054 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : False := by
  have h0 := collision_c329054_s0 p hpa hpb X hX
  have h1 := collision_c329054_s1 p hpa hpb X hX h0
  exact collision_c329054_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c329055 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c329055_s0 p hpa hpb X hX
  have h1 := collision_c329055_s1 p hpa hpb X hX h0
  exact collision_c329055_s2 p hpa hpb X hX h1

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
theorem collision_support_c329052_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-117895619/2000000000 : ℝ)*x 0 + (1671985643/5000000000 : ℝ)*x 1 + (-7423801309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117895619/2000000000 : ℝ)^95 ≤ (12978021827/390625000000 : ℝ)^79 := by
    have hnat : (117895619 : ℕ)^95*390625000000^79 ≤ 12978021827^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117895619 2000000000 12978021827 390625000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1671985643/5000000000 : ℝ)^95 ≤ (26786171732171/100000000000000 : ℝ)^79 := by
    have hnat : (1671985643 : ℕ)^95*100000000000000^79 ≤ 26786171732171^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1671985643 5000000000 26786171732171 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7423801309/10000000000 : ℝ)^95 ≤ (34945727331169/50000000000000 : ℝ)^79 := by
    have hnat : (7423801309 : ℕ)^95*50000000000000^79 ≤ 34945727331169^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7423801309 10000000000 34945727331169 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117895619/2000000000 : ℝ), (1671985643/5000000000 : ℝ), (-7423801309/10000000000 : ℝ)] ![(12978021827/390625000000 : ℝ), (26786171732171/100000000000000 : ℝ), (34945727331169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117895619/2000000000 : ℝ)|^95 ≤ (12978021827/390625000000 : ℝ)^79
        have hw : |(-117895619/2000000000 : ℝ)|=(117895619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1671985643/5000000000 : ℝ)|^95 ≤ (26786171732171/100000000000000 : ℝ)^79
        have hw : |(1671985643/5000000000 : ℝ)|=(1671985643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7423801309/10000000000 : ℝ)|^95 ≤ (34945727331169/50000000000000 : ℝ)^79
        have hw : |(-7423801309/10000000000 : ℝ)|=(7423801309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4921194183/10000000000 : ℝ)*x 0 + (-2166700639/10000000000 : ℝ)*x 1 + (-4810195323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4921194183/10000000000 : ℝ)^95 ≤ (21314494554171/50000000000000 : ℝ)^79 := by
    have hnat : (4921194183 : ℕ)^95*50000000000000^79 ≤ 21314494554171^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4921194183 10000000000 21314494554171 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2166700639/10000000000 : ℝ)^95 ≤ (3973902254413/25000000000000 : ℝ)^79 := by
    have hnat : (2166700639 : ℕ)^95*25000000000000^79 ≤ 3973902254413^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166700639 10000000000 3973902254413 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4810195323/10000000000 : ℝ)^95 ≤ (20737700932177/50000000000000 : ℝ)^79 := by
    have hnat : (4810195323 : ℕ)^95*50000000000000^79 ≤ 20737700932177^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4810195323 10000000000 20737700932177 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4921194183/10000000000 : ℝ), (-2166700639/10000000000 : ℝ), (-4810195323/10000000000 : ℝ)] ![(21314494554171/50000000000000 : ℝ), (3973902254413/25000000000000 : ℝ), (20737700932177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4921194183/10000000000 : ℝ)|^95 ≤ (21314494554171/50000000000000 : ℝ)^79
        have hw : |(4921194183/10000000000 : ℝ)|=(4921194183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2166700639/10000000000 : ℝ)|^95 ≤ (3973902254413/25000000000000 : ℝ)^79
        have hw : |(-2166700639/10000000000 : ℝ)|=(2166700639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4810195323/10000000000 : ℝ)|^95 ≤ (20737700932177/50000000000000 : ℝ)^79
        have hw : |(-4810195323/10000000000 : ℝ)|=(4810195323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4921194459/10000000000 : ℝ)*x 0 + (6146605737/10000000000 : ℝ)*x 1 + (333455559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4921194459/10000000000 : ℝ)^95 ≤ (42628991983357/100000000000000 : ℝ)^79 := by
    have hnat : (4921194459 : ℕ)^95*100000000000000^79 ≤ 42628991983357^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4921194459 10000000000 42628991983357 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6146605737/10000000000 : ℝ)^95 ≤ (11139285207853/20000000000000 : ℝ)^79 := by
    have hnat : (6146605737 : ℕ)^95*20000000000000^79 ≤ 11139285207853^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6146605737 10000000000 11139285207853 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333455559/10000000000 : ℝ)^95 ≤ (1674581965991/100000000000000 : ℝ)^79 := by
    have hnat : (333455559 : ℕ)^95*100000000000000^79 ≤ 1674581965991^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333455559 10000000000 1674581965991 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4921194459/10000000000 : ℝ), (6146605737/10000000000 : ℝ), (333455559/10000000000 : ℝ)] ![(42628991983357/100000000000000 : ℝ), (11139285207853/20000000000000 : ℝ), (1674581965991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4921194459/10000000000 : ℝ)|^95 ≤ (42628991983357/100000000000000 : ℝ)^79
        have hw : |(4921194459/10000000000 : ℝ)|=(4921194459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6146605737/10000000000 : ℝ)|^95 ≤ (11139285207853/20000000000000 : ℝ)^79
        have hw : |(6146605737/10000000000 : ℝ)|=(6146605737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(333455559/10000000000 : ℝ)|^95 ≤ (1674581965991/100000000000000 : ℝ)^79
        have hw : |(333455559/10000000000 : ℝ)|=(333455559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-653953839/5000000000 : ℝ)*x 0 + (625563277/5000000000 : ℝ)*x 1 + (-8575300881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653953839/5000000000 : ℝ)^95 ≤ (2165688558449/25000000000000 : ℝ)^79 := by
    have hnat : (653953839 : ℕ)^95*25000000000000^79 ≤ 2165688558449^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653953839 5000000000 2165688558449 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625563277/5000000000 : ℝ)^95 ≤ (821251501727/10000000000000 : ℝ)^79 := by
    have hnat : (625563277 : ℕ)^95*10000000000000^79 ≤ 821251501727^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625563277 5000000000 821251501727 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8575300881/10000000000 : ℝ)^95 ≤ (83124730734877/100000000000000 : ℝ)^79 := by
    have hnat : (8575300881 : ℕ)^95*100000000000000^79 ≤ 83124730734877^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8575300881 10000000000 83124730734877 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-653953839/5000000000 : ℝ), (625563277/5000000000 : ℝ), (-8575300881/10000000000 : ℝ)] ![(2165688558449/25000000000000 : ℝ), (821251501727/10000000000000 : ℝ), (83124730734877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-653953839/5000000000 : ℝ)|^95 ≤ (2165688558449/25000000000000 : ℝ)^79
        have hw : |(-653953839/5000000000 : ℝ)|=(653953839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625563277/5000000000 : ℝ)|^95 ≤ (821251501727/10000000000000 : ℝ)^79
        have hw : |(625563277/5000000000 : ℝ)|=(625563277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8575300881/10000000000 : ℝ)|^95 ≤ (83124730734877/100000000000000 : ℝ)^79
        have hw : |(-8575300881/10000000000 : ℝ)|=(8575300881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (311090393/1000000000 : ℝ)*x 0 + (-589692851/5000000000 : ℝ)*x 1 + (-7237986201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (311090393/1000000000 : ℝ)^95 ≤ (2455727016329/10000000000000 : ℝ)^79 := by
    have hnat : (311090393 : ℕ)^95*10000000000000^79 ≤ 2455727016329^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311090393 1000000000 2455727016329 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (589692851/5000000000 : ℝ)^95 ≤ (7649565924409/100000000000000 : ℝ)^79 := by
    have hnat : (589692851 : ℕ)^95*100000000000000^79 ≤ 7649565924409^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589692851 5000000000 7649565924409 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7237986201/10000000000 : ℝ)^95 ≤ (108469062241/160000000000 : ℝ)^79 := by
    have hnat : (7237986201 : ℕ)^95*160000000000^79 ≤ 108469062241^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7237986201 10000000000 108469062241 160000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(311090393/1000000000 : ℝ), (-589692851/5000000000 : ℝ), (-7237986201/10000000000 : ℝ)] ![(2455727016329/10000000000000 : ℝ), (7649565924409/100000000000000 : ℝ), (108469062241/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(311090393/1000000000 : ℝ)|^95 ≤ (2455727016329/10000000000000 : ℝ)^79
        have hw : |(311090393/1000000000 : ℝ)|=(311090393/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-589692851/5000000000 : ℝ)|^95 ≤ (7649565924409/100000000000000 : ℝ)^79
        have hw : |(-589692851/5000000000 : ℝ)|=(589692851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7237986201/10000000000 : ℝ)|^95 ≤ (108469062241/160000000000 : ℝ)^79
        have hw : |(-7237986201/10000000000 : ℝ)|=(7237986201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7777261/25000000 : ℝ)*x 0 + (3926199361/5000000000 : ℝ)*x 1 + (19484797/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7777261/25000000 : ℝ)^95 ≤ (24557274624861/100000000000000 : ℝ)^79 := by
    have hnat : (7777261 : ℕ)^95*100000000000000^79 ≤ 24557274624861^79*25000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7777261 25000000 24557274624861 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3926199361/5000000000 : ℝ)^95 ≤ (74771655368003/100000000000000 : ℝ)^79 := by
    have hnat : (3926199361 : ℕ)^95*100000000000000^79 ≤ 74771655368003^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3926199361 5000000000 74771655368003 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19484797/1250000000 : ℝ)^95 ≤ (671069995559/100000000000000 : ℝ)^79 := by
    have hnat : (19484797 : ℕ)^95*100000000000000^79 ≤ 671069995559^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19484797 1250000000 671069995559 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7777261/25000000 : ℝ), (3926199361/5000000000 : ℝ), (19484797/1250000000 : ℝ)] ![(24557274624861/100000000000000 : ℝ), (74771655368003/100000000000000 : ℝ), (671069995559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7777261/25000000 : ℝ)|^95 ≤ (24557274624861/100000000000000 : ℝ)^79
        have hw : |(7777261/25000000 : ℝ)|=(7777261/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3926199361/5000000000 : ℝ)|^95 ≤ (74771655368003/100000000000000 : ℝ)^79
        have hw : |(3926199361/5000000000 : ℝ)|=(3926199361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19484797/1250000000 : ℝ)|^95 ≤ (671069995559/100000000000000 : ℝ)^79
        have hw : |(19484797/1250000000 : ℝ)|=(19484797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (810449671/2000000000 : ℝ)*x 0 + (7040967187/10000000000 : ℝ)*x 1 + (-31219941/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (810449671/2000000000 : ℝ)^95 ≤ (8436884421861/25000000000000 : ℝ)^79 := by
    have hnat : (810449671 : ℕ)^95*25000000000000^79 ≤ 8436884421861^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810449671 2000000000 8436884421861 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7040967187/10000000000 : ℝ)^95 ≤ (65580246311911/100000000000000 : ℝ)^79 := by
    have hnat : (7040967187 : ℕ)^95*100000000000000^79 ≤ 65580246311911^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7040967187 10000000000 65580246311911 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31219941/2000000000 : ℝ)^95 ≤ (168053995317/25000000000000 : ℝ)^79 := by
    have hnat : (31219941 : ℕ)^95*25000000000000^79 ≤ 168053995317^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31219941 2000000000 168053995317 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(810449671/2000000000 : ℝ), (7040967187/10000000000 : ℝ), (-31219941/2000000000 : ℝ)] ![(8436884421861/25000000000000 : ℝ), (65580246311911/100000000000000 : ℝ), (168053995317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(810449671/2000000000 : ℝ)|^95 ≤ (8436884421861/25000000000000 : ℝ)^79
        have hw : |(810449671/2000000000 : ℝ)|=(810449671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7040967187/10000000000 : ℝ)|^95 ≤ (65580246311911/100000000000000 : ℝ)^79
        have hw : |(7040967187/10000000000 : ℝ)|=(7040967187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31219941/2000000000 : ℝ)|^95 ≤ (168053995317/25000000000000 : ℝ)^79
        have hw : |(-31219941/2000000000 : ℝ)|=(31219941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-100067441/5000000000 : ℝ)*x 0 + (911566957/5000000000 : ℝ)*x 1 + (-441822433/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100067441/5000000000 : ℝ)^95 ≤ (906331133483/100000000000000 : ℝ)^79 := by
    have hnat : (100067441 : ℕ)^95*100000000000000^79 ≤ 906331133483^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100067441 5000000000 906331133483 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (911566957/5000000000 : ℝ)^95 ≤ (3228872879149/25000000000000 : ℝ)^79 := by
    have hnat : (911566957 : ℕ)^95*25000000000000^79 ≤ 3228872879149^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911566957 5000000000 3228872879149 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441822433/500000000 : ℝ)^95 ≤ (43089088670551/50000000000000 : ℝ)^79 := by
    have hnat : (441822433 : ℕ)^95*50000000000000^79 ≤ 43089088670551^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441822433 500000000 43089088670551 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100067441/5000000000 : ℝ), (911566957/5000000000 : ℝ), (-441822433/500000000 : ℝ)] ![(906331133483/100000000000000 : ℝ), (3228872879149/25000000000000 : ℝ), (43089088670551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100067441/5000000000 : ℝ)|^95 ≤ (906331133483/100000000000000 : ℝ)^79
        have hw : |(-100067441/5000000000 : ℝ)|=(100067441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(911566957/5000000000 : ℝ)|^95 ≤ (3228872879149/25000000000000 : ℝ)^79
        have hw : |(911566957/5000000000 : ℝ)|=(911566957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441822433/500000000 : ℝ)|^95 ≤ (43089088670551/50000000000000 : ℝ)^79
        have hw : |(-441822433/500000000 : ℝ)|=(441822433/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (425675429/2500000000 : ℝ)*x 0 + (-2379695931/10000000000 : ℝ)*x 1 + (-3730400977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425675429/2500000000 : ℝ)^95 ≤ (5948258148003/50000000000000 : ℝ)^79 := by
    have hnat : (425675429 : ℕ)^95*50000000000000^79 ≤ 5948258148003^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425675429 2500000000 5948258148003 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2379695931/10000000000 : ℝ)^95 ≤ (4448231114951/25000000000000 : ℝ)^79 := by
    have hnat : (2379695931 : ℕ)^95*25000000000000^79 ≤ 4448231114951^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2379695931 10000000000 4448231114951 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3730400977/5000000000 : ℝ)^95 ≤ (878881990427/1250000000000 : ℝ)^79 := by
    have hnat : (3730400977 : ℕ)^95*1250000000000^79 ≤ 878881990427^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3730400977 5000000000 878881990427 1250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425675429/2500000000 : ℝ), (-2379695931/10000000000 : ℝ), (-3730400977/5000000000 : ℝ)] ![(5948258148003/50000000000000 : ℝ), (4448231114951/25000000000000 : ℝ), (878881990427/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425675429/2500000000 : ℝ)|^95 ≤ (5948258148003/50000000000000 : ℝ)^79
        have hw : |(425675429/2500000000 : ℝ)|=(425675429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2379695931/10000000000 : ℝ)|^95 ≤ (4448231114951/25000000000000 : ℝ)^79
        have hw : |(-2379695931/10000000000 : ℝ)|=(2379695931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3730400977/5000000000 : ℝ)|^95 ≤ (878881990427/1250000000000 : ℝ)^79
        have hw : |(-3730400977/5000000000 : ℝ)|=(3730400977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7132532867/10000000000 : ℝ)*x 0 + (389692273/1000000000 : ℝ)*x 1 + (5036541/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7132532867/10000000000 : ℝ)^95 ≤ (66607173279909/100000000000000 : ℝ)^79 := by
    have hnat : (7132532867 : ℕ)^95*100000000000000^79 ≤ 66607173279909^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7132532867 10000000000 66607173279909 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389692273/1000000000 : ℝ)^95 ≤ (16099041146267/50000000000000 : ℝ)^79 := by
    have hnat : (389692273 : ℕ)^95*50000000000000^79 ≤ 16099041146267^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389692273 1000000000 16099041146267 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5036541/200000000 : ℝ)^95 ≤ (74671526369/6250000000000 : ℝ)^79 := by
    have hnat : (5036541 : ℕ)^95*6250000000000^79 ≤ 74671526369^79*200000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5036541 200000000 74671526369 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7132532867/10000000000 : ℝ), (389692273/1000000000 : ℝ), (5036541/200000000 : ℝ)] ![(66607173279909/100000000000000 : ℝ), (16099041146267/50000000000000 : ℝ), (74671526369/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7132532867/10000000000 : ℝ)|^95 ≤ (66607173279909/100000000000000 : ℝ)^79
        have hw : |(7132532867/10000000000 : ℝ)|=(7132532867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(389692273/1000000000 : ℝ)|^95 ≤ (16099041146267/50000000000000 : ℝ)^79
        have hw : |(389692273/1000000000 : ℝ)|=(389692273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5036541/200000000 : ℝ)|^95 ≤ (74671526369/6250000000000 : ℝ)^79
        have hw : |(5036541/200000000 : ℝ)|=(5036541/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4116216257/5000000000 : ℝ)*x 0 + (1290931667/5000000000 : ℝ)*x 1 + (-257934229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4116216257/5000000000 : ℝ)^95 ≤ (39572179165811/50000000000000 : ℝ)^79 := by
    have hnat : (4116216257 : ℕ)^95*50000000000000^79 ≤ 39572179165811^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116216257 5000000000 39572179165811 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1290931667/5000000000 : ℝ)^95 ≤ (19625969672557/100000000000000 : ℝ)^79 := by
    have hnat : (1290931667 : ℕ)^95*100000000000000^79 ≤ 19625969672557^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290931667 5000000000 19625969672557 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257934229/10000000000 : ℝ)^95 ≤ (1229671983287/100000000000000 : ℝ)^79 := by
    have hnat : (257934229 : ℕ)^95*100000000000000^79 ≤ 1229671983287^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257934229 10000000000 1229671983287 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4116216257/5000000000 : ℝ), (1290931667/5000000000 : ℝ), (-257934229/10000000000 : ℝ)] ![(39572179165811/50000000000000 : ℝ), (19625969672557/100000000000000 : ℝ), (1229671983287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4116216257/5000000000 : ℝ)|^95 ≤ (39572179165811/50000000000000 : ℝ)^79
        have hw : |(4116216257/5000000000 : ℝ)|=(4116216257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1290931667/5000000000 : ℝ)|^95 ≤ (19625969672557/100000000000000 : ℝ)^79
        have hw : |(1290931667/5000000000 : ℝ)|=(1290931667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257934229/10000000000 : ℝ)|^95 ≤ (1229671983287/100000000000000 : ℝ)^79
        have hw : |(-257934229/10000000000 : ℝ)|=(257934229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2034669/2500000000 : ℝ)*x 0 + (1157058829/2500000000 : ℝ)*x 1 + (-821738343/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2034669/2500000000 : ℝ)^95 ≤ (19268287983/100000000000000 : ℝ)^79 := by
    have hnat : (2034669 : ℕ)^95*100000000000000^79 ≤ 19268287983^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034669 2500000000 19268287983 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1157058829/2500000000 : ℝ)^95 ≤ (7919202793311/20000000000000 : ℝ)^79 := by
    have hnat : (1157058829 : ℕ)^95*20000000000000^79 ≤ 7919202793311^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157058829 2500000000 7919202793311 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (821738343/1250000000 : ℝ)^95 ≤ (60384717734067/100000000000000 : ℝ)^79 := by
    have hnat : (821738343 : ℕ)^95*100000000000000^79 ≤ 60384717734067^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821738343 1250000000 60384717734067 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2034669/2500000000 : ℝ), (1157058829/2500000000 : ℝ), (-821738343/1250000000 : ℝ)] ![(19268287983/100000000000000 : ℝ), (7919202793311/20000000000000 : ℝ), (60384717734067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2034669/2500000000 : ℝ)|^95 ≤ (19268287983/100000000000000 : ℝ)^79
        have hw : |(-2034669/2500000000 : ℝ)|=(2034669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1157058829/2500000000 : ℝ)|^95 ≤ (7919202793311/20000000000000 : ℝ)^79
        have hw : |(1157058829/2500000000 : ℝ)|=(1157058829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-821738343/1250000000 : ℝ)|^95 ≤ (60384717734067/100000000000000 : ℝ)^79
        have hw : |(-821738343/1250000000 : ℝ)|=(821738343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6700260063/10000000000 : ℝ)*x 0 + (-520040823/2500000000 : ℝ)*x 1 + (-2954646547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6700260063/10000000000 : ℝ)^95 ≤ (3089155155509/5000000000000 : ℝ)^79 := by
    have hnat : (6700260063 : ℕ)^95*5000000000000^79 ≤ 3089155155509^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6700260063 10000000000 3089155155509 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520040823/2500000000 : ℝ)^95 ≤ (15135284130931/100000000000000 : ℝ)^79 := by
    have hnat : (520040823 : ℕ)^95*100000000000000^79 ≤ 15135284130931^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520040823 2500000000 15135284130931 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2954646547/10000000000 : ℝ)^95 ≤ (1154080636679/5000000000000 : ℝ)^79 := by
    have hnat : (2954646547 : ℕ)^95*5000000000000^79 ≤ 1154080636679^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2954646547 10000000000 1154080636679 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6700260063/10000000000 : ℝ), (-520040823/2500000000 : ℝ), (-2954646547/10000000000 : ℝ)] ![(3089155155509/5000000000000 : ℝ), (15135284130931/100000000000000 : ℝ), (1154080636679/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6700260063/10000000000 : ℝ)|^95 ≤ (3089155155509/5000000000000 : ℝ)^79
        have hw : |(6700260063/10000000000 : ℝ)|=(6700260063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-520040823/2500000000 : ℝ)|^95 ≤ (15135284130931/100000000000000 : ℝ)^79
        have hw : |(-520040823/2500000000 : ℝ)|=(520040823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2954646547/10000000000 : ℝ)|^95 ≤ (1154080636679/5000000000000 : ℝ)^79
        have hw : |(-2954646547/10000000000 : ℝ)|=(2954646547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (228614577/1000000000 : ℝ)*x 0 + (119413379/156250000 : ℝ)*x 1 + (1555472513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228614577/1000000000 : ℝ)^95 ≤ (16955171249297/100000000000000 : ℝ)^79 := by
    have hnat : (228614577 : ℕ)^95*100000000000000^79 ≤ 16955171249297^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228614577 1000000000 16955171249297 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119413379/156250000 : ℝ)^95 ≤ (9046778435619/12500000000000 : ℝ)^79 := by
    have hnat : (119413379 : ℕ)^95*12500000000000^79 ≤ 9046778435619^79*156250000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119413379 156250000 9046778435619 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1555472513/10000000000 : ℝ)^95 ≤ (2134120250303/20000000000000 : ℝ)^79 := by
    have hnat : (1555472513 : ℕ)^95*20000000000000^79 ≤ 2134120250303^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555472513 10000000000 2134120250303 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(228614577/1000000000 : ℝ), (119413379/156250000 : ℝ), (1555472513/10000000000 : ℝ)] ![(16955171249297/100000000000000 : ℝ), (9046778435619/12500000000000 : ℝ), (2134120250303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(228614577/1000000000 : ℝ)|^95 ≤ (16955171249297/100000000000000 : ℝ)^79
        have hw : |(228614577/1000000000 : ℝ)|=(228614577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(119413379/156250000 : ℝ)|^95 ≤ (9046778435619/12500000000000 : ℝ)^79
        have hw : |(119413379/156250000 : ℝ)|=(119413379/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1555472513/10000000000 : ℝ)|^95 ≤ (2134120250303/20000000000000 : ℝ)^79
        have hw : |(1555472513/10000000000 : ℝ)|=(1555472513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s0_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1132881969/1250000000 : ℝ)*x 0 + (287960761/2000000000 : ℝ)*x 1 + (-293043907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1132881969/1250000000 : ℝ)^95 ≤ (44421316025629/50000000000000 : ℝ)^79 := by
    have hnat : (1132881969 : ℕ)^95*50000000000000^79 ≤ 44421316025629^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132881969 1250000000 44421316025629 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287960761/2000000000 : ℝ)^95 ≤ (9723734733841/100000000000000 : ℝ)^79 := by
    have hnat : (287960761 : ℕ)^95*100000000000000^79 ≤ 9723734733841^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287960761 2000000000 9723734733841 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (293043907/10000000000 : ℝ)^95 ≤ (1433633207417/100000000000000 : ℝ)^79 := by
    have hnat : (293043907 : ℕ)^95*100000000000000^79 ≤ 1433633207417^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293043907 10000000000 1433633207417 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1132881969/1250000000 : ℝ), (287960761/2000000000 : ℝ), (-293043907/10000000000 : ℝ)] ![(44421316025629/50000000000000 : ℝ), (9723734733841/100000000000000 : ℝ), (1433633207417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1132881969/1250000000 : ℝ)|^95 ≤ (44421316025629/50000000000000 : ℝ)^79
        have hw : |(1132881969/1250000000 : ℝ)|=(1132881969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(287960761/2000000000 : ℝ)|^95 ≤ (9723734733841/100000000000000 : ℝ)^79
        have hw : |(287960761/2000000000 : ℝ)|=(287960761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-293043907/10000000000 : ℝ)|^95 ≤ (1433633207417/100000000000000 : ℝ)^79
        have hw : |(-293043907/10000000000 : ℝ)|=(293043907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-37408591/200000000 : ℝ)*x 0 + (3669994209/10000000000 : ℝ)*x 1 + (-1560183491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37408591/200000000 : ℝ)^95 ≤ (13319454531871/100000000000000 : ℝ)^79 := by
    have hnat : (37408591 : ℕ)^95*100000000000000^79 ≤ 13319454531871^79*200000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37408591 200000000 13319454531871 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3669994209/10000000000 : ℝ)^95 ≤ (29956863586659/100000000000000 : ℝ)^79 := by
    have hnat : (3669994209 : ℕ)^95*100000000000000^79 ≤ 29956863586659^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3669994209 10000000000 29956863586659 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1560183491/2500000000 : ℝ)^95 ≤ (56723681867441/100000000000000 : ℝ)^79 := by
    have hnat : (1560183491 : ℕ)^95*100000000000000^79 ≤ 56723681867441^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560183491 2500000000 56723681867441 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37408591/200000000 : ℝ), (3669994209/10000000000 : ℝ), (-1560183491/2500000000 : ℝ)] ![(13319454531871/100000000000000 : ℝ), (29956863586659/100000000000000 : ℝ), (56723681867441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37408591/200000000 : ℝ)|^95 ≤ (13319454531871/100000000000000 : ℝ)^79
        have hw : |(-37408591/200000000 : ℝ)|=(37408591/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3669994209/10000000000 : ℝ)|^95 ≤ (29956863586659/100000000000000 : ℝ)^79
        have hw : |(3669994209/10000000000 : ℝ)|=(3669994209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1560183491/2500000000 : ℝ)|^95 ≤ (56723681867441/100000000000000 : ℝ)^79
        have hw : |(-1560183491/2500000000 : ℝ)|=(1560183491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2272129193/5000000000 : ℝ)*x 0 + (-27500889/100000000 : ℝ)*x 1 + (-4676457843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2272129193/5000000000 : ℝ)^95 ≤ (7746730261339/20000000000000 : ℝ)^79 := by
    have hnat : (2272129193 : ℕ)^95*20000000000000^79 ≤ 7746730261339^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272129193 5000000000 7746730261339 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27500889/100000000 : ℝ)^95 ≤ (5293424377839/25000000000000 : ℝ)^79 := by
    have hnat : (27500889 : ℕ)^95*25000000000000^79 ≤ 5293424377839^79*100000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27500889 100000000 5293424377839 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4676457843/10000000000 : ℝ)^95 ≤ (40092651159339/100000000000000 : ℝ)^79 := by
    have hnat : (4676457843 : ℕ)^95*100000000000000^79 ≤ 40092651159339^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4676457843 10000000000 40092651159339 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2272129193/5000000000 : ℝ), (-27500889/100000000 : ℝ), (-4676457843/10000000000 : ℝ)] ![(7746730261339/20000000000000 : ℝ), (5293424377839/25000000000000 : ℝ), (40092651159339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2272129193/5000000000 : ℝ)|^95 ≤ (7746730261339/20000000000000 : ℝ)^79
        have hw : |(2272129193/5000000000 : ℝ)|=(2272129193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27500889/100000000 : ℝ)|^95 ≤ (5293424377839/25000000000000 : ℝ)^79
        have hw : |(-27500889/100000000 : ℝ)|=(27500889/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4676457843/10000000000 : ℝ)|^95 ≤ (40092651159339/100000000000000 : ℝ)^79
        have hw : |(-4676457843/10000000000 : ℝ)|=(4676457843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4594917949/10000000000 : ℝ)*x 0 + (5490615331/10000000000 : ℝ)*x 1 + (172908681/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4594917949/10000000000 : ℝ)^95 ≤ (19626746994831/50000000000000 : ℝ)^79 := by
    have hnat : (4594917949 : ℕ)^95*50000000000000^79 ≤ 19626746994831^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4594917949 10000000000 19626746994831 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490615331/10000000000 : ℝ)^95 ≤ (12156989551431/25000000000000 : ℝ)^79 := by
    have hnat : (5490615331 : ℕ)^95*25000000000000^79 ≤ 12156989551431^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490615331 10000000000 12156989551431 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172908681/1000000000 : ℝ)^95 ≤ (12118547786541/100000000000000 : ℝ)^79 := by
    have hnat : (172908681 : ℕ)^95*100000000000000^79 ≤ 12118547786541^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172908681 1000000000 12118547786541 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4594917949/10000000000 : ℝ), (5490615331/10000000000 : ℝ), (172908681/1000000000 : ℝ)] ![(19626746994831/50000000000000 : ℝ), (12156989551431/25000000000000 : ℝ), (12118547786541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4594917949/10000000000 : ℝ)|^95 ≤ (19626746994831/50000000000000 : ℝ)^79
        have hw : |(4594917949/10000000000 : ℝ)|=(4594917949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490615331/10000000000 : ℝ)|^95 ≤ (12156989551431/25000000000000 : ℝ)^79
        have hw : |(5490615331/10000000000 : ℝ)|=(5490615331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(172908681/1000000000 : ℝ)|^95 ≤ (12118547786541/100000000000000 : ℝ)^79
        have hw : |(172908681/1000000000 : ℝ)|=(172908681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329052_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (169090887/250000000 : ℝ)*x 0 + (1838710511/5000000000 : ℝ)*x 1 + (-579040763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169090887/250000000 : ℝ)^95 ≤ (62486515713957/100000000000000 : ℝ)^79 := by
    have hnat : (169090887 : ℕ)^95*100000000000000^79 ≤ 62486515713957^79*250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169090887 250000000 62486515713957 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1838710511/5000000000 : ℝ)^95 ≤ (30029778927067/100000000000000 : ℝ)^79 := by
    have hnat : (1838710511 : ℕ)^95*100000000000000^79 ≤ 30029778927067^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838710511 5000000000 30029778927067 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579040763/5000000000 : ℝ)^95 ≤ (3741852672673/50000000000000 : ℝ)^79 := by
    have hnat : (579040763 : ℕ)^95*50000000000000^79 ≤ 3741852672673^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579040763 5000000000 3741852672673 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(169090887/250000000 : ℝ), (1838710511/5000000000 : ℝ), (-579040763/5000000000 : ℝ)] ![(62486515713957/100000000000000 : ℝ), (30029778927067/100000000000000 : ℝ), (3741852672673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(169090887/250000000 : ℝ)|^95 ≤ (62486515713957/100000000000000 : ℝ)^79
        have hw : |(169090887/250000000 : ℝ)|=(169090887/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1838710511/5000000000 : ℝ)|^95 ≤ (30029778927067/100000000000000 : ℝ)^79
        have hw : |(1838710511/5000000000 : ℝ)|=(1838710511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-579040763/5000000000 : ℝ)|^95 ≤ (3741852672673/50000000000000 : ℝ)^79
        have hw : |(-579040763/5000000000 : ℝ)|=(579040763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329052 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-117895619/2000000000 : ℝ)*X 0 0+(1671985643/5000000000 : ℝ)*X 0 1+(-7423801309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4921194183/10000000000 : ℝ)*X 1 0+(-2166700639/10000000000 : ℝ)*X 1 1+(-4810195323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4921194459/10000000000 : ℝ)*X 2 0+(6146605737/10000000000 : ℝ)*X 2 1+(333455559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-653953839/5000000000 : ℝ)*X 0 0+(625563277/5000000000 : ℝ)*X 0 1+(-8575300881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((311090393/1000000000 : ℝ)*X 1 0+(-589692851/5000000000 : ℝ)*X 1 1+(-7237986201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((7777261/25000000 : ℝ)*X 2 0+(3926199361/5000000000 : ℝ)*X 2 1+(19484797/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((810449671/2000000000 : ℝ)*X 0 0+(7040967187/10000000000 : ℝ)*X 0 1+(-31219941/2000000000 : ℝ)*X 0 2+(810449671/2000000000 : ℝ)*X 1 0+(7040967187/10000000000 : ℝ)*X 1 1+(-31219941/2000000000 : ℝ)*X 1 2+(810449671/2000000000 : ℝ)*X 2 0+(7040967187/10000000000 : ℝ)*X 2 1+(-31219941/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-100067441/5000000000 : ℝ)*X 0 0+(911566957/5000000000 : ℝ)*X 0 1+(-441822433/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((425675429/2500000000 : ℝ)*X 1 0+(-2379695931/10000000000 : ℝ)*X 1 1+(-3730400977/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7132532867/10000000000 : ℝ)*X 2 0+(389692273/1000000000 : ℝ)*X 2 1+(5036541/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((4116216257/5000000000 : ℝ)*X 0 0+(1290931667/5000000000 : ℝ)*X 0 1+(-257934229/10000000000 : ℝ)*X 0 2+(4116216257/5000000000 : ℝ)*X 1 0+(1290931667/5000000000 : ℝ)*X 1 1+(-257934229/10000000000 : ℝ)*X 1 2+(4116216257/5000000000 : ℝ)*X 2 0+(1290931667/5000000000 : ℝ)*X 2 1+(-257934229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-2034669/2500000000 : ℝ)*X 0 0+(1157058829/2500000000 : ℝ)*X 0 1+(-821738343/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((6700260063/10000000000 : ℝ)*X 1 0+(-520040823/2500000000 : ℝ)*X 1 1+(-2954646547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((228614577/1000000000 : ℝ)*X 2 0+(119413379/156250000 : ℝ)*X 2 1+(1555472513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1132881969/1250000000 : ℝ)*X 0 0+(287960761/2000000000 : ℝ)*X 0 1+(-293043907/10000000000 : ℝ)*X 0 2+(1132881969/1250000000 : ℝ)*X 1 0+(287960761/2000000000 : ℝ)*X 1 1+(-293043907/10000000000 : ℝ)*X 1 2+(1132881969/1250000000 : ℝ)*X 2 0+(287960761/2000000000 : ℝ)*X 2 1+(-293043907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1774/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1774/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (33102533979368833315287/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1008710825651/1000000000000 : ℝ)*(base7) + (5860982267/1000000000000 : ℝ)*(base39) + (71224193863/1000000000000 : ℝ)*(base59) + (1750141429727/1000000000000 : ℝ)*(major_s0_0) + (1750141429727/1000000000000 : ℝ)*(major_s0_1) + (1750141429727/1000000000000 : ℝ)*(major_s0_2) + (213623/25000000000 : ℝ)*(sp_s0_0) + (681251/250000000000 : ℝ)*(sp_s0_1) + (2174324231593/1000000000000 : ℝ)*(sp_s0_7) + (2174342098969/1000000000000 : ℝ)*(sp_s0_8) + (543586900337/250000000000 : ℝ)*(sp_s0_9) + (1795800640959/1000000000000 : ℝ)*(sp_s0_13) + (3706209/250000000000 : ℝ)*(sp_s0_14) + (22219/8000000000 : ℝ)*(sp_s0_15) + (196772453827/250000000000 : ℝ)*(f.failure) + (543586900337/250000000000 : ℝ)*(f.sum) + (651864731781639/5000000000000000000000000000 : ℝ)*base63 + (3929809947858327/10000000000000000000000000000 : ℝ)*base65 + (1967268594858327/10000000000000000000000000000 : ℝ)*base67 + (5551239204281639/10000000000000000000000000000 : ℝ)*base69 + (1154826332069983/5000000000000000000000000000 : ℝ)*base71 + (35207120858327/10000000000000000000000000000 : ℝ)*base72 + (4735083406281639/10000000000000000000000000000 : ℝ)*base75 + (7039697462281639/10000000000000000000000000000 : ℝ)*base77 + (4889166247/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (4647/6250000000000000 : ℝ)*base86 + (4647/6250000000000000 : ℝ)*base88 + (4647/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28821/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28821/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1462672853345237535897/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (519924568289/500000000000 : ℝ)*(base7) + (1620246423/1000000000000 : ℝ)*(base39) + (30109650787/500000000000 : ℝ)*(base59) + (96642952709/62500000000 : ℝ)*(major_s0_0) + (96642952709/62500000000 : ℝ)*(major_s0_1) + (96642952709/62500000000 : ℝ)*(major_s0_2) + (140249/1000000000000 : ℝ)*(sp_s0_1) + (131797/125000000000 : ℝ)*(sp_s0_7) + (22195913/1000000000000 : ℝ)*(sp_s0_8) + (1841682679359/1000000000000 : ℝ)*(sp_s0_14) + (1841661397573/1000000000000 : ℝ)*(sp_s0_15) + (368336746747/200000000000 : ℝ)*(sp_s0_16) + (347049505453/200000000000 : ℝ)*(sp_s0_20) + (12231623/1000000000000 : ℝ)*(sp_s0_27) + (69541062231/100000000000 : ℝ)*(f.failure) + (368336746747/200000000000 : ℝ)*(f.sum) + (74504775728187/312500000000000000000000000 : ℝ)*base62 + (513094361968591/625000000000000000000000000 : ℝ)*base64 + (170139850343909/625000000000000000000000000 : ℝ)*base67 + (236911935790687/625000000000000000000000000 : ℝ)*base68 + (137803256348389/312500000000000000000000000 : ℝ)*base70 + (347789729031091/625000000000000000000000000 : ℝ)*base73 + (244050893290687/625000000000000000000000000 : ℝ)*base74 + (266345619790687/625000000000000000000000000 : ℝ)*base76 + (594148249/2500000000000000000000 : ℝ)*base79 + (941/2500000000000000 : ℝ)*base86 + (941/2500000000000000 : ℝ)*base88 + (941/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11533/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11533/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1580904405925778156427/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (404587354337/500000000000 : ℝ)*(base7) + (105296610809/250000000000 : ℝ)*(base39) + (11163/250000000000 : ℝ)*(base43) + (115453335543/1000000000000 : ℝ)*(base49) + (160410298251/500000000000 : ℝ)*(base59) + (3480333417/2000000000 : ℝ)*(major_s0_0) + (217520832981/125000000000 : ℝ)*(major_s0_1) + (3480333417/2000000000 : ℝ)*(major_s0_2) + (510081/200000000000 : ℝ)*(sp_s0_2) + (6133257/100000000000 : ℝ)*(sp_s0_9) + (453094614167/200000000000 : ℝ)*(sp_s0_21) + (2265473115487/1000000000000 : ℝ)*(sp_s0_22) + (113270459393/50000000000 : ℝ)*(sp_s0_23) + (1591778599957/1000000000000 : ℝ)*(sp_s0_27) + (391301945641/500000000000 : ℝ)*(f.failure) + (2265473115487/1000000000000 : ℝ)*(f.sum) + (1084883848960841/2500000000000000000000000000 : ℝ)*base62 + (2300624314017/20000000000000000000000000 : ℝ)*base65 + (170603008833781/1250000000000000000000000000 : ℝ)*base67 + (7836552714031/20000000000000000000000000 : ℝ)*base68 + (211446208993/10000000000000000000000000 : ℝ)*base71 + (6115455971983/20000000000000000000000000 : ℝ)*base73 + (663242242353483/1250000000000000000000000000 : ℝ)*base74 + (246168835969/20000000000000000000000000 : ℝ)*base77 + (1106126383415437/2500000000000000000000000000 : ℝ)*base79 + (12451/12500000000000000 : ℝ)*base86 + (12451/12500000000000000 : ℝ)*base88 + (12451/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (1774/3125 : ℝ) ^ (93/16 : ℝ) ≤ (3721578114112396043/100000000000000000000 : ℝ) := by
    have hpowers : (1774/3125 : ℝ)^93 ≤ (3721578114112396043/100000000000000000000 : ℝ)^16 := by
      have hnat : (1774 : ℕ)^93*100000000000000000000^16 ≤ 3721578114112396043^16*3125^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1774 3125 3721578114112396043 100000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1774/3125 : ℝ)) (X := (3721578114112396043/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (103721578114112396043/100000000000000000000 : ℝ) ≤ (10063062510387913/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (103721578114112396043/100000000000000000000 : ℝ)^16 ≤ (10063062510387913/10000000000000000 : ℝ)^93 := by
      have hnat : (103721578114112396043 : ℕ)^16*10000000000000000^93 ≤ 10063062510387913^93*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103721578114112396043 100000000000000000000 10063062510387913 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10063062510387913/10000000000000000 : ℝ)) (X := (103721578114112396043/100000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (53721578114112396043/50000000000000000000 : ℝ) ≤ (2024855718869169/2000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (53721578114112396043/50000000000000000000 : ℝ)^16 ≤ (2024855718869169/2000000000000000 : ℝ)^93 := by
      have hnat : (53721578114112396043 : ℕ)^16*2000000000000000^93 ≤ 2024855718869169^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53721578114112396043 50000000000000000000 2024855718869169 2000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2024855718869169/2000000000000000 : ℝ)) (X := (53721578114112396043/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(63062510387913/5676800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(15304020989483/1419200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1774/3125 : ℝ)) (alpha := (63062510387913/5676800000000000 : ℝ)) (beta := (15304020989483/1419200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1774/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(63062510387913/5676800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(15304020989483/1419200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (28821/50000 : ℝ) ^ (93/16 : ℝ) ≤ (4067201380734573969/100000000000000000000 : ℝ) := by
    have hpowers : (28821/50000 : ℝ)^93 ≤ (4067201380734573969/100000000000000000000 : ℝ)^16 := by
      have hnat : (28821 : ℕ)^93*100000000000000000000^16 ≤ 4067201380734573969^16*50000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28821 50000 4067201380734573969 100000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28821/50000 : ℝ)) (X := (4067201380734573969/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (104067201380734573969/100000000000000000000 : ℝ) ≤ (2013764715051789/2000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (104067201380734573969/100000000000000000000 : ℝ)^16 ≤ (2013764715051789/2000000000000000 : ℝ)^93 := by
      have hnat : (104067201380734573969 : ℕ)^16*2000000000000000^93 ≤ 2013764715051789^93*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104067201380734573969 100000000000000000000 2013764715051789 2000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2013764715051789/2000000000000000 : ℝ)) (X := (104067201380734573969/100000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (54067201380734573969/50000000000000000000 : ℝ) ≤ (10135454986316671/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (54067201380734573969/50000000000000000000 : ℝ)^16 ≤ (10135454986316671/10000000000000000 : ℝ)^93 := by
      have hnat : (54067201380734573969 : ℕ)^16*10000000000000000^93 ≤ 10135454986316671^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54067201380734573969 50000000000000000000 10135454986316671 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10135454986316671/10000000000000000 : ℝ)) (X := (54067201380734573969/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1058824234753/88680000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(33315705528863/2882100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (28821/50000 : ℝ)) (alpha := (1058824234753/88680000000000 : ℝ)) (beta := (33315705528863/2882100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (28821/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1058824234753/88680000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(33315705528863/2882100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (11533/25000 : ℝ) ^ (93/16 : ℝ) ≤ (4457314347480197/400000000000000000 : ℝ) := by
    have hpowers : (11533/25000 : ℝ)^93 ≤ (4457314347480197/400000000000000000 : ℝ)^16 := by
      have hnat : (11533 : ℕ)^93*400000000000000000^16 ≤ 4457314347480197^16*25000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11533 25000 4457314347480197 400000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11533/25000 : ℝ)) (X := (4457314347480197/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (404457314347480197/400000000000000000 : ℝ) ≤ (78274089076543/78125000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (404457314347480197/400000000000000000 : ℝ)^16 ≤ (78274089076543/78125000000000 : ℝ)^93 := by
      have hnat : (404457314347480197 : ℕ)^16*78125000000000^93 ≤ 78274089076543^93*400000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        404457314347480197 400000000000000000 78274089076543 78125000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78274089076543/78125000000000 : ℝ)) (X := (404457314347480197/400000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (204457314347480197/200000000000000000 : ℝ) ≤ (10037993464444201/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (204457314347480197/200000000000000000 : ℝ)^16 ≤ (10037993464444201/10000000000000000 : ℝ)^93 := by
      have hnat : (204457314347480197 : ℕ)^16*10000000000000000^93 ≤ 10037993464444201^93*200000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        204457314347480197 200000000000000000 10037993464444201 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10037993464444201/10000000000000000 : ℝ)) (X := (204457314347480197/200000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(149089076543/36040625000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(18910062646697/4613200000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (11533/25000 : ℝ)) (alpha := (149089076543/36040625000000 : ℝ)) (beta := (18910062646697/4613200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (11533/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(149089076543/36040625000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(18910062646697/4613200000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-37408591/200000000 : ℝ)*X 0 0+(3669994209/10000000000 : ℝ)*X 0 1+(-1560183491/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2272129193/5000000000 : ℝ)*X 1 0+(-27500889/100000000 : ℝ)*X 1 1+(-4676457843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4594917949/10000000000 : ℝ)*X 2 0+(5490615331/10000000000 : ℝ)*X 2 1+(172908681/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((169090887/250000000 : ℝ)*X 0 0+(1838710511/5000000000 : ℝ)*X 0 1+(-579040763/5000000000 : ℝ)*X 0 2+(169090887/250000000 : ℝ)*X 1 0+(1838710511/5000000000 : ℝ)*X 1 1+(-579040763/5000000000 : ℝ)*X 1 2+(169090887/250000000 : ℝ)*X 2 0+(1838710511/5000000000 : ℝ)*X 2 1+(-579040763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329052_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-1553525228650526720092382708328327/151196015380000000000000000000000 : ℝ) := by norm_num
    linear_combination (15249/1000000000000 : ℝ)*(base8) + (2421/1000000000000 : ℝ)*(base11) + (96420282987/200000000000 : ℝ)*(base39) + (6011/1000000000000 : ℝ)*(base43) + (3977195017/1000000000000 : ℝ)*(base49) + (33/50000000000 : ℝ)*(base50) + (589741431367/1000000000000 : ℝ)*(base59) + (55589/25000 : ℝ)*(major_s1_0) + (2223559993989/1000000000000 : ℝ)*(major_s1_1) + (55589/25000 : ℝ)*(major_s1_2) + (1712484741393/500000000000 : ℝ)*(sp_s1_0) + (3424969506467/1000000000000 : ℝ)*(sp_s1_1) + (3424969498117/1000000000000 : ℝ)*(sp_s1_2) + (50000000117/50000000000 : ℝ)*(sp_s1_6) + (3424969506467/1000000000000 : ℝ)*(f.sum) + (78073948696455813/340915480000000000000000000000 : ℝ)*base62 + (1740640181559/57665000000000000000000000 : ℝ)*base65 + (6559749573911/960700000000000000000000000 : ℝ)*base67 + (3263427996623/57665000000000000000000000 : ℝ)*base68 + (88987175292633/639360687500000000000000000 : ℝ)*base70 + (3864028720873/8870000000000000000000000 : ℝ)*base72 + (6068464955509/29560000000000000000000000 : ℝ)*base74 + (4572302772109/8870000000000000000000000 : ℝ)*base76 + (14335607644119603/852140900000000000000000000000 : ℝ)*base78 + (2339/1000000000000 : ℝ)*base84 + (117/50000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p029_b025 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 52 ≤ c.val) (hhi : c.val < 56)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=52 ∨ c=53 ∨ c=54 ∨ c=55 := by omega
  rcases hc with rfl|rfl|rfl|rfl
  · exact collision_c329052 p hpa (by linarith only [hpb]) X hX
  · exact collision_c329053 p hpa (by linarith only [hpb]) X hX
  · exact collision_c329054 p hpa (by linarith only [hpb]) X hX
  · exact collision_c329055 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 52 ≤ c.val) (hhi : c.val < 56)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b025 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
