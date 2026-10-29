-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_b027
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:14:13.738091+00:00
-- url     : https://prove2.me/submissions/606f0f58-e13d-429f-9555-4078b6da479e

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317059_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317059_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317059_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317060_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317060_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317060_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317061_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317061_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317061_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317061_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317062_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317062_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317062_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c317059 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : False := by
  have h0 := collision_c317059_s0 p hpa hpb X hX
  have h1 := collision_c317059_s1 p hpa hpb X hX h0
  exact collision_c317059_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c317060 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]]) : False := by
  have h0 := collision_c317060_s0 p hpa hpb X hX
  have h1 := collision_c317060_s1 p hpa hpb X hX h0
  exact collision_c317060_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c317061 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]]) : False := by
  have h0 := collision_c317061_s0 p hpa hpb X hX
  have h1 := collision_c317061_s1 p hpa hpb X hX h0
  have h2 := collision_c317061_s2 p hpa hpb X hX h1
  exact collision_c317061_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c317062 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]]) : False := by
  have h0 := collision_c317062_s0 p hpa hpb X hX
  have h1 := collision_c317062_s1 p hpa hpb X hX h0
  exact collision_c317062_s2 p hpa hpb X hX h1

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
theorem collision_support_c317058_s0_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-745391727/2500000000 : ℝ)*x 0 + (596312937/2000000000 : ℝ)*x 1 + (-1267964211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (745391727/2500000000 : ℝ)^39 ≤ (5454530290389/25000000000000 : ℝ)^31 := by
    have hnat : (745391727 : ℕ)^39*25000000000000^31 ≤ 5454530290389^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745391727 2500000000 5454530290389 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596312937/2000000000 : ℝ)^39 ≤ (21818100696397/100000000000000 : ℝ)^31 := by
    have hnat : (596312937 : ℕ)^39*100000000000000^31 ≤ 21818100696397^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596312937 2000000000 21818100696397 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1267964211/2000000000 : ℝ)^39 ≤ (3522736132353/6250000000000 : ℝ)^31 := by
    have hnat : (1267964211 : ℕ)^39*6250000000000^31 ≤ 3522736132353^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267964211 2000000000 3522736132353 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-745391727/2500000000 : ℝ), (596312937/2000000000 : ℝ), (-1267964211/2000000000 : ℝ)] ![(5454530290389/25000000000000 : ℝ), (21818100696397/100000000000000 : ℝ), (3522736132353/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-745391727/2500000000 : ℝ)|^39 ≤ (5454530290389/25000000000000 : ℝ)^31
        have hw : |(-745391727/2500000000 : ℝ)|=(745391727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(596312937/2000000000 : ℝ)|^39 ≤ (21818100696397/100000000000000 : ℝ)^31
        have hw : |(596312937/2000000000 : ℝ)|=(596312937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1267964211/2000000000 : ℝ)|^39 ≤ (3522736132353/6250000000000 : ℝ)^31
        have hw : |(-1267964211/2000000000 : ℝ)|=(1267964211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s0_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (745392753/2500000000 : ℝ)*x 0 + (-2981567483/10000000000 : ℝ)*x 1 + (-50718523/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (745392753/2500000000 : ℝ)^39 ≤ (21818158943399/100000000000000 : ℝ)^31 := by
    have hnat : (745392753 : ℕ)^39*100000000000000^31 ≤ 21818158943399^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745392753 2500000000 21818158943399 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2981567483/10000000000 : ℝ)^39 ≤ (2727265806883/12500000000000 : ℝ)^31 := by
    have hnat : (2981567483 : ℕ)^39*12500000000000^31 ≤ 2727265806883^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2981567483 10000000000 2727265806883 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50718523/80000000 : ℝ)^39 ≤ (11272742917663/20000000000000 : ℝ)^31 := by
    have hnat : (50718523 : ℕ)^39*20000000000000^31 ≤ 11272742917663^31*80000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50718523 80000000 11272742917663 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(745392753/2500000000 : ℝ), (-2981567483/10000000000 : ℝ), (-50718523/80000000 : ℝ)] ![(21818158943399/100000000000000 : ℝ), (2727265806883/12500000000000 : ℝ), (11272742917663/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(745392753/2500000000 : ℝ)|^39 ≤ (21818158943399/100000000000000 : ℝ)^31
        have hw : |(745392753/2500000000 : ℝ)|=(745392753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2981567483/10000000000 : ℝ)|^39 ≤ (2727265806883/12500000000000 : ℝ)^31
        have hw : |(-2981567483/10000000000 : ℝ)|=(2981567483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50718523/80000000 : ℝ)|^39 ≤ (11272742917663/20000000000000 : ℝ)^31
        have hw : |(-50718523/80000000 : ℝ)|=(50718523/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s0_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-201027577/1000000000 : ℝ)*x 0 + (374395231/5000000000 : ℝ)*x 1 + (-4306581863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201027577/1000000000 : ℝ)^39 ≤ (6643862653257/50000000000000 : ℝ)^31 := by
    have hnat : (201027577 : ℕ)^39*50000000000000^31 ≤ 6643862653257^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201027577 1000000000 6643862653257 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374395231/5000000000 : ℝ)^39 ≤ (3835947372703/100000000000000 : ℝ)^31 := by
    have hnat : (374395231 : ℕ)^39*100000000000000^31 ≤ 3835947372703^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374395231 5000000000 3835947372703 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4306581863/5000000000 : ℝ)^39 ≤ (82876327316097/100000000000000 : ℝ)^31 := by
    have hnat : (4306581863 : ℕ)^39*100000000000000^31 ≤ 82876327316097^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306581863 5000000000 82876327316097 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-201027577/1000000000 : ℝ), (374395231/5000000000 : ℝ), (-4306581863/5000000000 : ℝ)] ![(6643862653257/50000000000000 : ℝ), (3835947372703/100000000000000 : ℝ), (82876327316097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-201027577/1000000000 : ℝ)|^39 ≤ (6643862653257/50000000000000 : ℝ)^31
        have hw : |(-201027577/1000000000 : ℝ)|=(201027577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(374395231/5000000000 : ℝ)|^39 ≤ (3835947372703/100000000000000 : ℝ)^31
        have hw : |(374395231/5000000000 : ℝ)|=(374395231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4306581863/5000000000 : ℝ)|^39 ≤ (82876327316097/100000000000000 : ℝ)^31
        have hw : |(-4306581863/5000000000 : ℝ)|=(4306581863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s0_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1571593427/10000000000 : ℝ)*x 0 + (-1258969293/10000000000 : ℝ)*x 1 + (-2153291929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1571593427/10000000000 : ℝ)^39 ≤ (1218580264733/12500000000000 : ℝ)^31 := by
    have hnat : (1571593427 : ℕ)^39*12500000000000^31 ≤ 1218580264733^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1571593427 10000000000 1218580264733 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1258969293/10000000000 : ℝ)^39 ≤ (7374982251489/100000000000000 : ℝ)^31 := by
    have hnat : (1258969293 : ℕ)^39*100000000000000^31 ≤ 7374982251489^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1258969293 10000000000 7374982251489 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153291929/2500000000 : ℝ)^39 ≤ (82876375615707/100000000000000 : ℝ)^31 := by
    have hnat : (2153291929 : ℕ)^39*100000000000000^31 ≤ 82876375615707^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153291929 2500000000 82876375615707 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1571593427/10000000000 : ℝ), (-1258969293/10000000000 : ℝ), (-2153291929/2500000000 : ℝ)] ![(1218580264733/12500000000000 : ℝ), (7374982251489/100000000000000 : ℝ), (82876375615707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1571593427/10000000000 : ℝ)|^39 ≤ (1218580264733/12500000000000 : ℝ)^31
        have hw : |(1571593427/10000000000 : ℝ)|=(1571593427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1258969293/10000000000 : ℝ)|^39 ≤ (7374982251489/100000000000000 : ℝ)^31
        have hw : |(-1258969293/10000000000 : ℝ)|=(1258969293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2153291929/2500000000 : ℝ)|^39 ≤ (82876375615707/100000000000000 : ℝ)^31
        have hw : |(-2153291929/2500000000 : ℝ)|=(2153291929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s0_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (741006513/2000000000 : ℝ)*x 0 + (837646399/1250000000 : ℝ)*x 1 + (1716133167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (741006513/2000000000 : ℝ)^39 ≤ (28675602611019/100000000000000 : ℝ)^31 := by
    have hnat : (741006513 : ℕ)^39*100000000000000^31 ≤ 28675602611019^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741006513 2000000000 28675602611019 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (837646399/1250000000 : ℝ)^39 ≤ (12086940279517/20000000000000 : ℝ)^31 := by
    have hnat : (837646399 : ℕ)^39*20000000000000^31 ≤ 12086940279517^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837646399 1250000000 12086940279517 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1716133167/10000000000 : ℝ)^39 ≤ (435587839067/4000000000000 : ℝ)^31 := by
    have hnat : (1716133167 : ℕ)^39*4000000000000^31 ≤ 435587839067^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716133167 10000000000 435587839067 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(741006513/2000000000 : ℝ), (837646399/1250000000 : ℝ), (1716133167/10000000000 : ℝ)] ![(28675602611019/100000000000000 : ℝ), (12086940279517/20000000000000 : ℝ), (435587839067/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(741006513/2000000000 : ℝ)|^39 ≤ (28675602611019/100000000000000 : ℝ)^31
        have hw : |(741006513/2000000000 : ℝ)|=(741006513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(837646399/1250000000 : ℝ)|^39 ≤ (12086940279517/20000000000000 : ℝ)^31
        have hw : |(837646399/1250000000 : ℝ)|=(837646399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1716133167/10000000000 : ℝ)|^39 ≤ (435587839067/4000000000000 : ℝ)^31
        have hw : |(1716133167/10000000000 : ℝ)|=(1716133167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s0_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1789508039/10000000000 : ℝ)*x 0 + (1815258301/2000000000 : ℝ)*x 1 + (-508101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1789508039/10000000000 : ℝ)^39 ≤ (2295729533719/20000000000000 : ℝ)^31 := by
    have hnat : (1789508039 : ℕ)^39*20000000000000^31 ≤ 2295729533719^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789508039 10000000000 2295729533719 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1815258301/2000000000 : ℝ)^39 ≤ (88520956217043/100000000000000 : ℝ)^31 := by
    have hnat : (1815258301 : ℕ)^39*100000000000000^31 ≤ 88520956217043^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815258301 2000000000 88520956217043 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508101/10000000000 : ℝ)^39 ≤ (99025749/25000000000000 : ℝ)^31 := by
    have hnat : (508101 : ℕ)^39*25000000000000^31 ≤ 99025749^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508101 10000000000 99025749 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1789508039/10000000000 : ℝ), (1815258301/2000000000 : ℝ), (-508101/10000000000 : ℝ)] ![(2295729533719/20000000000000 : ℝ), (88520956217043/100000000000000 : ℝ), (99025749/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1789508039/10000000000 : ℝ)|^39 ≤ (2295729533719/20000000000000 : ℝ)^31
        have hw : |(1789508039/10000000000 : ℝ)|=(1789508039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1815258301/2000000000 : ℝ)|^39 ≤ (88520956217043/100000000000000 : ℝ)^31
        have hw : |(1815258301/2000000000 : ℝ)|=(1815258301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508101/10000000000 : ℝ)|^39 ≤ (99025749/25000000000000 : ℝ)^31
        have hw : |(-508101/10000000000 : ℝ)|=(508101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s0_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-300744757/2500000000 : ℝ)*x 0 + (1949907333/10000000000 : ℝ)*x 1 + (-4197644199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (300744757/2500000000 : ℝ)^39 ≤ (3482373111379/50000000000000 : ℝ)^31 := by
    have hnat : (300744757 : ℕ)^39*50000000000000^31 ≤ 3482373111379^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300744757 2500000000 3482373111379 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1949907333/10000000000 : ℝ)^39 ≤ (6393840176367/50000000000000 : ℝ)^31 := by
    have hnat : (1949907333 : ℕ)^39*50000000000000^31 ≤ 6393840176367^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949907333 10000000000 6393840176367 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4197644199/5000000000 : ℝ)^39 ≤ (40123786706161/50000000000000 : ℝ)^31 := by
    have hnat : (4197644199 : ℕ)^39*50000000000000^31 ≤ 40123786706161^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197644199 5000000000 40123786706161 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-300744757/2500000000 : ℝ), (1949907333/10000000000 : ℝ), (-4197644199/5000000000 : ℝ)] ![(3482373111379/50000000000000 : ℝ), (6393840176367/50000000000000 : ℝ), (40123786706161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-300744757/2500000000 : ℝ)|^39 ≤ (3482373111379/50000000000000 : ℝ)^31
        have hw : |(-300744757/2500000000 : ℝ)|=(300744757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1949907333/10000000000 : ℝ)|^39 ≤ (6393840176367/50000000000000 : ℝ)^31
        have hw : |(1949907333/10000000000 : ℝ)|=(1949907333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4197644199/5000000000 : ℝ)|^39 ≤ (40123786706161/50000000000000 : ℝ)^31
        have hw : |(-4197644199/5000000000 : ℝ)|=(4197644199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s0_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (601489123/5000000000 : ℝ)*x 0 + (-389981213/2000000000 : ℝ)*x 1 + (-8395289741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (601489123/5000000000 : ℝ)^39 ≤ (696474052693/10000000000000 : ℝ)^31 := by
    have hnat : (601489123 : ℕ)^39*10000000000000^31 ≤ 696474052693^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601489123 5000000000 696474052693 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389981213/2000000000 : ℝ)^39 ≤ (1278766989109/10000000000000 : ℝ)^31 := by
    have hnat : (389981213 : ℕ)^39*10000000000000^31 ≤ 1278766989109^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389981213 2000000000 1278766989109 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8395289741/10000000000 : ℝ)^39 ≤ (80247589562423/100000000000000 : ℝ)^31 := by
    have hnat : (8395289741 : ℕ)^39*100000000000000^31 ≤ 80247589562423^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8395289741 10000000000 80247589562423 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(601489123/5000000000 : ℝ), (-389981213/2000000000 : ℝ), (-8395289741/10000000000 : ℝ)] ![(696474052693/10000000000000 : ℝ), (1278766989109/10000000000000 : ℝ), (80247589562423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(601489123/5000000000 : ℝ)|^39 ≤ (696474052693/10000000000000 : ℝ)^31
        have hw : |(601489123/5000000000 : ℝ)|=(601489123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389981213/2000000000 : ℝ)|^39 ≤ (1278766989109/10000000000000 : ℝ)^31
        have hw : |(-389981213/2000000000 : ℝ)|=(389981213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8395289741/10000000000 : ℝ)|^39 ≤ (80247589562423/100000000000000 : ℝ)^31
        have hw : |(-8395289741/10000000000 : ℝ)|=(8395289741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s0_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7653342177/10000000000 : ℝ)*x 0 + (1596989069/5000000000 : ℝ)*x 1 + (178358367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7653342177/10000000000 : ℝ)^39 ≤ (71429437338737/100000000000000 : ℝ)^31 := by
    have hnat : (7653342177 : ℕ)^39*100000000000000^31 ≤ 71429437338737^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7653342177 10000000000 71429437338737 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1596989069/5000000000 : ℝ)^39 ≤ (2973908580163/12500000000000 : ℝ)^31 := by
    have hnat : (1596989069 : ℕ)^39*12500000000000^31 ≤ 2973908580163^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596989069 5000000000 2973908580163 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (178358367/2000000000 : ℝ)^39 ≤ (477929400619/10000000000000 : ℝ)^31 := by
    have hnat : (178358367 : ℕ)^39*10000000000000^31 ≤ 477929400619^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178358367 2000000000 477929400619 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7653342177/10000000000 : ℝ), (1596989069/5000000000 : ℝ), (178358367/2000000000 : ℝ)] ![(71429437338737/100000000000000 : ℝ), (2973908580163/12500000000000 : ℝ), (477929400619/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7653342177/10000000000 : ℝ)|^39 ≤ (71429437338737/100000000000000 : ℝ)^31
        have hw : |(7653342177/10000000000 : ℝ)|=(7653342177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1596989069/5000000000 : ℝ)|^39 ≤ (2973908580163/12500000000000 : ℝ)^31
        have hw : |(1596989069/5000000000 : ℝ)|=(1596989069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(178358367/2000000000 : ℝ)|^39 ≤ (477929400619/10000000000000 : ℝ)^31
        have hw : |(178358367/2000000000 : ℝ)|=(178358367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s0_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-21807127/39062500 : ℝ)*x 0 + (2156871601/10000000000 : ℝ)*x 1 + (-4581136819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21807127/39062500 : ℝ)^39 ≤ (960586309477/2000000000000 : ℝ)^31 := by
    have hnat : (21807127 : ℕ)^39*2000000000000^31 ≤ 960586309477^31*39062500^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21807127 39062500 960586309477 2000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156871601/10000000000 : ℝ)^39 ≤ (14518039729853/100000000000000 : ℝ)^31 := by
    have hnat : (2156871601 : ℕ)^39*100000000000000^31 ≤ 14518039729853^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156871601 10000000000 14518039729853 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4581136819/10000000000 : ℝ)^39 ≤ (1170395149337/3125000000000 : ℝ)^31 := by
    have hnat : (4581136819 : ℕ)^39*3125000000000^31 ≤ 1170395149337^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4581136819 10000000000 1170395149337 3125000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21807127/39062500 : ℝ), (2156871601/10000000000 : ℝ), (-4581136819/10000000000 : ℝ)] ![(960586309477/2000000000000 : ℝ), (14518039729853/100000000000000 : ℝ), (1170395149337/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21807127/39062500 : ℝ)|^39 ≤ (960586309477/2000000000000 : ℝ)^31
        have hw : |(-21807127/39062500 : ℝ)|=(21807127/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2156871601/10000000000 : ℝ)|^39 ≤ (14518039729853/100000000000000 : ℝ)^31
        have hw : |(2156871601/10000000000 : ℝ)|=(2156871601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4581136819/10000000000 : ℝ)|^39 ≤ (1170395149337/3125000000000 : ℝ)^31
        have hw : |(-4581136819/10000000000 : ℝ)|=(4581136819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s0_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1103360153/10000000000 : ℝ)*x 0 + (-5421711/40000000 : ℝ)*x 1 + (-8842354033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103360153/10000000000 : ℝ)^39 ≤ (1561768310767/25000000000000 : ℝ)^31 := by
    have hnat : (1103360153 : ℕ)^39*25000000000000^31 ≤ 1561768310767^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103360153 10000000000 1561768310767 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421711/40000000 : ℝ)^39 ≤ (4046374603861/50000000000000 : ℝ)^31 := by
    have hnat : (5421711 : ℕ)^39*50000000000000^31 ≤ 4046374603861^31*40000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421711 40000000 4046374603861 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8842354033/10000000000 : ℝ)^39 ≤ (8566017753069/10000000000000 : ℝ)^31 := by
    have hnat : (8842354033 : ℕ)^39*10000000000000^31 ≤ 8566017753069^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8842354033 10000000000 8566017753069 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103360153/10000000000 : ℝ), (-5421711/40000000 : ℝ), (-8842354033/10000000000 : ℝ)] ![(1561768310767/25000000000000 : ℝ), (4046374603861/50000000000000 : ℝ), (8566017753069/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103360153/10000000000 : ℝ)|^39 ≤ (1561768310767/25000000000000 : ℝ)^31
        have hw : |(1103360153/10000000000 : ℝ)|=(1103360153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5421711/40000000 : ℝ)|^39 ≤ (4046374603861/50000000000000 : ℝ)^31
        have hw : |(-5421711/40000000 : ℝ)|=(5421711/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8842354033/10000000000 : ℝ)|^39 ≤ (8566017753069/10000000000000 : ℝ)^31
        have hw : |(-8842354033/10000000000 : ℝ)|=(8842354033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s0_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3935896679/5000000000 : ℝ)*x 0 + (1339342213/5000000000 : ℝ)*x 1 + (1198060469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3935896679/5000000000 : ℝ)^39 ≤ (9250474360051/12500000000000 : ℝ)^31 := by
    have hnat : (3935896679 : ℕ)^39*12500000000000^31 ≤ 9250474360051^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3935896679 5000000000 9250474360051 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1339342213/5000000000 : ℝ)^39 ≤ (2383408138619/12500000000000 : ℝ)^31 := by
    have hnat : (1339342213 : ℕ)^39*12500000000000^31 ≤ 2383408138619^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339342213 5000000000 2383408138619 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198060469/10000000000 : ℝ)^39 ≤ (1385787998067/20000000000000 : ℝ)^31 := by
    have hnat : (1198060469 : ℕ)^39*20000000000000^31 ≤ 1385787998067^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198060469 10000000000 1385787998067 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3935896679/5000000000 : ℝ), (1339342213/5000000000 : ℝ), (1198060469/10000000000 : ℝ)] ![(9250474360051/12500000000000 : ℝ), (2383408138619/12500000000000 : ℝ), (1385787998067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3935896679/5000000000 : ℝ)|^39 ≤ (9250474360051/12500000000000 : ℝ)^31
        have hw : |(3935896679/5000000000 : ℝ)|=(3935896679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1339342213/5000000000 : ℝ)|^39 ≤ (2383408138619/12500000000000 : ℝ)^31
        have hw : |(1339342213/5000000000 : ℝ)|=(1339342213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198060469/10000000000 : ℝ)|^39 ≤ (1385787998067/20000000000000 : ℝ)^31
        have hw : |(1198060469/10000000000 : ℝ)|=(1198060469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s0_27 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1001405329/10000000000 : ℝ)*x 0 + (238947587/250000000 : ℝ)*x 1 + (-117671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001405329/10000000000 : ℝ)^39 ≤ (2764857669743/50000000000000 : ℝ)^31 := by
    have hnat : (1001405329 : ℕ)^39*50000000000000^31 ≤ 2764857669743^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001405329 10000000000 2764857669743 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238947587/250000000 : ℝ)^39 ≤ (94470221761621/100000000000000 : ℝ)^31 := by
    have hnat : (238947587 : ℕ)^39*100000000000000^31 ≤ 94470221761621^31*250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238947587 250000000 94470221761621 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117671/10000000000 : ℝ)^39 ≤ (62890369/100000000000000 : ℝ)^31 := by
    have hnat : (117671 : ℕ)^39*100000000000000^31 ≤ 62890369^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117671 10000000000 62890369 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1001405329/10000000000 : ℝ), (238947587/250000000 : ℝ), (-117671/10000000000 : ℝ)] ![(2764857669743/50000000000000 : ℝ), (94470221761621/100000000000000 : ℝ), (62890369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1001405329/10000000000 : ℝ)|^39 ≤ (2764857669743/50000000000000 : ℝ)^31
        have hw : |(1001405329/10000000000 : ℝ)|=(1001405329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238947587/250000000 : ℝ)|^39 ≤ (94470221761621/100000000000000 : ℝ)^31
        have hw : |(238947587/250000000 : ℝ)|=(238947587/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117671/10000000000 : ℝ)|^39 ≤ (62890369/100000000000000 : ℝ)^31
        have hw : |(-117671/10000000000 : ℝ)|=(117671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s1_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1687460091/5000000000 : ℝ)*x 0 + (1660707133/5000000000 : ℝ)*x 1 + (-1429734127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1687460091/5000000000 : ℝ)^39 ≤ (5099822394471/20000000000000 : ℝ)^31 := by
    have hnat : (1687460091 : ℕ)^39*20000000000000^31 ≤ 5099822394471^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687460091 5000000000 5099822394471 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1660707133/5000000000 : ℝ)^39 ≤ (999662732059/4000000000000 : ℝ)^31 := by
    have hnat : (1660707133 : ℕ)^39*4000000000000^31 ≤ 999662732059^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660707133 5000000000 999662732059 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1429734127/2500000000 : ℝ)^39 ≤ (49509319709461/100000000000000 : ℝ)^31 := by
    have hnat : (1429734127 : ℕ)^39*100000000000000^31 ≤ 49509319709461^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429734127 2500000000 49509319709461 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1687460091/5000000000 : ℝ), (1660707133/5000000000 : ℝ), (-1429734127/2500000000 : ℝ)] ![(5099822394471/20000000000000 : ℝ), (999662732059/4000000000000 : ℝ), (49509319709461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1687460091/5000000000 : ℝ)|^39 ≤ (5099822394471/20000000000000 : ℝ)^31
        have hw : |(-1687460091/5000000000 : ℝ)|=(1687460091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1660707133/5000000000 : ℝ)|^39 ≤ (999662732059/4000000000000 : ℝ)^31
        have hw : |(1660707133/5000000000 : ℝ)|=(1660707133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1429734127/2500000000 : ℝ)|^39 ≤ (49509319709461/100000000000000 : ℝ)^31
        have hw : |(-1429734127/2500000000 : ℝ)|=(1429734127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s1_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (633955989/2000000000 : ℝ)*x 0 + (-3117504287/10000000000 : ℝ)*x 1 + (-3034808639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (633955989/2000000000 : ℝ)^39 ≤ (11782364045809/50000000000000 : ℝ)^31 := by
    have hnat : (633955989 : ℕ)^39*50000000000000^31 ≤ 11782364045809^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633955989 2000000000 11782364045809 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117504287/10000000000 : ℝ)^39 ≤ (23076855097303/100000000000000 : ℝ)^31 := by
    have hnat : (3117504287 : ℕ)^39*100000000000000^31 ≤ 23076855097303^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117504287 10000000000 23076855097303 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3034808639/5000000000 : ℝ)^39 ≤ (13339604197177/25000000000000 : ℝ)^31 := by
    have hnat : (3034808639 : ℕ)^39*25000000000000^31 ≤ 13339604197177^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3034808639 5000000000 13339604197177 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(633955989/2000000000 : ℝ), (-3117504287/10000000000 : ℝ), (-3034808639/5000000000 : ℝ)] ![(11782364045809/50000000000000 : ℝ), (23076855097303/100000000000000 : ℝ), (13339604197177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(633955989/2000000000 : ℝ)|^39 ≤ (11782364045809/50000000000000 : ℝ)^31
        have hw : |(633955989/2000000000 : ℝ)|=(633955989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3117504287/10000000000 : ℝ)|^39 ≤ (23076855097303/100000000000000 : ℝ)^31
        have hw : |(-3117504287/10000000000 : ℝ)|=(3117504287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3034808639/5000000000 : ℝ)|^39 ≤ (13339604197177/25000000000000 : ℝ)^31
        have hw : |(-3034808639/5000000000 : ℝ)|=(3034808639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s1_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5405337619/10000000000 : ℝ)*x 0 + (5255671479/10000000000 : ℝ)*x 1 + (1522099687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5405337619/10000000000 : ℝ)^39 ≤ (46118362325289/100000000000000 : ℝ)^31 := by
    have hnat : (5405337619 : ℕ)^39*100000000000000^31 ≤ 46118362325289^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405337619 10000000000 46118362325289 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255671479/10000000000 : ℝ)^39 ≤ (44517653505039/100000000000000 : ℝ)^31 := by
    have hnat : (5255671479 : ℕ)^39*100000000000000^31 ≤ 44517653505039^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255671479 10000000000 44517653505039 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1522099687/10000000000 : ℝ)^39 ≤ (2340996037851/25000000000000 : ℝ)^31 := by
    have hnat : (1522099687 : ℕ)^39*25000000000000^31 ≤ 2340996037851^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522099687 10000000000 2340996037851 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5405337619/10000000000 : ℝ), (5255671479/10000000000 : ℝ), (1522099687/10000000000 : ℝ)] ![(46118362325289/100000000000000 : ℝ), (44517653505039/100000000000000 : ℝ), (2340996037851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5405337619/10000000000 : ℝ)|^39 ≤ (46118362325289/100000000000000 : ℝ)^31
        have hw : |(5405337619/10000000000 : ℝ)|=(5405337619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255671479/10000000000 : ℝ)|^39 ≤ (44517653505039/100000000000000 : ℝ)^31
        have hw : |(5255671479/10000000000 : ℝ)|=(5255671479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1522099687/10000000000 : ℝ)|^39 ≤ (2340996037851/25000000000000 : ℝ)^31
        have hw : |(1522099687/10000000000 : ℝ)|=(1522099687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317058_s1_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4910232713/10000000000 : ℝ)*x 0 + (1444016431/2500000000 : ℝ)*x 1 + (-1474800463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4910232713/10000000000 : ℝ)^39 ≤ (2043414572533/5000000000000 : ℝ)^31 := by
    have hnat : (4910232713 : ℕ)^39*5000000000000^31 ≤ 2043414572533^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4910232713 10000000000 2043414572533 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1444016431/2500000000 : ℝ)^39 ≤ (6266540478221/12500000000000 : ℝ)^31 := by
    have hnat : (1444016431 : ℕ)^39*12500000000000^31 ≤ 6266540478221^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444016431 2500000000 6266540478221 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1474800463/10000000000 : ℝ)^39 ≤ (4499692354643/50000000000000 : ℝ)^31 := by
    have hnat : (1474800463 : ℕ)^39*50000000000000^31 ≤ 4499692354643^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1474800463 10000000000 4499692354643 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4910232713/10000000000 : ℝ), (1444016431/2500000000 : ℝ), (-1474800463/10000000000 : ℝ)] ![(2043414572533/5000000000000 : ℝ), (6266540478221/12500000000000 : ℝ), (4499692354643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4910232713/10000000000 : ℝ)|^39 ≤ (2043414572533/5000000000000 : ℝ)^31
        have hw : |(4910232713/10000000000 : ℝ)|=(4910232713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1444016431/2500000000 : ℝ)|^39 ≤ (6266540478221/12500000000000 : ℝ)^31
        have hw : |(1444016431/2500000000 : ℝ)|=(1444016431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1474800463/10000000000 : ℝ)|^39 ≤ (4499692354643/50000000000000 : ℝ)^31
        have hw : |(-1474800463/10000000000 : ℝ)|=(1474800463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317058 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (34473/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-745391727/2500000000 : ℝ)*X 0 0+(596312937/2000000000 : ℝ)*X 0 1+(-1267964211/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((745392753/2500000000 : ℝ)*X 1 0+(-2981567483/10000000000 : ℝ)*X 1 1+(-50718523/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-201027577/1000000000 : ℝ)*X 0 0+(374395231/5000000000 : ℝ)*X 0 1+(-4306581863/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1571593427/10000000000 : ℝ)*X 1 0+(-1258969293/10000000000 : ℝ)*X 1 1+(-2153291929/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((741006513/2000000000 : ℝ)*X 2 0+(837646399/1250000000 : ℝ)*X 2 1+(1716133167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1789508039/10000000000 : ℝ)*X 0 0+(1815258301/2000000000 : ℝ)*X 0 1+(-508101/10000000000 : ℝ)*X 0 2+(1789508039/10000000000 : ℝ)*X 1 0+(1815258301/2000000000 : ℝ)*X 1 1+(-508101/10000000000 : ℝ)*X 1 2+(1789508039/10000000000 : ℝ)*X 2 0+(1815258301/2000000000 : ℝ)*X 2 1+(-508101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-300744757/2500000000 : ℝ)*X 0 0+(1949907333/10000000000 : ℝ)*X 0 1+(-4197644199/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((601489123/5000000000 : ℝ)*X 1 0+(-389981213/2000000000 : ℝ)*X 1 1+(-8395289741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7653342177/10000000000 : ℝ)*X 2 0+(1596989069/5000000000 : ℝ)*X 2 1+(178358367/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-21807127/39062500 : ℝ)*X 0 0+(2156871601/10000000000 : ℝ)*X 0 1+(-4581136819/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1103360153/10000000000 : ℝ)*X 1 0+(-5421711/40000000 : ℝ)*X 1 1+(-8842354033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3935896679/5000000000 : ℝ)*X 2 0+(1339342213/5000000000 : ℝ)*X 2 1+(1198060469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1001405329/10000000000 : ℝ)*X 0 0+(238947587/250000000 : ℝ)*X 0 1+(-117671/10000000000 : ℝ)*X 0 2+(1001405329/10000000000 : ℝ)*X 1 0+(238947587/250000000 : ℝ)*X 1 1+(-117671/10000000000 : ℝ)*X 1 2+(1001405329/10000000000 : ℝ)*X 2 0+(238947587/250000000 : ℝ)*X 2 1+(-117671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((78021/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(78021/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4052917848928162787673/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2382161149/10000000000 : ℝ)*(base5) + (1101666502213/1000000000000 : ℝ)*(base7) + (3702259/1000000000000 : ℝ)*(base44) + (614971/500000000000 : ℝ)*(base50) + (158473644877/1000000000000 : ℝ)*(base53) + (18938501601/12500000000 : ℝ)*(major_s0_0) + (1515076425821/1000000000000 : ℝ)*(major_s0_1) + (1356606483203/1000000000000 : ℝ)*(major_s0_2) + (349078661037/250000000000 : ℝ)*(sp_s0_7) + (1396358026993/1000000000000 : ℝ)*(sp_s0_8) + (448262872257/250000000000 : ℝ)*(sp_s0_9) + (852900428759/500000000000 : ℝ)*(sp_s0_13) + (47085103/1000000000000 : ℝ)*(sp_s0_14) + (704207/250000000000 : ℝ)*(sp_s0_27) + (210589247323/250000000000 : ℝ)*(f.failure) + (97177210883/62500000000 : ℝ)*(f.sum) + (505176205468207/5000000000000000000000000000 : ℝ)*base63 + (535606921088339/10000000000000000000000000000 : ℝ)*base65 + (1893372039557427/10000000000000000000000000000 : ℝ)*base66 + (1746703365353631/10000000000000000000000000000 : ℝ)*base69 + (3885905987306179/10000000000000000000000000000 : ℝ)*base71 + (48146318044713/125000000000000000000000000 : ℝ)*base73 + (1434499756582783/10000000000000000000000000000 : ℝ)*base75 + (13541637047277/125000000000000000000000000 : ℝ)*base76 + (1344247607980387/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (4713/12500000000000000 : ℝ)*base87 + (4713/12500000000000000 : ℝ)*base89 + (4713/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9099/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9099/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12496335287991304112847/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (513358962693/250000000000 : ℝ)*(base5) + (1107226501597/1000000000000 : ℝ)*(base7) + (213765338547/500000000000 : ℝ)*(base59) + (609553713219/500000000000 : ℝ)*(base60) + (1701871059611/1000000000000 : ℝ)*(major_s0_0) + (1701871059611/1000000000000 : ℝ)*(major_s0_1) + (1701871059611/1000000000000 : ℝ)*(major_s0_2) + (394531/500000000000 : ℝ)*(sp_s0_0) + (4076391/500000000000 : ℝ)*(sp_s0_1) + (182009/3125000000 : ℝ)*(sp_s0_8) + (1821371662131/1000000000000 : ℝ)*(sp_s0_14) + (1821306055531/1000000000000 : ℝ)*(sp_s0_15) + (1937391067279/500000000000 : ℝ)*(sp_s0_16) + (26167407/1000000000000 : ℝ)*(sp_s0_23) + (473104674587/500000000000 : ℝ)*(f.failure) + (1821372451193/1000000000000 : ℝ)*(f.sum) + (439412759/2500000000000000000000 : ℝ)*base62 + (8488156000587157/10000000000000000000000000000 : ℝ)*base64 + (4782182640412843/10000000000000000000000000000 : ℝ)*base67 + (7185495512070953/10000000000000000000000000000 : ℝ)*base68 + (925998776129051/2500000000000000000000000000 : ℝ)*base70 + (5496718893412843/10000000000000000000000000000 : ℝ)*base73 + (9980723729929047/10000000000000000000000000000 : ℝ)*base74 + (7357384643929047/10000000000000000000000000000 : ℝ)*base76 + (758707814087157/5000000000000000000000000000 : ℝ)*base78 + (8497/25000000000000000 : ℝ)*base87 + (8497/25000000000000000 : ℝ)*base89 + (8497/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-307/500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-307/500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19289600812428666116037/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21443716729/1000000000000 : ℝ)*(base5) + (31200437001/62500000000 : ℝ)*(base7) + (243270315501/1000000000000 : ℝ)*(base33) + (425873950537/500000000000 : ℝ)*(base44) + (472723/500000000000 : ℝ)*(base60) + (714264080663/500000000000 : ℝ)*(major_s0_0) + (820050575753/1000000000000 : ℝ)*(major_s0_1) + (1671798476827/1000000000000 : ℝ)*(major_s0_2) + (121354219/1000000000000 : ℝ)*(sp_s0_8) + (31894343/1000000000000 : ℝ)*(sp_s0_13) + (2127286750197/1000000000000 : ℝ)*(sp_s0_21) + (1032147179403/1000000000000 : ℝ)*(sp_s0_22) + (76218406057/40000000000 : ℝ)*(sp_s0_23) + (69434127511/125000000000 : ℝ)*(sp_s0_27) + (464744770109/500000000000 : ℝ)*(f.failure) + (2127286750197/1000000000000 : ℝ)*(f.sum) + (764358840195651/5000000000000000000000000000 : ℝ)*base62 + (3316395143659051/10000000000000000000000000000 : ℝ)*base65 + (2565780038013511/10000000000000000000000000000 : ℝ)*base66 + (1097015925961321/10000000000000000000000000000 : ℝ)*base68 + (450792932137051/10000000000000000000000000000 : ℝ)*base70 + (2524618344750681/5000000000000000000000000000 : ℝ)*base72 + (3410014730570019/10000000000000000000000000000 : ℝ)*base75 + (2503978302601949/5000000000000000000000000000 : ℝ)*base77 + (729137810485127/10000000000000000000000000000 : ℝ)*base79 + (2521/25000000000000000 : ℝ)*base86 + (2521/25000000000000000 : ℝ)*base88 + (2521/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (78021/100000 : ℝ) ^ (77/16 : ℝ) ≤ (30287812172209314459/100000000000000000000 : ℝ) := by
    have hpowers : (78021/100000 : ℝ)^77 ≤ (30287812172209314459/100000000000000000000 : ℝ)^16 := by
      have hnat : (78021 : ℕ)^77*100000000000000000000^16 ≤ 30287812172209314459^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78021 100000 30287812172209314459 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (78021/100000 : ℝ)) (X := (30287812172209314459/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (130287812172209314459/100000000000000000000 : ℝ) ≤ (10565160828227487/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (130287812172209314459/100000000000000000000 : ℝ)^16 ≤ (10565160828227487/10000000000000000 : ℝ)^77 := by
      have hnat : (130287812172209314459 : ℕ)^16*10000000000000000^77 ≤ 10565160828227487^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        130287812172209314459 100000000000000000000 10565160828227487 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10565160828227487/10000000000000000 : ℝ)) (X := (130287812172209314459/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (80287812172209314459/50000000000000000000 : ℝ) ≤ (11034143360149927/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (80287812172209314459/50000000000000000000 : ℝ)^16 ≤ (11034143360149927/10000000000000000 : ℝ)^77 := by
      have hnat : (80287812172209314459 : ℕ)^16*10000000000000000^77 ≤ 11034143360149927^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80287812172209314459 50000000000000000000 11034143360149927 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11034143360149927/10000000000000000 : ℝ)) (X := (80287812172209314459/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(565160828227487/7802100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(11724563298061/195052500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (78021/100000 : ℝ)) (alpha := (565160828227487/7802100000000000 : ℝ)) (beta := (11724563298061/195052500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (78021/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(565160828227487/7802100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(11724563298061/195052500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (9099/12500 : ℝ) ^ (77/16 : ℝ) ≤ (5422725039942590047/25000000000000000000 : ℝ) := by
    have hpowers : (9099/12500 : ℝ)^77 ≤ (5422725039942590047/25000000000000000000 : ℝ)^16 := by
      have hnat : (9099 : ℕ)^77*25000000000000000000^16 ≤ 5422725039942590047^16*12500^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9099 12500 5422725039942590047 25000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9099/12500 : ℝ)) (X := (5422725039942590047/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (30422725039942590047/25000000000000000000 : ℝ) ≤ (416654388913307/400000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (30422725039942590047/25000000000000000000 : ℝ)^16 ≤ (416654388913307/400000000000000 : ℝ)^77 := by
      have hnat : (30422725039942590047 : ℕ)^16*400000000000000^77 ≤ 416654388913307^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30422725039942590047 25000000000000000000 416654388913307 400000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (416654388913307/400000000000000 : ℝ)) (X := (30422725039942590047/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (17922725039942590047/12500000000000000000 : ℝ) ≤ (5388752584539207/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (17922725039942590047/12500000000000000000 : ℝ)^16 ≤ (5388752584539207/5000000000000000 : ℝ)^77 := by
      have hnat : (17922725039942590047 : ℕ)^16*5000000000000000^77 ≤ 5388752584539207^77*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17922725039942590047 12500000000000000000 5388752584539207 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5388752584539207/5000000000000000 : ℝ)) (X := (17922725039942590047/12500000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(16654388913307/291168000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(361145446245739/7279200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (9099/12500 : ℝ)) (alpha := (16654388913307/291168000000000 : ℝ)) (beta := (361145446245739/7279200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (9099/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(16654388913307/291168000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(361145446245739/7279200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (307/500 : ℝ) ^ (77/16 : ℝ) ≤ (9562254232010194241/100000000000000000000 : ℝ) := by
    have hpowers : (307/500 : ℝ)^77 ≤ (9562254232010194241/100000000000000000000 : ℝ)^16 := by
      have hnat : (307 : ℕ)^77*100000000000000000000^16 ≤ 9562254232010194241^16*500^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        307 500 9562254232010194241 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (307/500 : ℝ)) (X := (9562254232010194241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (109562254232010194241/100000000000000000000 : ℝ) ≤ (5095786719449601/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (109562254232010194241/100000000000000000000 : ℝ)^16 ≤ (5095786719449601/5000000000000000 : ℝ)^77 := by
      have hnat : (109562254232010194241 : ℕ)^16*5000000000000000^77 ≤ 5095786719449601^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109562254232010194241 100000000000000000000 5095786719449601 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5095786719449601/5000000000000000 : ℝ)) (X := (109562254232010194241/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (59562254232010194241/50000000000000000000 : ℝ) ≤ (10370326760356189/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (59562254232010194241/50000000000000000000 : ℝ)^16 ≤ (10370326760356189/10000000000000000 : ℝ)^77 := by
      have hnat : (59562254232010194241 : ℕ)^16*10000000000000000^77 ≤ 10370326760356189^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59562254232010194241 50000000000000000000 10370326760356189 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10370326760356189/10000000000000000 : ℝ)) (X := (59562254232010194241/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(95786719449601/3070000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(178753321456987/6140000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (307/500 : ℝ)) (alpha := (95786719449601/3070000000000000 : ℝ)) (beta := (178753321456987/6140000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (307/500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(95786719449601/3070000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(178753321456987/6140000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1687460091/5000000000 : ℝ)*X 0 0+(1660707133/5000000000 : ℝ)*X 0 1+(-1429734127/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((633955989/2000000000 : ℝ)*X 1 0+(-3117504287/10000000000 : ℝ)*X 1 1+(-3034808639/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5405337619/10000000000 : ℝ)*X 2 0+(5255671479/10000000000 : ℝ)*X 2 1+(1522099687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4910232713/10000000000 : ℝ)*X 0 0+(1444016431/2500000000 : ℝ)*X 0 1+(-1474800463/10000000000 : ℝ)*X 0 2+(4910232713/10000000000 : ℝ)*X 1 0+(1444016431/2500000000 : ℝ)*X 1 1+(-1474800463/10000000000 : ℝ)*X 1 2+(4910232713/10000000000 : ℝ)*X 2 0+(1444016431/2500000000 : ℝ)*X 2 1+(-1474800463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317058_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-194793/25000 : ℝ) < ((-89931/50000 : ℝ)*P 0+(-89931/50000 : ℝ)*P 1+(-89931/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-194793/25000 : ℝ) < (-69715352523296015215418977839557/8968860710000000000000000000000 : ℝ) := by norm_num
    linear_combination (200850714613/1000000000000 : ℝ)*(base5) + (81257/1000000000000 : ℝ)*(base15) + (33341/1000000000000 : ℝ)*(base16) + (6527/200000000000 : ℝ)*(base39) + (6559/500000000000 : ℝ)*(base40) + (13717620321/125000000000 : ℝ)*(base49) + (529/1000000000000 : ℝ)*(base50) + (528805846353/1000000000000 : ℝ)*(base60) + (89931/50000 : ℝ)*(major_s1_0) + (89931/50000 : ℝ)*(major_s1_1) + (89931/50000 : ℝ)*(major_s1_2) + (20242303127/7812500000 : ℝ)*(sp_s1_0) + (1295507342829/500000000000 : ℝ)*(sp_s1_1) + (2791865514869/1000000000000 : ℝ)*(sp_s1_2) + (799149285387/1000000000000 : ℝ)*(sp_s1_6) + (20242303127/7812500000 : ℝ)*(f.sum) + (8390939297701409/9311310000000000000000000000 : ℝ)*base62 + (507163651547/767500000000000000000000 : ℝ)*base64 + (23256826484557/30330000000000000000000000 : ℝ)*base67 + (2588883298487/3070000000000000000000000 : ℝ)*base68 + (44446268004639979/39920745000000000000000000000 : ℝ)*base70 + (6273352587653/52014000000000000000000000 : ℝ)*base72 + (3774915448393/15165000000000000000000000 : ℝ)*base74 + (112230498889073/260070000000000000000000000 : ℝ)*base76 + (124821306980496853/131465385000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c317064_s0_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-612868463/2000000000 : ℝ)*x 0 + (-728521241/2000000000 : ℝ)*x 1 + (-5704123461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (612868463/2000000000 : ℝ)^39 ≤ (22582871150131/100000000000000 : ℝ)^31 := by
    have hnat : (612868463 : ℕ)^39*100000000000000^31 ≤ 22582871150131^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612868463 2000000000 22582871150131 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (728521241/2000000000 : ℝ)^39 ≤ (2806908661237/10000000000000 : ℝ)^31 := by
    have hnat : (728521241 : ℕ)^39*10000000000000^31 ≤ 2806908661237^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728521241 2000000000 2806908661237 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5704123461/10000000000 : ℝ)^39 ≤ (49348042228197/100000000000000 : ℝ)^31 := by
    have hnat : (5704123461 : ℕ)^39*100000000000000^31 ≤ 49348042228197^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704123461 10000000000 49348042228197 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-612868463/2000000000 : ℝ), (-728521241/2000000000 : ℝ), (-5704123461/10000000000 : ℝ)] ![(22582871150131/100000000000000 : ℝ), (2806908661237/10000000000000 : ℝ), (49348042228197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-612868463/2000000000 : ℝ)|^39 ≤ (22582871150131/100000000000000 : ℝ)^31
        have hw : |(-612868463/2000000000 : ℝ)|=(612868463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-728521241/2000000000 : ℝ)|^39 ≤ (2806908661237/10000000000000 : ℝ)^31
        have hw : |(-728521241/2000000000 : ℝ)|=(728521241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5704123461/10000000000 : ℝ)|^39 ≤ (49348042228197/100000000000000 : ℝ)^31
        have hw : |(-5704123461/10000000000 : ℝ)|=(5704123461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317064_s0_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3410507437/10000000000 : ℝ)*x 0 + (5417578261/10000000000 : ℝ)*x 1 + (-725286297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3410507437/10000000000 : ℝ)^39 ≤ (3229729686667/12500000000000 : ℝ)^31 := by
    have hnat : (3410507437 : ℕ)^39*12500000000000^31 ≤ 3229729686667^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3410507437 10000000000 3229729686667 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417578261/10000000000 : ℝ)^39 ≤ (361326479997/781250000000 : ℝ)^31 := by
    have hnat : (5417578261 : ℕ)^39*781250000000^31 ≤ 361326479997^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417578261 10000000000 361326479997 781250000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (725286297/2000000000 : ℝ)^39 ≤ (13956186528369/50000000000000 : ℝ)^31 := by
    have hnat : (725286297 : ℕ)^39*50000000000000^31 ≤ 13956186528369^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725286297 2000000000 13956186528369 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3410507437/10000000000 : ℝ), (5417578261/10000000000 : ℝ), (-725286297/2000000000 : ℝ)] ![(3229729686667/12500000000000 : ℝ), (361326479997/781250000000 : ℝ), (13956186528369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3410507437/10000000000 : ℝ)|^39 ≤ (3229729686667/12500000000000 : ℝ)^31
        have hw : |(3410507437/10000000000 : ℝ)|=(3410507437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417578261/10000000000 : ℝ)|^39 ≤ (361326479997/781250000000 : ℝ)^31
        have hw : |(5417578261/10000000000 : ℝ)|=(5417578261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-725286297/2000000000 : ℝ)|^39 ≤ (13956186528369/50000000000000 : ℝ)^31
        have hw : |(-725286297/2000000000 : ℝ)|=(725286297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317064_s0_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6369544127/10000000000 : ℝ)*x 0 + (-883113561/2500000000 : ℝ)*x 1 + (472912533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6369544127/10000000000 : ℝ)^39 ≤ (2267856956691/4000000000000 : ℝ)^31 := by
    have hnat : (6369544127 : ℕ)^39*4000000000000^31 ≤ 2267856956691^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6369544127 10000000000 2267856956691 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883113561/2500000000 : ℝ)^39 ≤ (27005432524171/100000000000000 : ℝ)^31 := by
    have hnat : (883113561 : ℕ)^39*100000000000000^31 ≤ 27005432524171^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883113561 2500000000 27005432524171 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472912533/2000000000 : ℝ)^39 ≤ (16298143545603/100000000000000 : ℝ)^31 := by
    have hnat : (472912533 : ℕ)^39*100000000000000^31 ≤ 16298143545603^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472912533 2000000000 16298143545603 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6369544127/10000000000 : ℝ), (-883113561/2500000000 : ℝ), (472912533/2000000000 : ℝ)] ![(2267856956691/4000000000000 : ℝ), (27005432524171/100000000000000 : ℝ), (16298143545603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6369544127/10000000000 : ℝ)|^39 ≤ (2267856956691/4000000000000 : ℝ)^31
        have hw : |(6369544127/10000000000 : ℝ)|=(6369544127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-883113561/2500000000 : ℝ)|^39 ≤ (27005432524171/100000000000000 : ℝ)^31
        have hw : |(-883113561/2500000000 : ℝ)|=(883113561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(472912533/2000000000 : ℝ)|^39 ≤ (16298143545603/100000000000000 : ℝ)^31
        have hw : |(472912533/2000000000 : ℝ)|=(472912533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317064 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (34473/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-612868463/2000000000 : ℝ)*X 0 0+(-728521241/2000000000 : ℝ)*X 0 1+(-5704123461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317064_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3410507437/10000000000 : ℝ)*X 1 0+(5417578261/10000000000 : ℝ)*X 1 1+(-725286297/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317064_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((6369544127/10000000000 : ℝ)*X 2 0+(-883113561/2500000000 : ℝ)*X 2 1+(472912533/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317064_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-194793/25000 : ℝ) < ((-89931/50000 : ℝ)*P 0+(-89931/50000 : ℝ)*P 1+(-89931/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-194793/25000 : ℝ) < (-3895786771436847846109673589/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1104577081589/1000000000000 : ℝ)*(base1) + (104577081589/1000000000000 : ℝ)*(base7) + (56029/1000000000000 : ℝ)*(base18) + (140571/200000000000 : ℝ)*(base21) + (116737/1000000000000 : ℝ)*(base33) + (1319715029957/1000000000000 : ℝ)*(base39) + (155939472711/250000000000 : ℝ)*(base40) + (23021/500000000000 : ℝ)*(base50) + (130939345621/200000000000 : ℝ)*(base60) + (1798619883263/1000000000000 : ℝ)*(major_s0_0) + (89931/50000 : ℝ)*(major_s0_1) + (89931/50000 : ℝ)*(major_s0_2) + (910420875079/250000000000 : ℝ)*(sp_s0_0) + (2537106245961/1000000000000 : ℝ)*(sp_s0_1) + (1268552799567/500000000000 : ℝ)*(sp_s0_2) + (2537106418727/1000000000000 : ℝ)*(f.sum) + (197022261/500000000000000000000 : ℝ)*base63 + (13150491/125000000000000000000 : ℝ)*base64 + (545576573/1250000000000000000000 : ℝ)*base66 + (2602838217/10000000000000000000000 : ℝ)*base68 + (1301709809901749/10000000000000000000000000000 : ℝ)*base71 + (1808376428176881/10000000000000000000000000000 : ℝ)*base72 + (4490456961/5000000000000000000000 : ℝ)*base75 + (2228488386901749/10000000000000000000000000000 : ℝ)*base77 + (3106716883176881/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p017_b027 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 58 ≤ c.val) (hhi : c.val < 65)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=58 ∨ c=59 ∨ c=60 ∨ c=61 ∨ c=62 ∨ c=63 ∨ c=64 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact collision_c317058 p hpa (by linarith only [hpb]) X hX
  · exact collision_c317059 p hpa (by linarith only [hpb]) X hX
  · exact collision_c317060 p hpa (by linarith only [hpb]) X hX
  · exact collision_c317061 p hpa (by linarith only [hpb]) X hX
  · exact collision_c317062 p hpa (by linarith only [hpb]) X hX
  · exact (hn63 rfl).elim
  · exact collision_c317064 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 58 ≤ c.val) (hhi : c.val < 65)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_b027 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
