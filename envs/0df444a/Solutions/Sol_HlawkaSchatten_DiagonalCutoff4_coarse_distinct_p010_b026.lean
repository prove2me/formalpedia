-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b026
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:16:27.159795+00:00
-- url     : https://prove2.me/submissions/bfed68e1-987b-47a1-bc20-268d7dc70eb7

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310047_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310047_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310047_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310048_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310048_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310048_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310049_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310049_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310049_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310050_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310050_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310050_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310050_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310051_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310051_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310051_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310052_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310052_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310052_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310052_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310053_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310053_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310053_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310053_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310053_s4
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310047 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]]) : False := by
  have h0 := collision_c310047_s0 p hpa hpb X hX
  have h1 := collision_c310047_s1 p hpa hpb X hX h0
  exact collision_c310047_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310048 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]]) : False := by
  have h0 := collision_c310048_s0 p hpa hpb X hX
  have h1 := collision_c310048_s1 p hpa hpb X hX h0
  exact collision_c310048_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310049 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]]) : False := by
  have h0 := collision_c310049_s0 p hpa hpb X hX
  have h1 := collision_c310049_s1 p hpa hpb X hX h0
  exact collision_c310049_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310050 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]]) : False := by
  have h0 := collision_c310050_s0 p hpa hpb X hX
  have h1 := collision_c310050_s1 p hpa hpb X hX h0
  have h2 := collision_c310050_s2 p hpa hpb X hX h1
  exact collision_c310050_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310051 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  have h0 := collision_c310051_s0 p hpa hpb X hX
  have h1 := collision_c310051_s1 p hpa hpb X hX h0
  exact collision_c310051_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310052 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by
  have h0 := collision_c310052_s0 p hpa hpb X hX
  have h1 := collision_c310052_s1 p hpa hpb X hX h0
  have h2 := collision_c310052_s2 p hpa hpb X hX h1
  exact collision_c310052_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310053 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : False := by
  have h0 := collision_c310053_s0 p hpa hpb X hX
  have h1 := collision_c310053_s1 p hpa hpb X hX h0
  have h2 := collision_c310053_s2 p hpa hpb X hX h1
  have h3 := collision_c310053_s3 p hpa hpb X hX h2
  exact collision_c310053_s4 p hpa hpb X hX h3

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
theorem collision_support_c310046_s0_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1171513061/10000000000 : ℝ)*x 0 + (-1385639213/2500000000 : ℝ)*x 1 + (-1385639213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1171513061/10000000000 : ℝ)^9 ≤ (6348555018151/100000000000000 : ℝ)^7 := by
    have hnat : (1171513061 : ℕ)^9*100000000000000^7 ≤ 6348555018151^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171513061 10000000000 6348555018151 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385639213/2500000000 : ℝ)^9 ≤ (23412861244103/50000000000000 : ℝ)^7 := by
    have hnat : (1385639213 : ℕ)^9*50000000000000^7 ≤ 23412861244103^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385639213 2500000000 23412861244103 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1385639213/2500000000 : ℝ)^9 ≤ (23412861244103/50000000000000 : ℝ)^7 := by
    have hnat : (1385639213 : ℕ)^9*50000000000000^7 ≤ 23412861244103^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385639213 2500000000 23412861244103 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1171513061/10000000000 : ℝ), (-1385639213/2500000000 : ℝ), (-1385639213/2500000000 : ℝ)] ![(6348555018151/100000000000000 : ℝ), (23412861244103/50000000000000 : ℝ), (23412861244103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1171513061/10000000000 : ℝ)|^9 ≤ (6348555018151/100000000000000 : ℝ)^7
        have hw : |(-1171513061/10000000000 : ℝ)|=(1171513061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1385639213/2500000000 : ℝ)|^9 ≤ (23412861244103/50000000000000 : ℝ)^7
        have hw : |(-1385639213/2500000000 : ℝ)|=(1385639213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1385639213/2500000000 : ℝ)|^9 ≤ (23412861244103/50000000000000 : ℝ)^7
        have hw : |(-1385639213/2500000000 : ℝ)|=(1385639213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2383481003/5000000000 : ℝ)*x 0 + (3992480303/10000000000 : ℝ)*x 1 + (-3992480303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2383481003/5000000000 : ℝ)^9 ≤ (38575427253761/100000000000000 : ℝ)^7 := by
    have hnat : (2383481003 : ℕ)^9*100000000000000^7 ≤ 38575427253761^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383481003 5000000000 38575427253761 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3992480303/10000000000 : ℝ)^9 ≤ (6142457273261/20000000000000 : ℝ)^7 := by
    have hnat : (3992480303 : ℕ)^9*20000000000000^7 ≤ 6142457273261^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3992480303 10000000000 6142457273261 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3992480303/10000000000 : ℝ)^9 ≤ (6142457273261/20000000000000 : ℝ)^7 := by
    have hnat : (3992480303 : ℕ)^9*20000000000000^7 ≤ 6142457273261^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3992480303 10000000000 6142457273261 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2383481003/5000000000 : ℝ), (3992480303/10000000000 : ℝ), (-3992480303/10000000000 : ℝ)] ![(38575427253761/100000000000000 : ℝ), (6142457273261/20000000000000 : ℝ), (6142457273261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2383481003/5000000000 : ℝ)|^9 ≤ (38575427253761/100000000000000 : ℝ)^7
        have hw : |(2383481003/5000000000 : ℝ)|=(2383481003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3992480303/10000000000 : ℝ)|^9 ≤ (6142457273261/20000000000000 : ℝ)^7
        have hw : |(3992480303/10000000000 : ℝ)|=(3992480303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3992480303/10000000000 : ℝ)|^9 ≤ (6142457273261/20000000000000 : ℝ)^7
        have hw : |(-3992480303/10000000000 : ℝ)|=(3992480303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2383481003/5000000000 : ℝ)*x 0 + (-3992480303/10000000000 : ℝ)*x 1 + (3992480303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2383481003/5000000000 : ℝ)^9 ≤ (38575427253761/100000000000000 : ℝ)^7 := by
    have hnat : (2383481003 : ℕ)^9*100000000000000^7 ≤ 38575427253761^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383481003 5000000000 38575427253761 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3992480303/10000000000 : ℝ)^9 ≤ (6142457273261/20000000000000 : ℝ)^7 := by
    have hnat : (3992480303 : ℕ)^9*20000000000000^7 ≤ 6142457273261^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3992480303 10000000000 6142457273261 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3992480303/10000000000 : ℝ)^9 ≤ (6142457273261/20000000000000 : ℝ)^7 := by
    have hnat : (3992480303 : ℕ)^9*20000000000000^7 ≤ 6142457273261^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3992480303 10000000000 6142457273261 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2383481003/5000000000 : ℝ), (-3992480303/10000000000 : ℝ), (3992480303/10000000000 : ℝ)] ![(38575427253761/100000000000000 : ℝ), (6142457273261/20000000000000 : ℝ), (6142457273261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2383481003/5000000000 : ℝ)|^9 ≤ (38575427253761/100000000000000 : ℝ)^7
        have hw : |(2383481003/5000000000 : ℝ)|=(2383481003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3992480303/10000000000 : ℝ)|^9 ≤ (6142457273261/20000000000000 : ℝ)^7
        have hw : |(-3992480303/10000000000 : ℝ)|=(3992480303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3992480303/10000000000 : ℝ)|^9 ≤ (6142457273261/20000000000000 : ℝ)^7
        have hw : |(3992480303/10000000000 : ℝ)|=(3992480303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_3 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^9 ≤ (1 : ℝ)^7 := by
    have hnat : (1 : ℕ)^9*1^7 ≤ 1^7*1^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^9 ≤ (0 : ℝ)^7 := by
    have hnat : (0 : ℕ)^9*1^7 ≤ 0^7*1^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^9 ≤ (0 : ℝ)^7 := by
    have hnat : (0 : ℕ)^9*1^7 ≤ 0^7*1^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^9 ≤ (1 : ℝ)^7
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^9 ≤ (0 : ℝ)^7
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^9 ≤ (0 : ℝ)^7
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-14802279/125000000 : ℝ)*x 0 + (-1468020057/2500000000 : ℝ)*x 1 + (-5199046827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14802279/125000000 : ℝ)^9 ≤ (321848156877/5000000000000 : ℝ)^7 := by
    have hnat : (14802279 : ℕ)^9*5000000000000^7 ≤ 321848156877^7*125000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14802279 125000000 321848156877 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1468020057/2500000000 : ℝ)^9 ≤ (10087012106787/20000000000000 : ℝ)^7 := by
    have hnat : (1468020057 : ℕ)^9*20000000000000^7 ≤ 10087012106787^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468020057 2500000000 10087012106787 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5199046827/10000000000 : ℝ)^9 ≤ (10781994076823/25000000000000 : ℝ)^7 := by
    have hnat : (5199046827 : ℕ)^9*25000000000000^7 ≤ 10781994076823^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199046827 10000000000 10781994076823 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14802279/125000000 : ℝ), (-1468020057/2500000000 : ℝ), (-5199046827/10000000000 : ℝ)] ![(321848156877/5000000000000 : ℝ), (10087012106787/20000000000000 : ℝ), (10781994076823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14802279/125000000 : ℝ)|^9 ≤ (321848156877/5000000000000 : ℝ)^7
        have hw : |(-14802279/125000000 : ℝ)|=(14802279/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1468020057/2500000000 : ℝ)|^9 ≤ (10087012106787/20000000000000 : ℝ)^7
        have hw : |(-1468020057/2500000000 : ℝ)|=(1468020057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5199046827/10000000000 : ℝ)|^9 ≤ (10781994076823/25000000000000 : ℝ)^7
        have hw : |(-5199046827/10000000000 : ℝ)|=(5199046827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (91755151/200000000 : ℝ)*x 0 + (2390313423/5000000000 : ℝ)*x 1 + (-1677726577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91755151/200000000 : ℝ)^9 ≤ (9180257943463/25000000000000 : ℝ)^7 := by
    have hnat : (91755151 : ℕ)^9*25000000000000^7 ≤ 9180257943463^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91755151 200000000 9180257943463 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2390313423/5000000000 : ℝ)^9 ≤ (19358829372797/50000000000000 : ℝ)^7 := by
    have hnat : (2390313423 : ℕ)^9*50000000000000^7 ≤ 19358829372797^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2390313423 5000000000 19358829372797 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1677726577/5000000000 : ℝ)^9 ≤ (12280654731003/50000000000000 : ℝ)^7 := by
    have hnat : (1677726577 : ℕ)^9*50000000000000^7 ≤ 12280654731003^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677726577 5000000000 12280654731003 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(91755151/200000000 : ℝ), (2390313423/5000000000 : ℝ), (-1677726577/5000000000 : ℝ)] ![(9180257943463/25000000000000 : ℝ), (19358829372797/50000000000000 : ℝ), (12280654731003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(91755151/200000000 : ℝ)|^9 ≤ (9180257943463/25000000000000 : ℝ)^7
        have hw : |(91755151/200000000 : ℝ)|=(91755151/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2390313423/5000000000 : ℝ)|^9 ≤ (19358829372797/50000000000000 : ℝ)^7
        have hw : |(2390313423/5000000000 : ℝ)|=(2390313423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1677726577/5000000000 : ℝ)|^9 ≤ (12280654731003/50000000000000 : ℝ)^7
        have hw : |(-1677726577/5000000000 : ℝ)|=(1677726577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4587757531/10000000000 : ℝ)*x 0 + (-3278985953/10000000000 : ℝ)*x 1 + (4849371549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4587757531/10000000000 : ℝ)^9 ≤ (18360515789161/50000000000000 : ℝ)^7 := by
    have hnat : (4587757531 : ℕ)^9*50000000000000^7 ≤ 18360515789161^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4587757531 10000000000 18360515789161 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3278985953/10000000000 : ℝ)^9 ≤ (2980502170143/12500000000000 : ℝ)^7 := by
    have hnat : (3278985953 : ℕ)^9*12500000000000^7 ≤ 2980502170143^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3278985953 10000000000 2980502170143 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4849371549/10000000000 : ℝ)^9 ≤ (788699020691/2000000000000 : ℝ)^7 := by
    have hnat : (4849371549 : ℕ)^9*2000000000000^7 ≤ 788699020691^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4849371549 10000000000 788699020691 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4587757531/10000000000 : ℝ), (-3278985953/10000000000 : ℝ), (4849371549/10000000000 : ℝ)] ![(18360515789161/50000000000000 : ℝ), (2980502170143/12500000000000 : ℝ), (788699020691/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4587757531/10000000000 : ℝ)|^9 ≤ (18360515789161/50000000000000 : ℝ)^7
        have hw : |(4587757531/10000000000 : ℝ)|=(4587757531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3278985953/10000000000 : ℝ)|^9 ≤ (2980502170143/12500000000000 : ℝ)^7
        have hw : |(-3278985953/10000000000 : ℝ)|=(3278985953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4849371549/10000000000 : ℝ)|^9 ≤ (788699020691/2000000000000 : ℝ)^7
        have hw : |(4849371549/10000000000 : ℝ)|=(4849371549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4101400869/5000000000 : ℝ)*x 0 + (-1209284847/10000000000 : ℝ)*x 1 + (-1194709837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4101400869/5000000000 : ℝ)^9 ≤ (77513971763113/100000000000000 : ℝ)^7 := by
    have hnat : (4101400869 : ℕ)^9*100000000000000^7 ≤ 77513971763113^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4101400869 5000000000 77513971763113 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209284847/10000000000 : ℝ)^9 ≤ (661293004257/10000000000000 : ℝ)^7 := by
    have hnat : (1209284847 : ℕ)^9*10000000000000^7 ≤ 661293004257^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209284847 10000000000 661293004257 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194709837/5000000000 : ℝ)^9 ≤ (15873098179207/100000000000000 : ℝ)^7 := by
    have hnat : (1194709837 : ℕ)^9*100000000000000^7 ≤ 15873098179207^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194709837 5000000000 15873098179207 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4101400869/5000000000 : ℝ), (-1209284847/10000000000 : ℝ), (-1194709837/5000000000 : ℝ)] ![(77513971763113/100000000000000 : ℝ), (661293004257/10000000000000 : ℝ), (15873098179207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4101400869/5000000000 : ℝ)|^9 ≤ (77513971763113/100000000000000 : ℝ)^7
        have hw : |(4101400869/5000000000 : ℝ)|=(4101400869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1209284847/10000000000 : ℝ)|^9 ≤ (661293004257/10000000000000 : ℝ)^7
        have hw : |(-1209284847/10000000000 : ℝ)|=(1209284847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1194709837/5000000000 : ℝ)|^9 ≤ (15873098179207/100000000000000 : ℝ)^7
        have hw : |(-1194709837/5000000000 : ℝ)|=(1194709837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-144601273/5000000000 : ℝ)*x 0 + (-547939263/1000000000 : ℝ)*x 1 + (-1217179297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (144601273/5000000000 : ℝ)^9 ≤ (1050861720837/100000000000000 : ℝ)^7 := by
    have hnat : (144601273 : ℕ)^9*100000000000000^7 ≤ 1050861720837^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144601273 5000000000 1050861720837 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547939263/1000000000 : ℝ)^9 ≤ (9228147706703/20000000000000 : ℝ)^7 := by
    have hnat : (547939263 : ℕ)^9*20000000000000^7 ≤ 9228147706703^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547939263 1000000000 9228147706703 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217179297/2000000000 : ℝ)^9 ≤ (26404199870963/50000000000000 : ℝ)^7 := by
    have hnat : (1217179297 : ℕ)^9*50000000000000^7 ≤ 26404199870963^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217179297 2000000000 26404199870963 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-144601273/5000000000 : ℝ), (-547939263/1000000000 : ℝ), (-1217179297/2000000000 : ℝ)] ![(1050861720837/100000000000000 : ℝ), (9228147706703/20000000000000 : ℝ), (26404199870963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-144601273/5000000000 : ℝ)|^9 ≤ (1050861720837/100000000000000 : ℝ)^7
        have hw : |(-144601273/5000000000 : ℝ)|=(144601273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-547939263/1000000000 : ℝ)|^9 ≤ (9228147706703/20000000000000 : ℝ)^7
        have hw : |(-547939263/1000000000 : ℝ)|=(547939263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1217179297/2000000000 : ℝ)|^9 ≤ (26404199870963/50000000000000 : ℝ)^7
        have hw : |(-1217179297/2000000000 : ℝ)|=(1217179297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (66147193/156250000 : ℝ)*x 0 + (817751357/2000000000 : ℝ)*x 1 + (-555112771/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66147193/156250000 : ℝ)^9 ≤ (16557768098829/50000000000000 : ℝ)^7 := by
    have hnat : (66147193 : ℕ)^9*50000000000000^7 ≤ 16557768098829^7*156250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66147193 156250000 16557768098829 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (817751357/2000000000 : ℝ)^9 ≤ (15833880448119/50000000000000 : ℝ)^7 := by
    have hnat : (817751357 : ℕ)^9*50000000000000^7 ≤ 15833880448119^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817751357 2000000000 15833880448119 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555112771/1250000000 : ℝ)^9 ≤ (35216702881313/100000000000000 : ℝ)^7 := by
    have hnat : (555112771 : ℕ)^9*100000000000000^7 ≤ 35216702881313^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555112771 1250000000 35216702881313 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66147193/156250000 : ℝ), (817751357/2000000000 : ℝ), (-555112771/1250000000 : ℝ)] ![(16557768098829/50000000000000 : ℝ), (15833880448119/50000000000000 : ℝ), (35216702881313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66147193/156250000 : ℝ)|^9 ≤ (16557768098829/50000000000000 : ℝ)^7
        have hw : |(66147193/156250000 : ℝ)|=(66147193/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(817751357/2000000000 : ℝ)|^9 ≤ (15833880448119/50000000000000 : ℝ)^7
        have hw : |(817751357/2000000000 : ℝ)|=(817751357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-555112771/1250000000 : ℝ)|^9 ≤ (35216702881313/100000000000000 : ℝ)^7
        have hw : |(-555112771/1250000000 : ℝ)|=(555112771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (17827477/31250000 : ℝ)*x 0 + (-3331761883/10000000000 : ℝ)*x 1 + (1809355429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17827477/31250000 : ℝ)^9 ≤ (971905646837/2000000000000 : ℝ)^7 := by
    have hnat : (17827477 : ℕ)^9*2000000000000^7 ≤ 971905646837^7*31250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17827477 31250000 971905646837 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3331761883/10000000000 : ℝ)^9 ≤ (12169285771733/50000000000000 : ℝ)^7 := by
    have hnat : (3331761883 : ℕ)^9*50000000000000^7 ≤ 12169285771733^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3331761883 10000000000 12169285771733 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1809355429/5000000000 : ℝ)^9 ≤ (5413229218937/20000000000000 : ℝ)^7 := by
    have hnat : (1809355429 : ℕ)^9*20000000000000^7 ≤ 5413229218937^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809355429 5000000000 5413229218937 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17827477/31250000 : ℝ), (-3331761883/10000000000 : ℝ), (1809355429/5000000000 : ℝ)] ![(971905646837/2000000000000 : ℝ), (12169285771733/50000000000000 : ℝ), (5413229218937/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17827477/31250000 : ℝ)|^9 ≤ (971905646837/2000000000000 : ℝ)^7
        have hw : |(17827477/31250000 : ℝ)|=(17827477/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3331761883/10000000000 : ℝ)|^9 ≤ (12169285771733/50000000000000 : ℝ)^7
        have hw : |(-3331761883/10000000000 : ℝ)|=(3331761883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1809355429/5000000000 : ℝ)|^9 ≤ (5413229218937/20000000000000 : ℝ)^7
        have hw : |(1809355429/5000000000 : ℝ)|=(1809355429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4745766147/5000000000 : ℝ)*x 0 + (-5266817/80000000 : ℝ)*x 1 + (-365611953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4745766147/5000000000 : ℝ)^9 ≤ (11688829084241/12500000000000 : ℝ)^7 := by
    have hnat : (4745766147 : ℕ)^9*12500000000000^7 ≤ 11688829084241^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4745766147 5000000000 11688829084241 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266817/80000000 : ℝ)^9 ≤ (60520830337/2000000000000 : ℝ)^7 := by
    have hnat : (5266817 : ℕ)^9*2000000000000^7 ≤ 60520830337^7*80000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266817 80000000 60520830337 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365611953/5000000000 : ℝ)^9 ≤ (3463325794799/100000000000000 : ℝ)^7 := by
    have hnat : (365611953 : ℕ)^9*100000000000000^7 ≤ 3463325794799^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365611953 5000000000 3463325794799 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4745766147/5000000000 : ℝ), (-5266817/80000000 : ℝ), (-365611953/5000000000 : ℝ)] ![(11688829084241/12500000000000 : ℝ), (60520830337/2000000000000 : ℝ), (3463325794799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4745766147/5000000000 : ℝ)|^9 ≤ (11688829084241/12500000000000 : ℝ)^7
        have hw : |(4745766147/5000000000 : ℝ)|=(4745766147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5266817/80000000 : ℝ)|^9 ≤ (60520830337/2000000000000 : ℝ)^7
        have hw : |(-5266817/80000000 : ℝ)|=(5266817/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-365611953/5000000000 : ℝ)|^9 ≤ (3463325794799/100000000000000 : ℝ)^7
        have hw : |(-365611953/5000000000 : ℝ)|=(365611953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-28920239/1000000000 : ℝ)*x 0 + (-608589561/1000000000 : ℝ)*x 1 + (-2739696799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28920239/1000000000 : ℝ)^9 ≤ (105086099203/10000000000000 : ℝ)^7 := by
    have hnat : (28920239 : ℕ)^9*10000000000000^7 ≤ 105086099203^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28920239 1000000000 105086099203 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608589561/1000000000 : ℝ)^9 ≤ (26404194990051/50000000000000 : ℝ)^7 := by
    have hnat : (608589561 : ℕ)^9*50000000000000^7 ≤ 26404194990051^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608589561 1000000000 26404194990051 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2739696799/5000000000 : ℝ)^9 ≤ (46140749013773/100000000000000 : ℝ)^7 := by
    have hnat : (2739696799 : ℕ)^9*100000000000000^7 ≤ 46140749013773^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739696799 5000000000 46140749013773 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-28920239/1000000000 : ℝ), (-608589561/1000000000 : ℝ), (-2739696799/5000000000 : ℝ)] ![(105086099203/10000000000000 : ℝ), (26404194990051/50000000000000 : ℝ), (46140749013773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-28920239/1000000000 : ℝ)|^9 ≤ (105086099203/10000000000000 : ℝ)^7
        have hw : |(-28920239/1000000000 : ℝ)|=(28920239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-608589561/1000000000 : ℝ)|^9 ≤ (26404194990051/50000000000000 : ℝ)^7
        have hw : |(-608589561/1000000000 : ℝ)|=(608589561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2739696799/5000000000 : ℝ)|^9 ≤ (46140749013773/100000000000000 : ℝ)^7
        have hw : |(-2739696799/5000000000 : ℝ)|=(2739696799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5704792503/10000000000 : ℝ)*x 0 + (90467783/250000000 : ℝ)*x 1 + (-333176157/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5704792503/10000000000 : ℝ)^9 ≤ (759301263147/1562500000000 : ℝ)^7 := by
    have hnat : (5704792503 : ℕ)^9*1562500000000^7 ≤ 759301263147^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704792503 10000000000 759301263147 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90467783/250000000 : ℝ)^9 ≤ (6766537634377/25000000000000 : ℝ)^7 := by
    have hnat : (90467783 : ℕ)^9*25000000000000^7 ≤ 6766537634377^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90467783 250000000 6766537634377 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333176157/1000000000 : ℝ)^9 ≤ (24338568603719/100000000000000 : ℝ)^7 := by
    have hnat : (333176157 : ℕ)^9*100000000000000^7 ≤ 24338568603719^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333176157 1000000000 24338568603719 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5704792503/10000000000 : ℝ), (90467783/250000000 : ℝ), (-333176157/1000000000 : ℝ)] ![(759301263147/1562500000000 : ℝ), (6766537634377/25000000000000 : ℝ), (24338568603719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5704792503/10000000000 : ℝ)|^9 ≤ (759301263147/1562500000000 : ℝ)^7
        have hw : |(5704792503/10000000000 : ℝ)|=(5704792503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90467783/250000000 : ℝ)|^9 ≤ (6766537634377/25000000000000 : ℝ)^7
        have hw : |(90467783/250000000 : ℝ)|=(90467783/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-333176157/1000000000 : ℝ)|^9 ≤ (24338568603719/100000000000000 : ℝ)^7
        have hw : |(-333176157/1000000000 : ℝ)|=(333176157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (529177689/1250000000 : ℝ)*x 0 + (-277556377/625000000 : ℝ)*x 1 + (4088755753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529177689/1250000000 : ℝ)^9 ≤ (1655777393211/5000000000000 : ℝ)^7 := by
    have hnat : (529177689 : ℕ)^9*5000000000000^7 ≤ 1655777393211^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529177689 1250000000 1655777393211 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277556377/625000000 : ℝ)^9 ≤ (35216701494683/100000000000000 : ℝ)^7 := by
    have hnat : (277556377 : ℕ)^9*100000000000000^7 ≤ 35216701494683^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277556377 625000000 35216701494683 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4088755753/10000000000 : ℝ)^9 ≤ (1583387530981/5000000000000 : ℝ)^7 := by
    have hnat : (4088755753 : ℕ)^9*5000000000000^7 ≤ 1583387530981^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4088755753 10000000000 1583387530981 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529177689/1250000000 : ℝ), (-277556377/625000000 : ℝ), (4088755753/10000000000 : ℝ)] ![(1655777393211/5000000000000 : ℝ), (35216701494683/100000000000000 : ℝ), (1583387530981/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529177689/1250000000 : ℝ)|^9 ≤ (1655777393211/5000000000000 : ℝ)^7
        have hw : |(529177689/1250000000 : ℝ)|=(529177689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277556377/625000000 : ℝ)|^9 ≤ (35216701494683/100000000000000 : ℝ)^7
        have hw : |(-277556377/625000000 : ℝ)|=(277556377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4088755753/10000000000 : ℝ)|^9 ≤ (1583387530981/5000000000000 : ℝ)^7
        have hw : |(4088755753/10000000000 : ℝ)|=(4088755753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s0_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (9491532351/10000000000 : ℝ)*x 0 + (-365611867/5000000000 : ℝ)*x 1 + (-658352181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9491532351/10000000000 : ℝ)^9 ≤ (93510633395939/100000000000000 : ℝ)^7 := by
    have hnat : (9491532351 : ℕ)^9*100000000000000^7 ≤ 93510633395939^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9491532351 10000000000 93510633395939 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (365611867/5000000000 : ℝ)^9 ≤ (3463324747391/100000000000000 : ℝ)^7 := by
    have hnat : (365611867 : ℕ)^9*100000000000000^7 ≤ 3463324747391^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365611867 5000000000 3463324747391 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658352181/10000000000 : ℝ)^9 ≤ (3026041847789/100000000000000 : ℝ)^7 := by
    have hnat : (658352181 : ℕ)^9*100000000000000^7 ≤ 3026041847789^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658352181 10000000000 3026041847789 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9491532351/10000000000 : ℝ), (-365611867/5000000000 : ℝ), (-658352181/10000000000 : ℝ)] ![(93510633395939/100000000000000 : ℝ), (3463324747391/100000000000000 : ℝ), (3026041847789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9491532351/10000000000 : ℝ)|^9 ≤ (93510633395939/100000000000000 : ℝ)^7
        have hw : |(9491532351/10000000000 : ℝ)|=(9491532351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-365611867/5000000000 : ℝ)|^9 ≤ (3463324747391/100000000000000 : ℝ)^7
        have hw : |(-365611867/5000000000 : ℝ)|=(365611867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-658352181/10000000000 : ℝ)|^9 ≤ (3026041847789/100000000000000 : ℝ)^7
        have hw : |(-658352181/10000000000 : ℝ)|=(658352181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2654562039/10000000000 : ℝ)*x 0 + (-4990220523/10000000000 : ℝ)*x 1 + (-4990220523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654562039/10000000000 : ℝ)^9 ≤ (18172698300849/100000000000000 : ℝ)^7 := by
    have hnat : (2654562039 : ℕ)^9*100000000000000^7 ≤ 18172698300849^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654562039 10000000000 18172698300849 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4990220523/10000000000 : ℝ)^9 ≤ (20456825419423/50000000000000 : ℝ)^7 := by
    have hnat : (4990220523 : ℕ)^9*50000000000000^7 ≤ 20456825419423^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990220523 10000000000 20456825419423 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4990220523/10000000000 : ℝ)^9 ≤ (20456825419423/50000000000000 : ℝ)^7 := by
    have hnat : (4990220523 : ℕ)^9*50000000000000^7 ≤ 20456825419423^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990220523 10000000000 20456825419423 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2654562039/10000000000 : ℝ), (-4990220523/10000000000 : ℝ), (-4990220523/10000000000 : ℝ)] ![(18172698300849/100000000000000 : ℝ), (20456825419423/50000000000000 : ℝ), (20456825419423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2654562039/10000000000 : ℝ)|^9 ≤ (18172698300849/100000000000000 : ℝ)^7
        have hw : |(-2654562039/10000000000 : ℝ)|=(2654562039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4990220523/10000000000 : ℝ)|^9 ≤ (20456825419423/50000000000000 : ℝ)^7
        have hw : |(-4990220523/10000000000 : ℝ)|=(4990220523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4990220523/10000000000 : ℝ)|^9 ≤ (20456825419423/50000000000000 : ℝ)^7
        have hw : |(-4990220523/10000000000 : ℝ)|=(4990220523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (909858083/2000000000 : ℝ)*x 0 + (41057601/100000000 : ℝ)*x 1 + (-41057601/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (909858083/2000000000 : ℝ)^9 ≤ (3632564042193/10000000000000 : ℝ)^7 := by
    have hnat : (909858083 : ℕ)^9*10000000000000^7 ≤ 3632564042193^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909858083 2000000000 3632564042193 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41057601/100000000 : ℝ)^9 ≤ (3979647472849/12500000000000 : ℝ)^7 := by
    have hnat : (41057601 : ℕ)^9*12500000000000^7 ≤ 3979647472849^7*100000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41057601 100000000 3979647472849 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41057601/100000000 : ℝ)^9 ≤ (3979647472849/12500000000000 : ℝ)^7 := by
    have hnat : (41057601 : ℕ)^9*12500000000000^7 ≤ 3979647472849^7*100000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41057601 100000000 3979647472849 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(909858083/2000000000 : ℝ), (41057601/100000000 : ℝ), (-41057601/100000000 : ℝ)] ![(3632564042193/10000000000000 : ℝ), (3979647472849/12500000000000 : ℝ), (3979647472849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(909858083/2000000000 : ℝ)|^9 ≤ (3632564042193/10000000000000 : ℝ)^7
        have hw : |(909858083/2000000000 : ℝ)|=(909858083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41057601/100000000 : ℝ)|^9 ≤ (3979647472849/12500000000000 : ℝ)^7
        have hw : |(41057601/100000000 : ℝ)|=(41057601/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41057601/100000000 : ℝ)|^9 ≤ (3979647472849/12500000000000 : ℝ)^7
        have hw : |(-41057601/100000000 : ℝ)|=(41057601/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (909858083/2000000000 : ℝ)*x 0 + (-41057601/100000000 : ℝ)*x 1 + (41057601/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (909858083/2000000000 : ℝ)^9 ≤ (3632564042193/10000000000000 : ℝ)^7 := by
    have hnat : (909858083 : ℕ)^9*10000000000000^7 ≤ 3632564042193^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909858083 2000000000 3632564042193 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41057601/100000000 : ℝ)^9 ≤ (3979647472849/12500000000000 : ℝ)^7 := by
    have hnat : (41057601 : ℕ)^9*12500000000000^7 ≤ 3979647472849^7*100000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41057601 100000000 3979647472849 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41057601/100000000 : ℝ)^9 ≤ (3979647472849/12500000000000 : ℝ)^7 := by
    have hnat : (41057601 : ℕ)^9*12500000000000^7 ≤ 3979647472849^7*100000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41057601 100000000 3979647472849 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(909858083/2000000000 : ℝ), (-41057601/100000000 : ℝ), (41057601/100000000 : ℝ)] ![(3632564042193/10000000000000 : ℝ), (3979647472849/12500000000000 : ℝ), (3979647472849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(909858083/2000000000 : ℝ)|^9 ≤ (3632564042193/10000000000000 : ℝ)^7
        have hw : |(909858083/2000000000 : ℝ)|=(909858083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41057601/100000000 : ℝ)|^9 ≤ (3979647472849/12500000000000 : ℝ)^7
        have hw : |(-41057601/100000000 : ℝ)|=(41057601/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41057601/100000000 : ℝ)|^9 ≤ (3979647472849/12500000000000 : ℝ)^7
        have hw : |(41057601/100000000 : ℝ)|=(41057601/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310046_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6320036157/10000000000 : ℝ)*x 0 + (-3110731467/10000000000 : ℝ)*x 1 + (-3110731467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6320036157/10000000000 : ℝ)^9 ≤ (11086955153303/20000000000000 : ℝ)^7 := by
    have hnat : (6320036157 : ℕ)^9*20000000000000^7 ≤ 11086955153303^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6320036157 10000000000 11086955153303 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3110731467/10000000000 : ℝ)^9 ≤ (1114130605363/5000000000000 : ℝ)^7 := by
    have hnat : (3110731467 : ℕ)^9*5000000000000^7 ≤ 1114130605363^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110731467 10000000000 1114130605363 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3110731467/10000000000 : ℝ)^9 ≤ (1114130605363/5000000000000 : ℝ)^7 := by
    have hnat : (3110731467 : ℕ)^9*5000000000000^7 ≤ 1114130605363^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110731467 10000000000 1114130605363 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6320036157/10000000000 : ℝ), (-3110731467/10000000000 : ℝ), (-3110731467/10000000000 : ℝ)] ![(11086955153303/20000000000000 : ℝ), (1114130605363/5000000000000 : ℝ), (1114130605363/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6320036157/10000000000 : ℝ)|^9 ≤ (11086955153303/20000000000000 : ℝ)^7
        have hw : |(6320036157/10000000000 : ℝ)|=(6320036157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3110731467/10000000000 : ℝ)|^9 ≤ (1114130605363/5000000000000 : ℝ)^7
        have hw : |(-3110731467/10000000000 : ℝ)|=(3110731467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3110731467/10000000000 : ℝ)|^9 ≤ (1114130605363/5000000000000 : ℝ)^7
        have hw : |(-3110731467/10000000000 : ℝ)|=(3110731467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310046 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1171513061/10000000000 : ℝ)*X 0 0+(-1385639213/2500000000 : ℝ)*X 0 1+(-1385639213/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2383481003/5000000000 : ℝ)*X 1 0+(3992480303/10000000000 : ℝ)*X 1 1+(-3992480303/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2383481003/5000000000 : ℝ)*X 2 0+(-3992480303/10000000000 : ℝ)*X 2 1+(3992480303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-14802279/125000000 : ℝ)*X 0 0+(-1468020057/2500000000 : ℝ)*X 0 1+(-5199046827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((91755151/200000000 : ℝ)*X 1 0+(2390313423/5000000000 : ℝ)*X 1 1+(-1677726577/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4587757531/10000000000 : ℝ)*X 2 0+(-3278985953/10000000000 : ℝ)*X 2 1+(4849371549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((4101400869/5000000000 : ℝ)*X 0 0+(-1209284847/10000000000 : ℝ)*X 0 1+(-1194709837/5000000000 : ℝ)*X 0 2+(4101400869/5000000000 : ℝ)*X 1 0+(-1209284847/10000000000 : ℝ)*X 1 1+(-1194709837/5000000000 : ℝ)*X 1 2+(4101400869/5000000000 : ℝ)*X 2 0+(-1209284847/10000000000 : ℝ)*X 2 1+(-1194709837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-144601273/5000000000 : ℝ)*X 0 0+(-547939263/1000000000 : ℝ)*X 0 1+(-1217179297/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((66147193/156250000 : ℝ)*X 1 0+(817751357/2000000000 : ℝ)*X 1 1+(-555112771/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((17827477/31250000 : ℝ)*X 2 0+(-3331761883/10000000000 : ℝ)*X 2 1+(1809355429/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((4745766147/5000000000 : ℝ)*X 0 0+(-5266817/80000000 : ℝ)*X 0 1+(-365611953/5000000000 : ℝ)*X 0 2+(4745766147/5000000000 : ℝ)*X 1 0+(-5266817/80000000 : ℝ)*X 1 1+(-365611953/5000000000 : ℝ)*X 1 2+(4745766147/5000000000 : ℝ)*X 2 0+(-5266817/80000000 : ℝ)*X 2 1+(-365611953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-28920239/1000000000 : ℝ)*X 0 0+(-608589561/1000000000 : ℝ)*X 0 1+(-2739696799/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((5704792503/10000000000 : ℝ)*X 1 0+(90467783/250000000 : ℝ)*X 1 1+(-333176157/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((529177689/1250000000 : ℝ)*X 2 0+(-277556377/625000000 : ℝ)*X 2 1+(4088755753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((9491532351/10000000000 : ℝ)*X 0 0+(-365611867/5000000000 : ℝ)*X 0 1+(-658352181/10000000000 : ℝ)*X 0 2+(9491532351/10000000000 : ℝ)*X 1 0+(-365611867/5000000000 : ℝ)*X 1 1+(-658352181/10000000000 : ℝ)*X 1 2+(9491532351/10000000000 : ℝ)*X 2 0+(-365611867/5000000000 : ℝ)*X 2 1+(-658352181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((5107/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5107/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (43596007124070472374453/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3569/6250000000 : ℝ)*(base3) + (914750079597/1000000000000 : ℝ)*(base39) + (13358500193/200000000000 : ℝ)*(base49) + (1745753/1000000000000 : ℝ)*(base59) + (3328357378711/1000000000000 : ℝ)*(major_s0_0) + (3328357378711/1000000000000 : ℝ)*(major_s0_1) + (3328357378711/1000000000000 : ℝ)*(major_s0_2) + (1149885084307/250000000000 : ℝ)*(sp_s0_7) + (1149860553343/250000000000 : ℝ)*(sp_s0_8) + (919889856433/200000000000 : ℝ)*(sp_s0_9) + (2057169627121/1000000000000 : ℝ)*(sp_s0_13) + (25002631/250000000000 : ℝ)*(sp_s0_15) + (328907/250000000000 : ℝ)*(sp_s0_20) + (92370691/1000000000000 : ℝ)*(sp_s0_22) + (2057170198161/1000000000000 : ℝ)*(f.failure) + (574942706607/125000000000 : ℝ)*(f.sum) + (742594615105533/5000000000000000000000000000 : ℝ)*base62 + (4064877742958151/10000000000000000000000000000 : ℝ)*base64 + (4245830639958151/10000000000000000000000000000 : ℝ)*base66 + (3463614247894467/10000000000000000000000000000 : ℝ)*base69 + (522176183734079/2500000000000000000000000000 : ℝ)*base71 + (1043035580041849/10000000000000000000000000000 : ℝ)*base73 + (1902917888894467/10000000000000000000000000000 : ℝ)*base75 + (3372798562105533/10000000000000000000000000000 : ℝ)*base76 + (2460075529041849/5000000000000000000000000000 : ℝ)*base79 + (37327/100000000000000000 : ℝ)*base86 + (37327/100000000000000000 : ℝ)*base88 + (37327/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10859/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-10859/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2940022278389124234009/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5358379/500000000000 : ℝ)*(base12) + (67868090673/200000000000 : ℝ)*(base39) + (103489/40000000000 : ℝ)*(base59) + (147021852733/12500000000 : ℝ)*(major_s0_0) + (614758870799/125000000000 : ℝ)*(major_s0_1) + (614758870799/125000000000 : ℝ)*(major_s0_2) + (6856811/125000000000 : ℝ)*(sp_s0_0) + (211757/7812500000 : ℝ)*(sp_s0_1) + (855459656531/125000000000 : ℝ)*(sp_s0_3) + (7284331/250000000000 : ℝ)*(sp_s0_9) + (1699085712509/250000000000 : ℝ)*(sp_s0_14) + (6796381316387/1000000000000 : ℝ)*(sp_s0_15) + (3398189641979/500000000000 : ℝ)*(sp_s0_16) + (121589215019/40000000000 : ℝ)*(sp_s0_19) + (121589215019/40000000000 : ℝ)*(f.failure) + (3398204210641/500000000000 : ℝ)*(f.sum) + (62564680421997/625000000000000000000000000 : ℝ)*base62 + (124050106893241/1250000000000000000000000000 : ℝ)*base65 + (21907576268241/1250000000000000000000000000 : ℝ)*base67 + (783372697546997/1250000000000000000000000000 : ℝ)*base68 + (434029061545749/1250000000000000000000000000 : ℝ)*base70 + (52199979319947/125000000000000000000000000 : ℝ)*base73 + (158018518046997/1250000000000000000000000000 : ℝ)*base74 + (18813368156101/125000000000000000000000000 : ℝ)*base77 + (105402871782289/1250000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1067/4000000000000000 : ℝ)*base87 + (1067/4000000000000000 : ℝ)*base89 + (1067/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10859/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10859/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1237172529174935375157/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (907356384269/1000000000000 : ℝ)*(base39) + (983/2000000000 : ℝ)*(base49) + (3890171/1000000000000 : ℝ)*(base59) + (9771922397863/1000000000000 : ℝ)*(major_s0_0) + (245904389173/50000000000 : ℝ)*(major_s0_1) + (245904389173/50000000000 : ℝ)*(major_s0_2) + (6648949/500000000000 : ℝ)*(sp_s0_2) + (4853834614403/1000000000000 : ℝ)*(sp_s0_3) + (45126513/500000000000 : ℝ)*(sp_s0_7) + (14559457/250000000000 : ℝ)*(sp_s0_8) + (6796341245097/1000000000000 : ℝ)*(sp_s0_20) + (1359274652059/200000000000 : ℝ)*(sp_s0_21) + (271856728009/40000000000 : ℝ)*(sp_s0_22) + (1519870384831/500000000000 : ℝ)*(sp_s0_25) + (1519870384831/500000000000 : ℝ)*(f.failure) + (6796431498123/1000000000000 : ℝ)*(f.sum) + (79518733008281/250000000000000000000000000 : ℝ)*base63 + (103445357789093/500000000000000000000000000 : ℝ)*base64 + (285454441589093/500000000000000000000000000 : ℝ)*base66 + (398804805958281/500000000000000000000000000 : ℝ)*base69 + (5456189355874351/10000000000000000000000000000 : ℝ)*base71 + (3149445809935383/10000000000000000000000000000 : ℝ)*base72 + (414918115808281/500000000000000000000000000 : ℝ)*base75 + (5301021300343789/10000000000000000000000000000 : ℝ)*base76 + (3398474847282757/10000000000000000000000000000 : ℝ)*base79 + (38017/50000000000000000 : ℝ)*base86 + (38017/50000000000000000 : ℝ)*base88 + (38017/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (5107/50000 : ℝ) ^ (35/8 : ℝ) ≤ (925255882333003/20000000000000000000 : ℝ) := by
    have hpowers : (5107/50000 : ℝ)^35 ≤ (925255882333003/20000000000000000000 : ℝ)^8 := by
      have hnat : (5107 : ℕ)^35*20000000000000000000^8 ≤ 925255882333003^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5107 50000 925255882333003 20000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5107/50000 : ℝ)) (X := (925255882333003/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (20000925255882333003/20000000000000000000 : ℝ) ≤ (10000105741642551/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (20000925255882333003/20000000000000000000 : ℝ)^8 ≤ (10000105741642551/10000000000000000 : ℝ)^35 := by
      have hnat : (20000925255882333003 : ℕ)^8*10000000000000000^35 ≤ 10000105741642551^35*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20000925255882333003 20000000000000000000 10000105741642551 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000105741642551/10000000000000000 : ℝ)) (X := (20000925255882333003/20000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10000925255882333003/10000000000000000000 : ℝ) ≤ (2500052869877897/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (10000925255882333003/10000000000000000000 : ℝ)^8 ≤ (2500052869877897/2500000000000000 : ℝ)^35 := by
      have hnat : (10000925255882333003 : ℕ)^8*2500000000000000^35 ≤ 2500052869877897^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000925255882333003 10000000000000000000 2500052869877897 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500052869877897/2500000000000000 : ℝ)) (X := (10000925255882333003/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(105741642551/1021400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(105737869037/1021400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (5107/50000 : ℝ)) (alpha := (105741642551/1021400000000000 : ℝ)) (beta := (105737869037/1021400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5107/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(105741642551/1021400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(105737869037/1021400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (10859/25000 : ℝ) ^ (35/8 : ℝ) ≤ (260371222376393077/10000000000000000000 : ℝ) := by
    have hpowers : (10859/25000 : ℝ)^35 ≤ (260371222376393077/10000000000000000000 : ℝ)^8 := by
      have hnat : (10859 : ℕ)^35*10000000000000000000^8 ≤ 260371222376393077^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10859 25000 260371222376393077 10000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10859/25000 : ℝ)) (X := (260371222376393077/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10260371222376393077/10000000000000000000 : ℝ) ≤ (5029462380969743/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (10260371222376393077/10000000000000000000 : ℝ)^8 ≤ (5029462380969743/5000000000000000 : ℝ)^35 := by
      have hnat : (10260371222376393077 : ℕ)^8*5000000000000000^35 ≤ 5029462380969743^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10260371222376393077 10000000000000000000 5029462380969743 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029462380969743/5000000000000000 : ℝ)) (X := (10260371222376393077/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5260371222376393077/5000000000000000000 : ℝ) ≤ (2023341411470497/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (5260371222376393077/5000000000000000000 : ℝ)^8 ≤ (2023341411470497/2000000000000000 : ℝ)^35 := by
      have hnat : (5260371222376393077 : ℕ)^8*2000000000000000^35 ≤ 2023341411470497^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5260371222376393077 5000000000000000000 2023341411470497 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2023341411470497/2000000000000000 : ℝ)) (X := (5260371222376393077/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(29462380969743/2171800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(57782295412999/4343600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (10859/25000 : ℝ)) (alpha := (29462380969743/2171800000000000 : ℝ)) (beta := (57782295412999/4343600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (10859/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(29462380969743/2171800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(57782295412999/4343600000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (10859/25000 : ℝ) ^ (35/8 : ℝ) ≤ (260371222376393077/10000000000000000000 : ℝ) := by
    have hpowers : (10859/25000 : ℝ)^35 ≤ (260371222376393077/10000000000000000000 : ℝ)^8 := by
      have hnat : (10859 : ℕ)^35*10000000000000000000^8 ≤ 260371222376393077^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10859 25000 260371222376393077 10000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10859/25000 : ℝ)) (X := (260371222376393077/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (10260371222376393077/10000000000000000000 : ℝ) ≤ (5029462380969743/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (10260371222376393077/10000000000000000000 : ℝ)^8 ≤ (5029462380969743/5000000000000000 : ℝ)^35 := by
      have hnat : (10260371222376393077 : ℕ)^8*5000000000000000^35 ≤ 5029462380969743^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10260371222376393077 10000000000000000000 5029462380969743 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029462380969743/5000000000000000 : ℝ)) (X := (10260371222376393077/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5260371222376393077/5000000000000000000 : ℝ) ≤ (2023341411470497/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (5260371222376393077/5000000000000000000 : ℝ)^8 ≤ (2023341411470497/2000000000000000 : ℝ)^35 := by
      have hnat : (5260371222376393077 : ℕ)^8*2000000000000000^35 ≤ 2023341411470497^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5260371222376393077 5000000000000000000 2023341411470497 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2023341411470497/2000000000000000 : ℝ)) (X := (5260371222376393077/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(29462380969743/2171800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(57782295412999/4343600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (10859/25000 : ℝ)) (alpha := (29462380969743/2171800000000000 : ℝ)) (beta := (57782295412999/4343600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (10859/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(29462380969743/2171800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(57782295412999/4343600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2654562039/10000000000 : ℝ)*X 0 0+(-4990220523/10000000000 : ℝ)*X 0 1+(-4990220523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((909858083/2000000000 : ℝ)*X 1 0+(41057601/100000000 : ℝ)*X 1 1+(-41057601/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((909858083/2000000000 : ℝ)*X 2 0+(-41057601/100000000 : ℝ)*X 2 1+(41057601/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6320036157/10000000000 : ℝ)*X 0 0+(-3110731467/10000000000 : ℝ)*X 0 1+(-3110731467/10000000000 : ℝ)*X 0 2+(6320036157/10000000000 : ℝ)*X 1 0+(-3110731467/10000000000 : ℝ)*X 1 1+(-3110731467/10000000000 : ℝ)*X 1 2+(6320036157/10000000000 : ℝ)*X 2 0+(-3110731467/10000000000 : ℝ)*X 2 1+(-3110731467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310046_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-1842934809463026713717129160021/277284565000000000000000000000 : ℝ) := by norm_num
    linear_combination (16627/125000000000 : ℝ)*(base10) + (16627/125000000000 : ℝ)*(base12) + (6179/1000000000000 : ℝ)*(base27) + (397076497513/500000000000 : ℝ)*(base39) + (15883059781/40000000000 : ℝ)*(base40) + (44943157899/250000000000 : ℝ)*(base49) + (44943157899/250000000000 : ℝ)*(base59) + (161793/100000 : ℝ)*(major_s1_0) + (161793/100000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (2215455192707/1000000000000 : ℝ)*(sp_s1_0) + (1107727729369/500000000000 : ℝ)*(sp_s1_1) + (1107727729369/500000000000 : ℝ)*(sp_s1_2) + (999999993821/1000000000000 : ℝ)*(sp_s1_6) + (1107727729369/500000000000 : ℝ)*(f.sum) + (2554806814421/27147500000000000000000000 : ℝ)*base63 + (1374793765207/6786875000000000000000000 : ℝ)*base65 + (1374793765207/6786875000000000000000000 : ℝ)*base67 + (24920621148547/108590000000000000000000000 : ℝ)*base69 + (302155608369639191/554569130000000000000000000000 : ℝ)*base71 + (54649262409851/51070000000000000000000000 : ℝ)*base72 + (24920621148547/108590000000000000000000000 : ℝ)*base75 + (15106038590149/51070000000000000000000000 : ℝ)*base77 + (455317205189360809/554569130000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p010_b026 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=46 ∨ c=47 ∨ c=48 ∨ c=49 ∨ c=50 ∨ c=51 ∨ c=52 ∨ c=53 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact collision_c310046 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310047 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310048 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310049 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310050 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310051 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310052 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310053 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b026 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
