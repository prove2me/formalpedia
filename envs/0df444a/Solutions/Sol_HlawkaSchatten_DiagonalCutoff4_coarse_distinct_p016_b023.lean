-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p016_b023
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:01:46.763909+00:00
-- url     : https://prove2.me/submissions/9ecc66e1-3834-4652-805b-dde95753dbd0

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316048_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316048_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316048_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316049_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316049_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316049_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316050_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316050_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316050_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316051_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316051_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316051_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316052_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316052_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316052_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316053_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316053_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316053_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316053_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316053_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316054_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316054_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316054_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316054_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316048 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]]) : False := by
  have h0 := collision_c316048_s0 p hpa hpb X hX
  have h1 := collision_c316048_s1 p hpa hpb X hX h0
  exact collision_c316048_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316049 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]]) : False := by
  have h0 := collision_c316049_s0 p hpa hpb X hX
  have h1 := collision_c316049_s1 p hpa hpb X hX h0
  exact collision_c316049_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316050 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]]) : False := by
  have h0 := collision_c316050_s0 p hpa hpb X hX
  have h1 := collision_c316050_s1 p hpa hpb X hX h0
  exact collision_c316050_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316051 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  have h0 := collision_c316051_s0 p hpa hpb X hX
  have h1 := collision_c316051_s1 p hpa hpb X hX h0
  exact collision_c316051_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316052 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by
  have h0 := collision_c316052_s0 p hpa hpb X hX
  have h1 := collision_c316052_s1 p hpa hpb X hX h0
  exact collision_c316052_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316053 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : False := by
  have h0 := collision_c316053_s0 p hpa hpb X hX
  have h1 := collision_c316053_s1 p hpa hpb X hX h0
  have h2 := collision_c316053_s2 p hpa hpb X hX h1
  have h3 := collision_c316053_s3 p hpa hpb X hX h2
  exact collision_c316053_s4 p hpa hpb X hX h3

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316054 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : False := by
  have h0 := collision_c316054_s0 p hpa hpb X hX
  have h1 := collision_c316054_s1 p hpa hpb X hX h0
  have h2 := collision_c316054_s2 p hpa hpb X hX h1
  exact collision_c316054_s3 p hpa hpb X hX h2

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
theorem collision_support_c316047_s0_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-16730859/500000000 : ℝ)*x 0 + (-6226142521/10000000000 : ℝ)*x 1 + (5161103723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16730859/500000000 : ℝ)^39 ≤ (1392472057477/100000000000000 : ℝ)^31 := by
    have hnat : (16730859 : ℕ)^39*100000000000000^31 ≤ 1392472057477^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16730859 500000000 1392472057477 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6226142521/10000000000 : ℝ)^39 ≤ (6886908477071/12500000000000 : ℝ)^31 := by
    have hnat : (6226142521 : ℕ)^39*12500000000000^31 ≤ 6886908477071^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6226142521 10000000000 6886908477071 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5161103723/10000000000 : ℝ)^39 ≤ (870245202191/2000000000000 : ℝ)^31 := by
    have hnat : (5161103723 : ℕ)^39*2000000000000^31 ≤ 870245202191^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161103723 10000000000 870245202191 2000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16730859/500000000 : ℝ), (-6226142521/10000000000 : ℝ), (5161103723/10000000000 : ℝ)] ![(1392472057477/100000000000000 : ℝ), (6886908477071/12500000000000 : ℝ), (870245202191/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16730859/500000000 : ℝ)|^39 ≤ (1392472057477/100000000000000 : ℝ)^31
        have hw : |(-16730859/500000000 : ℝ)|=(16730859/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6226142521/10000000000 : ℝ)|^39 ≤ (6886908477071/12500000000000 : ℝ)^31
        have hw : |(-6226142521/10000000000 : ℝ)|=(6226142521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5161103723/10000000000 : ℝ)|^39 ≤ (870245202191/2000000000000 : ℝ)^31
        have hw : |(5161103723/10000000000 : ℝ)|=(5161103723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1025146089/2000000000 : ℝ)*x 0 + (3826806287/10000000000 : ℝ)*x 1 + (882876097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025146089/2000000000 : ℝ)^39 ≤ (539217573911/1250000000000 : ℝ)^31 := by
    have hnat : (1025146089 : ℕ)^39*1250000000000^31 ≤ 539217573911^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025146089 2000000000 539217573911 1250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3826806287/10000000000 : ℝ)^39 ≤ (29866296793183/100000000000000 : ℝ)^31 := by
    have hnat : (3826806287 : ℕ)^39*100000000000000^31 ≤ 29866296793183^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3826806287 10000000000 29866296793183 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (882876097/2500000000 : ℝ)^39 ≤ (13498148639511/50000000000000 : ℝ)^31 := by
    have hnat : (882876097 : ℕ)^39*50000000000000^31 ≤ 13498148639511^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882876097 2500000000 13498148639511 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1025146089/2000000000 : ℝ), (3826806287/10000000000 : ℝ), (882876097/2500000000 : ℝ)] ![(539217573911/1250000000000 : ℝ), (29866296793183/100000000000000 : ℝ), (13498148639511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1025146089/2000000000 : ℝ)|^39 ≤ (539217573911/1250000000000 : ℝ)^31
        have hw : |(1025146089/2000000000 : ℝ)|=(1025146089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3826806287/10000000000 : ℝ)|^39 ≤ (29866296793183/100000000000000 : ℝ)^31
        have hw : |(3826806287/10000000000 : ℝ)|=(3826806287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(882876097/2500000000 : ℝ)|^39 ≤ (13498148639511/50000000000000 : ℝ)^31
        have hw : |(882876097/2500000000 : ℝ)|=(882876097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5516595917/10000000000 : ℝ)*x 0 + (-191540859/500000000 : ℝ)*x 1 + (-3085431771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516595917/10000000000 : ℝ)^39 ≤ (47315743639103/100000000000000 : ℝ)^31 := by
    have hnat : (5516595917 : ℕ)^39*100000000000000^31 ≤ 47315743639103^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516595917 10000000000 47315743639103 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191540859/500000000 : ℝ)^39 ≤ (29905683312401/100000000000000 : ℝ)^31 := by
    have hnat : (191540859 : ℕ)^39*100000000000000^31 ≤ 29905683312401^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191540859 500000000 29905683312401 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3085431771/10000000000 : ℝ)^39 ≤ (22778573035303/100000000000000 : ℝ)^31 := by
    have hnat : (3085431771 : ℕ)^39*100000000000000^31 ≤ 22778573035303^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3085431771 10000000000 22778573035303 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516595917/10000000000 : ℝ), (-191540859/500000000 : ℝ), (-3085431771/10000000000 : ℝ)] ![(47315743639103/100000000000000 : ℝ), (29905683312401/100000000000000 : ℝ), (22778573035303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516595917/10000000000 : ℝ)|^39 ≤ (47315743639103/100000000000000 : ℝ)^31
        have hw : |(5516595917/10000000000 : ℝ)|=(5516595917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-191540859/500000000 : ℝ)|^39 ≤ (29905683312401/100000000000000 : ℝ)^31
        have hw : |(-191540859/500000000 : ℝ)|=(191540859/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3085431771/10000000000 : ℝ)|^39 ≤ (22778573035303/100000000000000 : ℝ)^31
        have hw : |(-3085431771/10000000000 : ℝ)|=(3085431771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1332627883/2000000000 : ℝ)*x 0 + (32363/2000000000 : ℝ)*x 1 + (603347601/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1332627883/2000000000 : ℝ)^39 ≤ (60003513466043/100000000000000 : ℝ)^31 := by
    have hnat : (1332627883 : ℕ)^39*100000000000000^31 ≤ 60003513466043^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332627883 2000000000 60003513466043 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32363/2000000000 : ℝ)^39 ≤ (23473429/25000000000000 : ℝ)^31 := by
    have hnat : (32363 : ℕ)^39*25000000000000^31 ≤ 23473429^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32363 2000000000 23473429 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (603347601/1250000000 : ℝ)^39 ≤ (19998196312499/50000000000000 : ℝ)^31 := by
    have hnat : (603347601 : ℕ)^39*50000000000000^31 ≤ 19998196312499^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603347601 1250000000 19998196312499 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1332627883/2000000000 : ℝ), (32363/2000000000 : ℝ), (603347601/1250000000 : ℝ)] ![(60003513466043/100000000000000 : ℝ), (23473429/25000000000000 : ℝ), (19998196312499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1332627883/2000000000 : ℝ)|^39 ≤ (60003513466043/100000000000000 : ℝ)^31
        have hw : |(1332627883/2000000000 : ℝ)|=(1332627883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32363/2000000000 : ℝ)|^39 ≤ (23473429/25000000000000 : ℝ)^31
        have hw : |(32363/2000000000 : ℝ)|=(32363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(603347601/1250000000 : ℝ)|^39 ≤ (19998196312499/50000000000000 : ℝ)^31
        have hw : |(603347601/1250000000 : ℝ)|=(603347601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-18237099/2500000000 : ℝ)*x 0 + (-7906645721/10000000000 : ℝ)*x 1 + (3362263561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18237099/2500000000 : ℝ)^39 ≤ (51224290109/25000000000000 : ℝ)^31 := by
    have hnat : (18237099 : ℕ)^39*25000000000000^31 ≤ 51224290109^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18237099 2500000000 51224290109 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7906645721/10000000000 : ℝ)^39 ≤ (74416237193733/100000000000000 : ℝ)^31 := by
    have hnat : (7906645721 : ℕ)^39*100000000000000^31 ≤ 74416237193733^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7906645721 10000000000 74416237193733 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3362263561/10000000000 : ℝ)^39 ≤ (5075773128001/20000000000000 : ℝ)^31 := by
    have hnat : (3362263561 : ℕ)^39*20000000000000^31 ≤ 5075773128001^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3362263561 10000000000 5075773128001 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18237099/2500000000 : ℝ), (-7906645721/10000000000 : ℝ), (3362263561/10000000000 : ℝ)] ![(51224290109/25000000000000 : ℝ), (74416237193733/100000000000000 : ℝ), (5075773128001/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18237099/2500000000 : ℝ)|^39 ≤ (51224290109/25000000000000 : ℝ)^31
        have hw : |(-18237099/2500000000 : ℝ)|=(18237099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7906645721/10000000000 : ℝ)|^39 ≤ (74416237193733/100000000000000 : ℝ)^31
        have hw : |(-7906645721/10000000000 : ℝ)|=(7906645721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3362263561/10000000000 : ℝ)|^39 ≤ (5075773128001/20000000000000 : ℝ)^31
        have hw : |(3362263561/10000000000 : ℝ)|=(3362263561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1489272059/5000000000 : ℝ)*x 0 + (2750316731/5000000000 : ℝ)*x 1 + (3948511909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1489272059/5000000000 : ℝ)^39 ≤ (5447574173719/25000000000000 : ℝ)^31 := by
    have hnat : (1489272059 : ℕ)^39*25000000000000^31 ≤ 5447574173719^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489272059 5000000000 5447574173719 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2750316731/5000000000 : ℝ)^39 ≤ (47143566771989/100000000000000 : ℝ)^31 := by
    have hnat : (2750316731 : ℕ)^39*100000000000000^31 ≤ 47143566771989^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750316731 5000000000 47143566771989 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3948511909/10000000000 : ℝ)^39 ≤ (15533068256969/50000000000000 : ℝ)^31 := by
    have hnat : (3948511909 : ℕ)^39*50000000000000^31 ≤ 15533068256969^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3948511909 10000000000 15533068256969 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1489272059/5000000000 : ℝ), (2750316731/5000000000 : ℝ), (3948511909/10000000000 : ℝ)] ![(5447574173719/25000000000000 : ℝ), (47143566771989/100000000000000 : ℝ), (15533068256969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1489272059/5000000000 : ℝ)|^39 ≤ (5447574173719/25000000000000 : ℝ)^31
        have hw : |(1489272059/5000000000 : ℝ)|=(1489272059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2750316731/5000000000 : ℝ)|^39 ≤ (47143566771989/100000000000000 : ℝ)^31
        have hw : |(2750316731/5000000000 : ℝ)|=(2750316731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3948511909/10000000000 : ℝ)|^39 ≤ (15533068256969/50000000000000 : ℝ)^31
        have hw : |(3948511909/10000000000 : ℝ)|=(3948511909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5770101/12500000 : ℝ)*x 0 + (-3359915323/10000000000 : ℝ)*x 1 + (-1130148797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5770101/12500000 : ℝ)^39 ≤ (37812403189597/100000000000000 : ℝ)^31 := by
    have hnat : (5770101 : ℕ)^39*100000000000000^31 ≤ 37812403189597^31*12500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5770101 12500000 37812403189597 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3359915323/10000000000 : ℝ)^39 ≤ (25356568645261/100000000000000 : ℝ)^31 := by
    have hnat : (3359915323 : ℕ)^39*100000000000000^31 ≤ 25356568645261^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3359915323 10000000000 25356568645261 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130148797/2500000000 : ℝ)^39 ≤ (1841551407569/5000000000000 : ℝ)^31 := by
    have hnat : (1130148797 : ℕ)^39*5000000000000^31 ≤ 1841551407569^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130148797 2500000000 1841551407569 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5770101/12500000 : ℝ), (-3359915323/10000000000 : ℝ), (-1130148797/2500000000 : ℝ)] ![(37812403189597/100000000000000 : ℝ), (25356568645261/100000000000000 : ℝ), (1841551407569/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5770101/12500000 : ℝ)|^39 ≤ (37812403189597/100000000000000 : ℝ)^31
        have hw : |(5770101/12500000 : ℝ)|=(5770101/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3359915323/10000000000 : ℝ)|^39 ≤ (25356568645261/100000000000000 : ℝ)^31
        have hw : |(-3359915323/10000000000 : ℝ)|=(3359915323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1130148797/2500000000 : ℝ)|^39 ≤ (1841551407569/5000000000000 : ℝ)^31
        have hw : |(-1130148797/2500000000 : ℝ)|=(1130148797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5042577051/10000000000 : ℝ)*x 0 + (5967239/2000000000 : ℝ)*x 1 + (1614185547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5042577051/10000000000 : ℝ)^39 ≤ (264117837469/625000000000 : ℝ)^31 := by
    have hnat : (5042577051 : ℕ)^39*625000000000^31 ≤ 264117837469^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5042577051 10000000000 264117837469 625000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5967239/2000000000 : ℝ)^39 ≤ (33268584893/50000000000000 : ℝ)^31 := by
    have hnat : (5967239 : ℕ)^39*50000000000000^31 ≤ 33268584893^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5967239 2000000000 33268584893 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1614185547/2500000000 : ℝ)^39 ≤ (57674608817383/100000000000000 : ℝ)^31 := by
    have hnat : (1614185547 : ℕ)^39*100000000000000^31 ≤ 57674608817383^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614185547 2500000000 57674608817383 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5042577051/10000000000 : ℝ), (5967239/2000000000 : ℝ), (1614185547/2500000000 : ℝ)] ![(264117837469/625000000000 : ℝ), (33268584893/50000000000000 : ℝ), (57674608817383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5042577051/10000000000 : ℝ)|^39 ≤ (264117837469/625000000000 : ℝ)^31
        have hw : |(5042577051/10000000000 : ℝ)|=(5042577051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5967239/2000000000 : ℝ)|^39 ≤ (33268584893/50000000000000 : ℝ)^31
        have hw : |(5967239/2000000000 : ℝ)|=(5967239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1614185547/2500000000 : ℝ)|^39 ≤ (57674608817383/100000000000000 : ℝ)^31
        have hw : |(1614185547/2500000000 : ℝ)|=(1614185547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (625863/10000000000 : ℝ)*x 0 + (-1151635481/2500000000 : ℝ)*x 1 + (1372755509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (625863/10000000000 : ℝ)^39 ≤ (128718137/25000000000000 : ℝ)^31 := by
    have hnat : (625863 : ℕ)^39*25000000000000^31 ≤ 128718137^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625863 10000000000 128718137 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1151635481/2500000000 : ℝ)^39 ≤ (37714127721683/100000000000000 : ℝ)^31 := by
    have hnat : (1151635481 : ℕ)^39*100000000000000^31 ≤ 37714127721683^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151635481 2500000000 37714127721683 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372755509/2000000000 : ℝ)^39 ≤ (12457071478583/20000000000000 : ℝ)^31 := by
    have hnat : (1372755509 : ℕ)^39*20000000000000^31 ≤ 12457071478583^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372755509 2000000000 12457071478583 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(625863/10000000000 : ℝ), (-1151635481/2500000000 : ℝ), (1372755509/2000000000 : ℝ)] ![(128718137/25000000000000 : ℝ), (37714127721683/100000000000000 : ℝ), (12457071478583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(625863/10000000000 : ℝ)|^39 ≤ (128718137/25000000000000 : ℝ)^31
        have hw : |(625863/10000000000 : ℝ)|=(625863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1151635481/2500000000 : ℝ)|^39 ≤ (37714127721683/100000000000000 : ℝ)^31
        have hw : |(-1151635481/2500000000 : ℝ)|=(1151635481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372755509/2000000000 : ℝ)|^39 ≤ (12457071478583/20000000000000 : ℝ)^31
        have hw : |(1372755509/2000000000 : ℝ)|=(1372755509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1477697779/5000000000 : ℝ)*x 0 + (465735317/1000000000 : ℝ)*x 1 + (4844799287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1477697779/5000000000 : ℝ)^39 ≤ (2697182321137/12500000000000 : ℝ)^31 := by
    have hnat : (1477697779 : ℕ)^39*12500000000000^31 ≤ 2697182321137^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477697779 5000000000 2697182321137 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465735317/1000000000 : ℝ)^39 ≤ (38238220040591/100000000000000 : ℝ)^31 := by
    have hnat : (465735317 : ℕ)^39*100000000000000^31 ≤ 38238220040591^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465735317 1000000000 38238220040591 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4844799287/10000000000 : ℝ)^39 ≤ (40184321379233/100000000000000 : ℝ)^31 := by
    have hnat : (4844799287 : ℕ)^39*100000000000000^31 ≤ 40184321379233^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844799287 10000000000 40184321379233 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1477697779/5000000000 : ℝ), (465735317/1000000000 : ℝ), (4844799287/10000000000 : ℝ)] ![(2697182321137/12500000000000 : ℝ), (38238220040591/100000000000000 : ℝ), (40184321379233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1477697779/5000000000 : ℝ)|^39 ≤ (2697182321137/12500000000000 : ℝ)^31
        have hw : |(1477697779/5000000000 : ℝ)|=(1477697779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(465735317/1000000000 : ℝ)|^39 ≤ (38238220040591/100000000000000 : ℝ)^31
        have hw : |(465735317/1000000000 : ℝ)|=(465735317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4844799287/10000000000 : ℝ)|^39 ≤ (40184321379233/100000000000000 : ℝ)^31
        have hw : |(4844799287/10000000000 : ℝ)|=(4844799287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3511194143/5000000000 : ℝ)*x 0 + (-2478772011/10000000000 : ℝ)*x 1 + (-131340683/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3511194143/5000000000 : ℝ)^39 ≤ (64101475060673/100000000000000 : ℝ)^31 := by
    have hnat : (3511194143 : ℕ)^39*100000000000000^31 ≤ 64101475060673^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3511194143 5000000000 64101475060673 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2478772011/10000000000 : ℝ)^39 ≤ (4323650188327/25000000000000 : ℝ)^31 := by
    have hnat : (2478772011 : ℕ)^39*25000000000000^31 ≤ 4323650188327^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2478772011 10000000000 4323650188327 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131340683/500000000 : ℝ)^39 ≤ (9301962082027/50000000000000 : ℝ)^31 := by
    have hnat : (131340683 : ℕ)^39*50000000000000^31 ≤ 9301962082027^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131340683 500000000 9301962082027 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3511194143/5000000000 : ℝ), (-2478772011/10000000000 : ℝ), (-131340683/500000000 : ℝ)] ![(64101475060673/100000000000000 : ℝ), (4323650188327/25000000000000 : ℝ), (9301962082027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3511194143/5000000000 : ℝ)|^39 ≤ (64101475060673/100000000000000 : ℝ)^31
        have hw : |(3511194143/5000000000 : ℝ)|=(3511194143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2478772011/10000000000 : ℝ)|^39 ≤ (4323650188327/25000000000000 : ℝ)^31
        have hw : |(-2478772011/10000000000 : ℝ)|=(2478772011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131340683/500000000 : ℝ)|^39 ≤ (9301962082027/50000000000000 : ℝ)^31
        have hw : |(-131340683/500000000 : ℝ)|=(131340683/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4129714459/5000000000 : ℝ)*x 0 + (-80028267/5000000000 : ℝ)*x 1 + (574791959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4129714459/5000000000 : ℝ)^39 ≤ (78617235281499/100000000000000 : ℝ)^31 := by
    have hnat : (4129714459 : ℕ)^39*100000000000000^31 ≤ 78617235281499^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129714459 5000000000 78617235281499 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80028267/5000000000 : ℝ)^39 ≤ (550630284823/100000000000000 : ℝ)^31 := by
    have hnat : (80028267 : ℕ)^39*100000000000000^31 ≤ 550630284823^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80028267 5000000000 550630284823 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (574791959/2000000000 : ℝ)^39 ≤ (1302008401183/6250000000000 : ℝ)^31 := by
    have hnat : (574791959 : ℕ)^39*6250000000000^31 ≤ 1302008401183^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574791959 2000000000 1302008401183 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4129714459/5000000000 : ℝ), (-80028267/5000000000 : ℝ), (574791959/2000000000 : ℝ)] ![(78617235281499/100000000000000 : ℝ), (550630284823/100000000000000 : ℝ), (1302008401183/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4129714459/5000000000 : ℝ)|^39 ≤ (78617235281499/100000000000000 : ℝ)^31
        have hw : |(4129714459/5000000000 : ℝ)|=(4129714459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-80028267/5000000000 : ℝ)|^39 ≤ (550630284823/100000000000000 : ℝ)^31
        have hw : |(-80028267/5000000000 : ℝ)|=(80028267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(574791959/2000000000 : ℝ)|^39 ≤ (1302008401183/6250000000000 : ℝ)^31
        have hw : |(574791959/2000000000 : ℝ)|=(574791959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-182369849/5000000000 : ℝ)*x 0 + (-266015507/312500000 : ℝ)*x 1 + (1210467199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182369849/5000000000 : ℝ)^39 ≤ (1551964853157/100000000000000 : ℝ)^31 := by
    have hnat : (182369849 : ℕ)^39*100000000000000^31 ≤ 1551964853157^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182369849 5000000000 1551964853157 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266015507/312500000 : ℝ)^39 ≤ (20414893423467/25000000000000 : ℝ)^31 := by
    have hnat : (266015507 : ℕ)^39*25000000000000^31 ≤ 20414893423467^31*312500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266015507 312500000 20414893423467 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1210467199/5000000000 : ℝ)^39 ≤ (16788461443253/100000000000000 : ℝ)^31 := by
    have hnat : (1210467199 : ℕ)^39*100000000000000^31 ≤ 16788461443253^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210467199 5000000000 16788461443253 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-182369849/5000000000 : ℝ), (-266015507/312500000 : ℝ), (1210467199/5000000000 : ℝ)] ![(1551964853157/100000000000000 : ℝ), (20414893423467/25000000000000 : ℝ), (16788461443253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-182369849/5000000000 : ℝ)|^39 ≤ (1551964853157/100000000000000 : ℝ)^31
        have hw : |(-182369849/5000000000 : ℝ)|=(182369849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266015507/312500000 : ℝ)|^39 ≤ (20414893423467/25000000000000 : ℝ)^31
        have hw : |(-266015507/312500000 : ℝ)|=(266015507/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1210467199/5000000000 : ℝ)|^39 ≤ (16788461443253/100000000000000 : ℝ)^31
        have hw : |(1210467199/5000000000 : ℝ)|=(1210467199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1362928923/2000000000 : ℝ)*x 0 + (790832123/2500000000 : ℝ)*x 1 + (1093323849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1362928923/2000000000 : ℝ)^39 ≤ (30862479872851/50000000000000 : ℝ)^31 := by
    have hnat : (1362928923 : ℕ)^39*50000000000000^31 ≤ 30862479872851^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362928923 2000000000 30862479872851 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (790832123/2500000000 : ℝ)^39 ≤ (2938050693539/12500000000000 : ℝ)^31 := by
    have hnat : (790832123 : ℕ)^39*12500000000000^31 ≤ 2938050693539^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790832123 2500000000 2938050693539 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093323849/5000000000 : ℝ)^39 ≤ (14770634689433/100000000000000 : ℝ)^31 := by
    have hnat : (1093323849 : ℕ)^39*100000000000000^31 ≤ 14770634689433^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093323849 5000000000 14770634689433 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1362928923/2000000000 : ℝ), (790832123/2500000000 : ℝ), (1093323849/5000000000 : ℝ)] ![(30862479872851/50000000000000 : ℝ), (2938050693539/12500000000000 : ℝ), (14770634689433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1362928923/2000000000 : ℝ)|^39 ≤ (30862479872851/50000000000000 : ℝ)^31
        have hw : |(1362928923/2000000000 : ℝ)|=(1362928923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(790832123/2500000000 : ℝ)|^39 ≤ (2938050693539/12500000000000 : ℝ)^31
        have hw : |(790832123/2500000000 : ℝ)|=(790832123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093323849/5000000000 : ℝ)|^39 ≤ (14770634689433/100000000000000 : ℝ)^31
        have hw : |(1093323849/5000000000 : ℝ)|=(1093323849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (108470081/500000000 : ℝ)*x 0 + (-7212370621/10000000000 : ℝ)*x 1 + (-2680666117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108470081/500000000 : ℝ)^39 ≤ (3656056189541/25000000000000 : ℝ)^31 := by
    have hnat : (108470081 : ℕ)^39*25000000000000^31 ≤ 3656056189541^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108470081 500000000 3656056189541 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7212370621/10000000000 : ℝ)^39 ≤ (33145381107589/50000000000000 : ℝ)^31 := by
    have hnat : (7212370621 : ℕ)^39*50000000000000^31 ≤ 33145381107589^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7212370621 10000000000 33145381107589 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2680666117/10000000000 : ℝ)^39 ≤ (9542506508089/50000000000000 : ℝ)^31 := by
    have hnat : (2680666117 : ℕ)^39*50000000000000^31 ≤ 9542506508089^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680666117 10000000000 9542506508089 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108470081/500000000 : ℝ), (-7212370621/10000000000 : ℝ), (-2680666117/10000000000 : ℝ)] ![(3656056189541/25000000000000 : ℝ), (33145381107589/50000000000000 : ℝ), (9542506508089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108470081/500000000 : ℝ)|^39 ≤ (3656056189541/25000000000000 : ℝ)^31
        have hw : |(108470081/500000000 : ℝ)|=(108470081/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7212370621/10000000000 : ℝ)|^39 ≤ (33145381107589/50000000000000 : ℝ)^31
        have hw : |(-7212370621/10000000000 : ℝ)|=(7212370621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2680666117/10000000000 : ℝ)|^39 ≤ (9542506508089/50000000000000 : ℝ)^31
        have hw : |(-2680666117/10000000000 : ℝ)|=(2680666117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s0_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2080504881/2500000000 : ℝ)*x 0 + (141537/10000000000 : ℝ)*x 1 + (2852039877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080504881/2500000000 : ℝ)^39 ≤ (15873496183209/20000000000000 : ℝ)^31 := by
    have hnat : (2080504881 : ℕ)^39*20000000000000^31 ≤ 15873496183209^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080504881 2500000000 15873496183209 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141537/10000000000 : ℝ)^39 ≤ (4958629/6250000000000 : ℝ)^31 := by
    have hnat : (141537 : ℕ)^39*6250000000000^31 ≤ 4958629^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141537 10000000000 4958629 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2852039877/10000000000 : ℝ)^39 ≤ (20632439739977/100000000000000 : ℝ)^31 := by
    have hnat : (2852039877 : ℕ)^39*100000000000000^31 ≤ 20632439739977^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852039877 10000000000 20632439739977 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2080504881/2500000000 : ℝ), (141537/10000000000 : ℝ), (2852039877/10000000000 : ℝ)] ![(15873496183209/20000000000000 : ℝ), (4958629/6250000000000 : ℝ), (20632439739977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2080504881/2500000000 : ℝ)|^39 ≤ (15873496183209/20000000000000 : ℝ)^31
        have hw : |(2080504881/2500000000 : ℝ)|=(2080504881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141537/10000000000 : ℝ)|^39 ≤ (4958629/6250000000000 : ℝ)^31
        have hw : |(141537/10000000000 : ℝ)|=(141537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2852039877/10000000000 : ℝ)|^39 ≤ (20632439739977/100000000000000 : ℝ)^31
        have hw : |(2852039877/10000000000 : ℝ)|=(2852039877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-789049399/5000000000 : ℝ)*x 0 + (-5374423311/10000000000 : ℝ)*x 1 + (2622961/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (789049399/5000000000 : ℝ)^39 ≤ (1959887180377/20000000000000 : ℝ)^31 := by
    have hnat : (789049399 : ℕ)^39*20000000000000^31 ≤ 1959887180377^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789049399 5000000000 1959887180377 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374423311/10000000000 : ℝ)^39 ≤ (22893389597287/50000000000000 : ℝ)^31 := by
    have hnat : (5374423311 : ℕ)^39*50000000000000^31 ≤ 22893389597287^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374423311 10000000000 22893389597287 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622961/5000000 : ℝ)^39 ≤ (11103446221189/25000000000000 : ℝ)^31 := by
    have hnat : (2622961 : ℕ)^39*25000000000000^31 ≤ 11103446221189^31*5000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622961 5000000 11103446221189 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-789049399/5000000000 : ℝ), (-5374423311/10000000000 : ℝ), (2622961/5000000 : ℝ)] ![(1959887180377/20000000000000 : ℝ), (22893389597287/50000000000000 : ℝ), (11103446221189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-789049399/5000000000 : ℝ)|^39 ≤ (1959887180377/20000000000000 : ℝ)^31
        have hw : |(-789049399/5000000000 : ℝ)|=(789049399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5374423311/10000000000 : ℝ)|^39 ≤ (22893389597287/50000000000000 : ℝ)^31
        have hw : |(-5374423311/10000000000 : ℝ)|=(5374423311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622961/5000000 : ℝ)|^39 ≤ (11103446221189/25000000000000 : ℝ)^31
        have hw : |(2622961/5000000 : ℝ)|=(2622961/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2527440971/5000000000 : ℝ)*x 0 + (791213359/2000000000 : ℝ)*x 1 + (869178789/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2527440971/5000000000 : ℝ)^39 ≤ (8477725288567/20000000000000 : ℝ)^31 := by
    have hnat : (2527440971 : ℕ)^39*20000000000000^31 ≤ 8477725288567^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2527440971 5000000000 8477725288567 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (791213359/2000000000 : ℝ)^39 ≤ (31140934822841/100000000000000 : ℝ)^31 := by
    have hnat : (791213359 : ℕ)^39*100000000000000^31 ≤ 31140934822841^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791213359 2000000000 31140934822841 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (869178789/2500000000 : ℝ)^39 ≤ (13235219361719/50000000000000 : ℝ)^31 := by
    have hnat : (869178789 : ℕ)^39*50000000000000^31 ≤ 13235219361719^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869178789 2500000000 13235219361719 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2527440971/5000000000 : ℝ), (791213359/2000000000 : ℝ), (869178789/2500000000 : ℝ)] ![(8477725288567/20000000000000 : ℝ), (31140934822841/100000000000000 : ℝ), (13235219361719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2527440971/5000000000 : ℝ)|^39 ≤ (8477725288567/20000000000000 : ℝ)^31
        have hw : |(2527440971/5000000000 : ℝ)|=(2527440971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(791213359/2000000000 : ℝ)|^39 ≤ (31140934822841/100000000000000 : ℝ)^31
        have hw : |(791213359/2000000000 : ℝ)|=(791213359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(869178789/2500000000 : ℝ)|^39 ≤ (13235219361719/50000000000000 : ℝ)^31
        have hw : |(869178789/2500000000 : ℝ)|=(869178789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4922715579/10000000000 : ℝ)*x 0 + (-509073329/1250000000 : ℝ)*x 1 + (-350084401/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4922715579/10000000000 : ℝ)^39 ≤ (20499521068321/50000000000000 : ℝ)^31 := by
    have hnat : (4922715579 : ℕ)^39*50000000000000^31 ≤ 20499521068321^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4922715579 10000000000 20499521068321 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509073329/1250000000 : ℝ)^39 ≤ (32299195652771/100000000000000 : ℝ)^31 := by
    have hnat : (509073329 : ℕ)^39*100000000000000^31 ≤ 32299195652771^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509073329 1250000000 32299195652771 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (350084401/1000000000 : ℝ)^39 ≤ (26701762199307/100000000000000 : ℝ)^31 := by
    have hnat : (350084401 : ℕ)^39*100000000000000^31 ≤ 26701762199307^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350084401 1000000000 26701762199307 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4922715579/10000000000 : ℝ), (-509073329/1250000000 : ℝ), (-350084401/1000000000 : ℝ)] ![(20499521068321/50000000000000 : ℝ), (32299195652771/100000000000000 : ℝ), (26701762199307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4922715579/10000000000 : ℝ)|^39 ≤ (20499521068321/50000000000000 : ℝ)^31
        have hw : |(4922715579/10000000000 : ℝ)|=(4922715579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509073329/1250000000 : ℝ)|^39 ≤ (32299195652771/100000000000000 : ℝ)^31
        have hw : |(-509073329/1250000000 : ℝ)|=(509073329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-350084401/1000000000 : ℝ)|^39 ≤ (26701762199307/100000000000000 : ℝ)^31
        have hw : |(-350084401/1000000000 : ℝ)|=(350084401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316047_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1234180911/2000000000 : ℝ)*x 0 + (-1489904803/10000000000 : ℝ)*x 1 + (4478833003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1234180911/2000000000 : ℝ)^39 ≤ (10896205792261/20000000000000 : ℝ)^31 := by
    have hnat : (1234180911 : ℕ)^39*20000000000000^31 ≤ 10896205792261^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234180911 2000000000 10896205792261 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1489904803/10000000000 : ℝ)^39 ≤ (45577455753/500000000000 : ℝ)^31 := by
    have hnat : (1489904803 : ℕ)^39*500000000000^31 ≤ 45577455753^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489904803 10000000000 45577455753 500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478833003/10000000000 : ℝ)^39 ≤ (2275217492067/6250000000000 : ℝ)^31 := by
    have hnat : (4478833003 : ℕ)^39*6250000000000^31 ≤ 2275217492067^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478833003 10000000000 2275217492067 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1234180911/2000000000 : ℝ), (-1489904803/10000000000 : ℝ), (4478833003/10000000000 : ℝ)] ![(10896205792261/20000000000000 : ℝ), (45577455753/500000000000 : ℝ), (2275217492067/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1234180911/2000000000 : ℝ)|^39 ≤ (10896205792261/20000000000000 : ℝ)^31
        have hw : |(1234180911/2000000000 : ℝ)|=(1234180911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1489904803/10000000000 : ℝ)|^39 ≤ (45577455753/500000000000 : ℝ)^31
        have hw : |(-1489904803/10000000000 : ℝ)|=(1489904803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478833003/10000000000 : ℝ)|^39 ≤ (2275217492067/6250000000000 : ℝ)^31
        have hw : |(4478833003/10000000000 : ℝ)|=(4478833003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316047 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (173433/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-16730859/500000000 : ℝ)*X 0 0+(-6226142521/10000000000 : ℝ)*X 0 1+(5161103723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1025146089/2000000000 : ℝ)*X 1 0+(3826806287/10000000000 : ℝ)*X 1 1+(882876097/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5516595917/10000000000 : ℝ)*X 2 0+(-191540859/500000000 : ℝ)*X 2 1+(-3085431771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1332627883/2000000000 : ℝ)*X 0 0+(32363/2000000000 : ℝ)*X 0 1+(603347601/1250000000 : ℝ)*X 0 2+(1332627883/2000000000 : ℝ)*X 1 0+(32363/2000000000 : ℝ)*X 1 1+(603347601/1250000000 : ℝ)*X 1 2+(1332627883/2000000000 : ℝ)*X 2 0+(32363/2000000000 : ℝ)*X 2 1+(603347601/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-18237099/2500000000 : ℝ)*X 0 0+(-7906645721/10000000000 : ℝ)*X 0 1+(3362263561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1489272059/5000000000 : ℝ)*X 1 0+(2750316731/5000000000 : ℝ)*X 1 1+(3948511909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((5770101/12500000 : ℝ)*X 2 0+(-3359915323/10000000000 : ℝ)*X 2 1+(-1130148797/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((5042577051/10000000000 : ℝ)*X 0 0+(5967239/2000000000 : ℝ)*X 0 1+(1614185547/2500000000 : ℝ)*X 0 2+(5042577051/10000000000 : ℝ)*X 1 0+(5967239/2000000000 : ℝ)*X 1 1+(1614185547/2500000000 : ℝ)*X 1 2+(5042577051/10000000000 : ℝ)*X 2 0+(5967239/2000000000 : ℝ)*X 2 1+(1614185547/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((625863/10000000000 : ℝ)*X 0 0+(-1151635481/2500000000 : ℝ)*X 0 1+(1372755509/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1477697779/5000000000 : ℝ)*X 1 0+(465735317/1000000000 : ℝ)*X 1 1+(4844799287/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3511194143/5000000000 : ℝ)*X 2 0+(-2478772011/10000000000 : ℝ)*X 2 1+(-131340683/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((4129714459/5000000000 : ℝ)*X 0 0+(-80028267/5000000000 : ℝ)*X 0 1+(574791959/2000000000 : ℝ)*X 0 2+(4129714459/5000000000 : ℝ)*X 1 0+(-80028267/5000000000 : ℝ)*X 1 1+(574791959/2000000000 : ℝ)*X 1 2+(4129714459/5000000000 : ℝ)*X 2 0+(-80028267/5000000000 : ℝ)*X 2 1+(574791959/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-182369849/5000000000 : ℝ)*X 0 0+(-266015507/312500000 : ℝ)*X 0 1+(1210467199/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1362928923/2000000000 : ℝ)*X 1 0+(790832123/2500000000 : ℝ)*X 1 1+(1093323849/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((108470081/500000000 : ℝ)*X 2 0+(-7212370621/10000000000 : ℝ)*X 2 1+(-2680666117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((2080504881/2500000000 : ℝ)*X 0 0+(141537/10000000000 : ℝ)*X 0 1+(2852039877/10000000000 : ℝ)*X 0 2+(2080504881/2500000000 : ℝ)*X 1 0+(141537/10000000000 : ℝ)*X 1 1+(2852039877/10000000000 : ℝ)*X 1 2+(2080504881/2500000000 : ℝ)*X 2 0+(141537/10000000000 : ℝ)*X 2 1+(2852039877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((66777/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66777/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (38134464247641549/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (372689418479/1000000000000 : ℝ)*(base3) + (1112854863617/1000000000000 : ℝ)*(base7) + (145561772649/500000000000 : ℝ)*(base50) + (2783729/500000000000 : ℝ)*(base54) + (2158366079239/1000000000000 : ℝ)*(major_s0_0) + (2158366079239/1000000000000 : ℝ)*(major_s0_1) + (107918025589/50000000000 : ℝ)*(major_s0_2) + (98689/500000000000 : ℝ)*(sp_s0_0) + (7672057/500000000000 : ℝ)*(sp_s0_2) + (1227864513399/500000000000 : ℝ)*(sp_s0_7) + (565683728531/200000000000 : ℝ)*(sp_s0_8) + (2455700658091/1000000000000 : ℝ)*(sp_s0_9) + (1957807744471/1000000000000 : ℝ)*(sp_s0_13) + (7654513/1000000000000 : ℝ)*(sp_s0_23) + (1217647866791/1000000000000 : ℝ)*(f.failure) + (153483076511/62500000000 : ℝ)*(f.sum) + (1695148540674219/10000000000000000000000000000 : ℝ)*base62 + (148003003672821/250000000000000000000000000 : ℝ)*base64 + (1523453337362671/5000000000000000000000000000 : ℝ)*base66 + (147735541645211/500000000000000000000000000 : ℝ)*base69 + (2037934235508721/10000000000000000000000000000 : ℝ)*base71 + (1345619548862671/5000000000000000000000000000 : ℝ)*base72 + (1819735869421561/10000000000000000000000000000 : ℝ)*base75 + (3078641070578439/10000000000000000000000000000 : ℝ)*base76 + (123817291387329/2500000000000000000000000000 : ℝ)*base79 + (127713/100000000000000000 : ℝ)*base86 + (127713/100000000000000000 : ℝ)*base88 + (27713/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-58877/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-58877/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (285370811651886393393/25000000000000000000000000 : ℝ) := by norm_num
    linear_combination (834237261189/1000000000000 : ℝ)*(base7) + (62054305897/125000000000 : ℝ)*(base40) + (4185677/1000000000000 : ℝ)*(base53) + (4193244869/50000000000 : ℝ)*(base59) + (2048347502263/1000000000000 : ℝ)*(major_s0_0) + (2048347502263/1000000000000 : ℝ)*(major_s0_1) + (1024171658293/500000000000 : ℝ)*(major_s0_2) + (22251687/1000000000000 : ℝ)*(sp_s0_1) + (8668093/1000000000000 : ℝ)*(sp_s0_6) + (2458825511893/1000000000000 : ℝ)*(sp_s0_14) + (2458803260207/1000000000000 : ℝ)*(sp_s0_15) + (245882969757/100000000000 : ℝ)*(sp_s0_16) + (1989227002403/1000000000000 : ℝ)*(sp_s0_20) + (291094817/500000000000 : ℝ)*(sp_s0_27) + (57779029947/50000000000 : ℝ)*(f.failure) + (245882969757/100000000000 : ℝ)*(f.sum) + (5018419934926049/10000000000000000000000000000 : ℝ)*base62 + (1239973413542877/2500000000000000000000000000 : ℝ)*base64 + (386142920301793/5000000000000000000000000000 : ℝ)*base67 + (2464337928688693/5000000000000000000000000000 : ℝ)*base68 + (2126415215279829/10000000000000000000000000000 : ℝ)*base71 + (4676923219698207/5000000000000000000000000000 : ℝ)*base72 + (1158281424548663/10000000000000000000000000000 : ℝ)*base74 + (2008541579451337/10000000000000000000000000000 : ℝ)*base77 + (1908538800448207/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (379/5000000000000000 : ℝ)*base87 + (379/5000000000000000 : ℝ)*base89 + (379/5000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38407/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38407/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9173214357244231598331/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54283650261/1000000000000 : ℝ)*(base3) + (1148040338897/1000000000000 : ℝ)*(base7) + (5657943/1000000000000 : ℝ)*(base34) + (72051318461/500000000000 : ℝ)*(base40) + (11245161/1000000000000 : ℝ)*(base43) + (113110621589/1000000000000 : ℝ)*(base50) + (347293967441/200000000000 : ℝ)*(major_s0_0) + (1736464249987/1000000000000 : ℝ)*(major_s0_1) + (434118873787/250000000000 : ℝ)*(major_s0_2) + (2653959/200000000000 : ℝ)*(sp_s0_2) + (228699800471/125000000000 : ℝ)*(sp_s0_21) + (1883898957133/1000000000000 : ℝ)*(sp_s0_22) + (457397697979/250000000000 : ℝ)*(sp_s0_23) + (207338822141/100000000000 : ℝ)*(sp_s0_27) + (244909297679/250000000000 : ℝ)*(f.failure) + (228701913359/125000000000 : ℝ)*(f.sum) + (690763535985373/2000000000000000000000000000 : ℝ)*base63 + (375383937300243/1250000000000000000000000000 : ℝ)*base64 + (2594117844852043/5000000000000000000000000000 : ℝ)*base66 + (715253367017387/2500000000000000000000000000 : ℝ)*base68 + (3199486159736851/10000000000000000000000000000 : ℝ)*base71 + (518582901239849/1000000000000000000000000000 : ℝ)*base72 + (1953620513996413/10000000000000000000000000000 : ℝ)*base75 + (537106778427759/2000000000000000000000000000 : ℝ)*base77 + (507711844818911/625000000000000000000000000 : ℝ)*base78 + (13497/25000000000000000 : ℝ)*base86 + (13497/25000000000000000 : ℝ)*base88 + (13497/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (66777/100000 : ℝ) ^ (19/4 : ℝ) ≤ (734425587367902137/5000000000000000000 : ℝ) := by
    have hpowers : (66777/100000 : ℝ)^19 ≤ (734425587367902137/5000000000000000000 : ℝ)^4 := by
      have hnat : (66777 : ℕ)^19*5000000000000000000^4 ≤ 734425587367902137^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66777 100000 734425587367902137 5000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (66777/100000 : ℝ)) (X := (734425587367902137/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (5734425587367902137/5000000000000000000 : ℝ) ≤ (10292728303345153/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (5734425587367902137/5000000000000000000 : ℝ)^4 ≤ (10292728303345153/10000000000000000 : ℝ)^19 := by
      have hnat : (5734425587367902137 : ℕ)^4*10000000000000000^19 ≤ 10292728303345153^19*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5734425587367902137 5000000000000000000 10292728303345153 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10292728303345153/10000000000000000 : ℝ)) (X := (5734425587367902137/5000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (3234425587367902137/2500000000000000000 : ℝ) ≤ (10557203056144057/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3234425587367902137/2500000000000000000 : ℝ)^4 ≤ (10557203056144057/10000000000000000 : ℝ)^19 := by
      have hnat : (3234425587367902137 : ℕ)^4*10000000000000000^19 ≤ 10557203056144057^19*2500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3234425587367902137 2500000000000000000 10557203056144057 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10557203056144057/10000000000000000 : ℝ)) (X := (3234425587367902137/2500000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(97576101115051/2225900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(11019781366621/278237500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (66777/100000 : ℝ)) (alpha := (97576101115051/2225900000000000 : ℝ)) (beta := (11019781366621/278237500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (66777/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(97576101115051/2225900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(11019781366621/278237500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (58877/100000 : ℝ) ^ (19/4 : ℝ) ≤ (8076848684909723459/100000000000000000000 : ℝ) := by
    have hpowers : (58877/100000 : ℝ)^19 ≤ (8076848684909723459/100000000000000000000 : ℝ)^4 := by
      have hnat : (58877 : ℕ)^19*100000000000000000000^4 ≤ 8076848684909723459^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58877 100000 8076848684909723459 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58877/100000 : ℝ)) (X := (8076848684909723459/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (108076848684909723459/100000000000000000000 : ℝ) ≤ (10164865005595183/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (108076848684909723459/100000000000000000000 : ℝ)^4 ≤ (10164865005595183/10000000000000000 : ℝ)^19 := by
      have hnat : (108076848684909723459 : ℕ)^4*10000000000000000^19 ≤ 10164865005595183^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108076848684909723459 100000000000000000000 10164865005595183 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10164865005595183/10000000000000000 : ℝ)) (X := (108076848684909723459/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (58076848684909723459/50000000000000000000 : ℝ) ≤ (5160136265889091/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (58076848684909723459/50000000000000000000 : ℝ)^4 ≤ (5160136265889091/5000000000000000 : ℝ)^19 := by
      have hnat : (58076848684909723459 : ℕ)^4*5000000000000000^19 ≤ 5160136265889091^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58076848684909723459 50000000000000000000 5160136265889091 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5160136265889091/5000000000000000 : ℝ)) (X := (58076848684909723459/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(164865005595183/5887700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(155407526182999/5887700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (58877/100000 : ℝ)) (alpha := (164865005595183/5887700000000000 : ℝ)) (beta := (155407526182999/5887700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (58877/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(164865005595183/5887700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(155407526182999/5887700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (38407/50000 : ℝ) ^ (19/4 : ℝ) ≤ (28565498680764456953/100000000000000000000 : ℝ) := by
    have hpowers : (38407/50000 : ℝ)^19 ≤ (28565498680764456953/100000000000000000000 : ℝ)^4 := by
      have hnat : (38407 : ℕ)^19*100000000000000000000^4 ≤ 28565498680764456953^4*50000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38407 50000 28565498680764456953 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38407/50000 : ℝ)) (X := (28565498680764456953/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (128565498680764456953/100000000000000000000 : ℝ) ≤ (10543227215732973/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (128565498680764456953/100000000000000000000 : ℝ)^4 ≤ (10543227215732973/10000000000000000 : ℝ)^19 := by
      have hnat : (128565498680764456953 : ℕ)^4*10000000000000000^19 ≤ 10543227215732973^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        128565498680764456953 100000000000000000000 10543227215732973 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10543227215732973/10000000000000000 : ℝ)) (X := (128565498680764456953/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (78565498680764456953/50000000000000000000 : ℝ) ≤ (10998115793050793/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (78565498680764456953/50000000000000000000 : ℝ)^4 ≤ (10998115793050793/10000000000000000 : ℝ)^19 := by
      have hnat : (78565498680764456953 : ℕ)^4*10000000000000000^19 ≤ 10998115793050793^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78565498680764456953 50000000000000000000 10998115793050793 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10998115793050793/10000000000000000 : ℝ)) (X := (78565498680764456953/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(543227215732973/7681400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(22744428865891/384070000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (38407/50000 : ℝ)) (alpha := (543227215732973/7681400000000000 : ℝ)) (beta := (22744428865891/384070000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (38407/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(543227215732973/7681400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(22744428865891/384070000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-789049399/5000000000 : ℝ)*X 0 0+(-5374423311/10000000000 : ℝ)*X 0 1+(2622961/5000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2527440971/5000000000 : ℝ)*X 1 0+(791213359/2000000000 : ℝ)*X 1 1+(869178789/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4922715579/10000000000 : ℝ)*X 2 0+(-509073329/1250000000 : ℝ)*X 2 1+(-350084401/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1234180911/2000000000 : ℝ)*X 0 0+(-1489904803/10000000000 : ℝ)*X 0 1+(4478833003/10000000000 : ℝ)*X 0 2+(1234180911/2000000000 : ℝ)*X 1 0+(-1489904803/10000000000 : ℝ)*X 1 1+(4478833003/10000000000 : ℝ)*X 1 2+(1234180911/2000000000 : ℝ)*X 2 0+(-1489904803/10000000000 : ℝ)*X 2 1+(4478833003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316047_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-381771/50000 : ℝ) < ((-177257/100000 : ℝ)*P 0+(-177257/100000 : ℝ)*P 1+(-177257/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-381771/50000 : ℝ) < (-3826178799640300935604669441410370527/503340304932010000000000000000000000 : ℝ) := by norm_num
    linear_combination (1523/50000000000 : ℝ)*(base10) + (7917/1000000000000 : ℝ)*(base17) + (24767/500000000000 : ℝ)*(base21) + (7881/250000000000 : ℝ)*(base39) + (513940245681/1000000000000 : ℝ)*(base40) + (1055799683/25000000000 : ℝ)*(base50) + (156806189471/1000000000000 : ℝ)*(base59) + (463/200000000000 : ℝ)*(base60) + (177257/100000 : ℝ)*(major_s1_0) + (177257/100000 : ℝ)*(major_s1_1) + (177257/100000 : ℝ)*(major_s1_2) + (1266929059111/500000000000 : ℝ)*(sp_s1_0) + (506771628153/200000000000 : ℝ)*(sp_s1_1) + (633464524787/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1266929074341/500000000000 : ℝ)*(f.sum) + (3444662964206585629/5653222347500000000000000000000 : ℝ)*base62 + (93036044762047/192035000000000000000000000 : ℝ)*base65 + (25327110283/147192500000000000000000 : ℝ)*base67 + (24794583765141/38407000000000000000000000 : ℝ)*base68 + (7263632265315149/341960565200000000000000000000 : ℝ)*base71 + (337353726297/11129500000000000000000000 : ℝ)*base73 + (32329609486221/147192500000000000000000000 : ℝ)*base74 + (143381333807/6955937500000000000000000 : ℝ)*base77 + (174738580645770941/327635785750000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p016_b023 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 55)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=47 ∨ c=48 ∨ c=49 ∨ c=50 ∨ c=51 ∨ c=52 ∨ c=53 ∨ c=54 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact collision_c316047 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316048 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316049 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316050 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316051 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316052 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316053 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316054 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 55)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p016_b023 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
