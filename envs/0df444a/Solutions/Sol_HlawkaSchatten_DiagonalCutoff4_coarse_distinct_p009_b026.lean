-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b026
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:01:10.270827+00:00
-- url     : https://prove2.me/submissions/cafc3706-72de-447e-a0ec-6046d56bc407

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308047_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308047_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308047_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308048_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308048_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308048_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308048_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308049_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308049_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308049_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308049_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308050_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308050_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308050_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308050_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308051_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308051_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308051_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308051_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308052_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308052_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308052_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308052_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308052_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309053_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309053_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309053_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309053_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309053_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309053_s5
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c308047 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]]) : False := by
  have h0 := collision_c308047_s0 p hpa hpb X hX
  have h1 := collision_c308047_s1 p hpa hpb X hX h0
  exact collision_c308047_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c308048 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]]) : False := by
  have h0 := collision_c308048_s0 p hpa hpb X hX
  have h1 := collision_c308048_s1 p hpa hpb X hX h0
  have h2 := collision_c308048_s2 p hpa hpb X hX h1
  exact collision_c308048_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c308049 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]]) : False := by
  have h0 := collision_c308049_s0 p hpa hpb X hX
  have h1 := collision_c308049_s1 p hpa hpb X hX h0
  have h2 := collision_c308049_s2 p hpa hpb X hX h1
  exact collision_c308049_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c308050 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]]) : False := by
  have h0 := collision_c308050_s0 p hpa hpb X hX
  have h1 := collision_c308050_s1 p hpa hpb X hX h0
  have h2 := collision_c308050_s2 p hpa hpb X hX h1
  exact collision_c308050_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c308051 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  have h0 := collision_c308051_s0 p hpa hpb X hX
  have h1 := collision_c308051_s1 p hpa hpb X hX h0
  have h2 := collision_c308051_s2 p hpa hpb X hX h1
  exact collision_c308051_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c308052 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by
  have h0 := collision_c308052_s0 p hpa hpb X hX
  have h1 := collision_c308052_s1 p hpa hpb X hX h0
  have h2 := collision_c308052_s2 p hpa hpb X hX h1
  have h3 := collision_c308052_s3 p hpa hpb X hX h2
  exact collision_c308052_s4 p hpa hpb X hX h3

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c309053 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : False := by
  have h0 := collision_c309053_s0 p hpa hpb X hX
  have h1 := collision_c309053_s1 p hpa hpb X hX h0
  have h2 := collision_c309053_s2 p hpa hpb X hX h1
  have h3 := collision_c309053_s3 p hpa hpb X hX h2
  have h4 := collision_c309053_s4 p hpa hpb X hX h3
  exact collision_c309053_s5 p hpa hpb X hX h4

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
theorem collision_support_c309046_s0_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1206688653/10000000000 : ℝ)*x 0 + (-693466671/1250000000 : ℝ)*x 1 + (-5547733367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1206688653/10000000000 : ℝ)^71 ≤ (25479034481/390625000000 : ℝ)^55 := by
    have hnat : (1206688653 : ℕ)^71*390625000000^55 ≤ 25479034481^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206688653 10000000000 25479034481 390625000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693466671/1250000000 : ℝ)^71 ≤ (46738683582417/100000000000000 : ℝ)^55 := by
    have hnat : (693466671 : ℕ)^71*100000000000000^55 ≤ 46738683582417^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693466671 1250000000 46738683582417 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5547733367/10000000000 : ℝ)^71 ≤ (46738683571541/100000000000000 : ℝ)^55 := by
    have hnat : (5547733367 : ℕ)^71*100000000000000^55 ≤ 46738683571541^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5547733367 10000000000 46738683571541 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1206688653/10000000000 : ℝ), (-693466671/1250000000 : ℝ), (-5547733367/10000000000 : ℝ)] ![(25479034481/390625000000 : ℝ), (46738683582417/100000000000000 : ℝ), (46738683571541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1206688653/10000000000 : ℝ)|^71 ≤ (25479034481/390625000000 : ℝ)^55
        have hw : |(-1206688653/10000000000 : ℝ)|=(1206688653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-693466671/1250000000 : ℝ)|^71 ≤ (46738683582417/100000000000000 : ℝ)^55
        have hw : |(-693466671/1250000000 : ℝ)|=(693466671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5547733367/10000000000 : ℝ)|^71 ≤ (46738683571541/100000000000000 : ℝ)^55
        have hw : |(-5547733367/10000000000 : ℝ)|=(5547733367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4748895213/10000000000 : ℝ)*x 0 + (-4024233453/10000000000 : ℝ)*x 1 + (4024233453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4748895213/10000000000 : ℝ)^71 ≤ (597489745673/1562500000000 : ℝ)^55 := by
    have hnat : (4748895213 : ℕ)^71*1562500000000^55 ≤ 597489745673^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4748895213 10000000000 597489745673 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4024233453/10000000000 : ℝ)^71 ≤ (3088032813183/10000000000000 : ℝ)^55 := by
    have hnat : (4024233453 : ℕ)^71*10000000000000^55 ≤ 3088032813183^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024233453 10000000000 3088032813183 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4024233453/10000000000 : ℝ)^71 ≤ (3088032813183/10000000000000 : ℝ)^55 := by
    have hnat : (4024233453 : ℕ)^71*10000000000000^55 ≤ 3088032813183^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024233453 10000000000 3088032813183 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4748895213/10000000000 : ℝ), (-4024233453/10000000000 : ℝ), (4024233453/10000000000 : ℝ)] ![(597489745673/1562500000000 : ℝ), (3088032813183/10000000000000 : ℝ), (3088032813183/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4748895213/10000000000 : ℝ)|^71 ≤ (597489745673/1562500000000 : ℝ)^55
        have hw : |(4748895213/10000000000 : ℝ)|=(4748895213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4024233453/10000000000 : ℝ)|^71 ≤ (3088032813183/10000000000000 : ℝ)^55
        have hw : |(-4024233453/10000000000 : ℝ)|=(4024233453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4024233453/10000000000 : ℝ)|^71 ≤ (3088032813183/10000000000000 : ℝ)^55
        have hw : |(4024233453/10000000000 : ℝ)|=(4024233453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^71 ≤ (1 : ℝ)^55 := by
    have hnat : (1 : ℕ)^71*1^55 ≤ 1^55*1^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^71 ≤ (0 : ℝ)^55 := by
    have hnat : (0 : ℕ)^71*1^55 ≤ 0^55*1^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^71 ≤ (0 : ℝ)^55 := by
    have hnat : (0 : ℕ)^71*1^55 ≤ 0^55*1^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^71 ≤ (1 : ℝ)^55
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^71 ≤ (0 : ℝ)^55
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^71 ≤ (0 : ℝ)^55
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8217469519/10000000000 : ℝ)*x 0 + (-458377191/2500000000 : ℝ)*x 1 + (-1833508763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8217469519/10000000000 : ℝ)^71 ≤ (7761303035619/10000000000000 : ℝ)^55 := by
    have hnat : (8217469519 : ℕ)^71*10000000000000^55 ≤ 7761303035619^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8217469519 10000000000 7761303035619 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458377191/2500000000 : ℝ)^71 ≤ (11193484819341/100000000000000 : ℝ)^55 := by
    have hnat : (458377191 : ℕ)^71*100000000000000^55 ≤ 11193484819341^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458377191 2500000000 11193484819341 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1833508763/10000000000 : ℝ)^71 ≤ (559674240573/5000000000000 : ℝ)^55 := by
    have hnat : (1833508763 : ℕ)^71*5000000000000^55 ≤ 559674240573^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833508763 10000000000 559674240573 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8217469519/10000000000 : ℝ), (-458377191/2500000000 : ℝ), (-1833508763/10000000000 : ℝ)] ![(7761303035619/10000000000000 : ℝ), (11193484819341/100000000000000 : ℝ), (559674240573/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8217469519/10000000000 : ℝ)|^71 ≤ (7761303035619/10000000000000 : ℝ)^55
        have hw : |(8217469519/10000000000 : ℝ)|=(8217469519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-458377191/2500000000 : ℝ)|^71 ≤ (11193484819341/100000000000000 : ℝ)^55
        have hw : |(-458377191/2500000000 : ℝ)|=(458377191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1833508763/10000000000 : ℝ)|^71 ≤ (559674240573/5000000000000 : ℝ)^55
        have hw : |(-1833508763/10000000000 : ℝ)|=(1833508763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-604079743/5000000000 : ℝ)*x 0 + (-147740217/250000000 : ℝ)*x 1 + (-5177887733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (604079743/5000000000 : ℝ)^71 ≤ (6532897939237/100000000000000 : ℝ)^55 := by
    have hnat : (604079743 : ℕ)^71*100000000000000^55 ≤ 6532897939237^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604079743 5000000000 6532897939237 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147740217/250000000 : ℝ)^71 ≤ (633888821223/1250000000000 : ℝ)^55 := by
    have hnat : (147740217 : ℕ)^71*1250000000000^55 ≤ 633888821223^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147740217 250000000 633888821223 1250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177887733/10000000000 : ℝ)^71 ≤ (4275599634061/10000000000000 : ℝ)^55 := by
    have hnat : (5177887733 : ℕ)^71*10000000000000^55 ≤ 4275599634061^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177887733 10000000000 4275599634061 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-604079743/5000000000 : ℝ), (-147740217/250000000 : ℝ), (-5177887733/10000000000 : ℝ)] ![(6532897939237/100000000000000 : ℝ), (633888821223/1250000000000 : ℝ), (4275599634061/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-604079743/5000000000 : ℝ)|^71 ≤ (6532897939237/100000000000000 : ℝ)^55
        have hw : |(-604079743/5000000000 : ℝ)|=(604079743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-147740217/250000000 : ℝ)|^71 ≤ (633888821223/1250000000000 : ℝ)^55
        have hw : |(-147740217/250000000 : ℝ)|=(147740217/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5177887733/10000000000 : ℝ)|^71 ≤ (4275599634061/10000000000000 : ℝ)^55
        have hw : |(-5177887733/10000000000 : ℝ)|=(5177887733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4556352383/10000000000 : ℝ)*x 0 + (1221432241/2500000000 : ℝ)*x 1 + (-3319228757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4556352383/10000000000 : ℝ)^71 ≤ (36249830061469/100000000000000 : ℝ)^55 := by
    have hnat : (4556352383 : ℕ)^71*100000000000000^55 ≤ 36249830061469^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556352383 10000000000 36249830061469 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1221432241/2500000000 : ℝ)^71 ≤ (2479225979647/6250000000000 : ℝ)^55 := by
    have hnat : (1221432241 : ℕ)^71*6250000000000^55 ≤ 2479225979647^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221432241 2500000000 2479225979647 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3319228757/10000000000 : ℝ)^71 ≤ (24082554246211/100000000000000 : ℝ)^55 := by
    have hnat : (3319228757 : ℕ)^71*100000000000000^55 ≤ 24082554246211^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3319228757 10000000000 24082554246211 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4556352383/10000000000 : ℝ), (1221432241/2500000000 : ℝ), (-3319228757/10000000000 : ℝ)] ![(36249830061469/100000000000000 : ℝ), (2479225979647/6250000000000 : ℝ), (24082554246211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4556352383/10000000000 : ℝ)|^71 ≤ (36249830061469/100000000000000 : ℝ)^55
        have hw : |(4556352383/10000000000 : ℝ)|=(4556352383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1221432241/2500000000 : ℝ)|^71 ≤ (2479225979647/6250000000000 : ℝ)^55
        have hw : |(1221432241/2500000000 : ℝ)|=(1221432241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3319228757/10000000000 : ℝ)|^71 ≤ (24082554246211/100000000000000 : ℝ)^55
        have hw : |(-3319228757/10000000000 : ℝ)|=(3319228757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (911270397/2000000000 : ℝ)*x 0 + (-1623228537/5000000000 : ℝ)*x 1 + (4950427747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (911270397/2000000000 : ℝ)^71 ≤ (36249825973879/100000000000000 : ℝ)^55 := by
    have hnat : (911270397 : ℕ)^71*100000000000000^55 ≤ 36249825973879^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911270397 2000000000 36249825973879 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1623228537/5000000000 : ℝ)^71 ≤ (731348401123/3125000000000 : ℝ)^55 := by
    have hnat : (1623228537 : ℕ)^71*3125000000000^55 ≤ 731348401123^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1623228537 5000000000 731348401123 3125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4950427747/10000000000 : ℝ)^71 ≤ (10086756294483/25000000000000 : ℝ)^55 := by
    have hnat : (4950427747 : ℕ)^71*25000000000000^55 ≤ 10086756294483^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4950427747 10000000000 10086756294483 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(911270397/2000000000 : ℝ), (-1623228537/5000000000 : ℝ), (4950427747/10000000000 : ℝ)] ![(36249825973879/100000000000000 : ℝ), (731348401123/3125000000000 : ℝ), (10086756294483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(911270397/2000000000 : ℝ)|^71 ≤ (36249825973879/100000000000000 : ℝ)^55
        have hw : |(911270397/2000000000 : ℝ)|=(911270397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1623228537/5000000000 : ℝ)|^71 ≤ (731348401123/3125000000000 : ℝ)^55
        have hw : |(-1623228537/5000000000 : ℝ)|=(1623228537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4950427747/10000000000 : ℝ)|^71 ≤ (10086756294483/25000000000000 : ℝ)^55
        have hw : |(4950427747/10000000000 : ℝ)|=(4950427747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4096629229/5000000000 : ℝ)*x 0 + (-146115087/1250000000 : ℝ)*x 1 + (-2467323007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4096629229/5000000000 : ℝ)^71 ≤ (19329490993371/25000000000000 : ℝ)^55 := by
    have hnat : (4096629229 : ℕ)^71*25000000000000^55 ≤ 19329490993371^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4096629229 5000000000 19329490993371 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146115087/1250000000 : ℝ)^71 ≤ (1565075353927/25000000000000 : ℝ)^55 := by
    have hnat : (146115087 : ℕ)^71*25000000000000^55 ≤ 1565075353927^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146115087 1250000000 1565075353927 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2467323007/10000000000 : ℝ)^71 ≤ (16421734601949/100000000000000 : ℝ)^55 := by
    have hnat : (2467323007 : ℕ)^71*100000000000000^55 ≤ 16421734601949^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2467323007 10000000000 16421734601949 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4096629229/5000000000 : ℝ), (-146115087/1250000000 : ℝ), (-2467323007/10000000000 : ℝ)] ![(19329490993371/25000000000000 : ℝ), (1565075353927/25000000000000 : ℝ), (16421734601949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4096629229/5000000000 : ℝ)|^71 ≤ (19329490993371/25000000000000 : ℝ)^55
        have hw : |(4096629229/5000000000 : ℝ)|=(4096629229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-146115087/1250000000 : ℝ)|^71 ≤ (1565075353927/25000000000000 : ℝ)^55
        have hw : |(-146115087/1250000000 : ℝ)|=(146115087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2467323007/10000000000 : ℝ)|^71 ≤ (16421734601949/100000000000000 : ℝ)^55
        have hw : |(-2467323007/10000000000 : ℝ)|=(2467323007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-28420483/1000000000 : ℝ)*x 0 + (-5467902519/10000000000 : ℝ)*x 1 + (-6125833833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28420483/1000000000 : ℝ)^71 ≤ (100873894119/10000000000000 : ℝ)^55 := by
    have hnat : (28420483 : ℕ)^71*10000000000000^55 ≤ 100873894119^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28420483 1000000000 100873894119 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467902519/10000000000 : ℝ)^71 ≤ (22936145997039/50000000000000 : ℝ)^55 := by
    have hnat : (5467902519 : ℕ)^71*50000000000000^55 ≤ 22936145997039^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467902519 10000000000 22936145997039 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6125833833/10000000000 : ℝ)^71 ≤ (53118969044723/100000000000000 : ℝ)^55 := by
    have hnat : (6125833833 : ℕ)^71*100000000000000^55 ≤ 53118969044723^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6125833833 10000000000 53118969044723 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-28420483/1000000000 : ℝ), (-5467902519/10000000000 : ℝ), (-6125833833/10000000000 : ℝ)] ![(100873894119/10000000000000 : ℝ), (22936145997039/50000000000000 : ℝ), (53118969044723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-28420483/1000000000 : ℝ)|^71 ≤ (100873894119/10000000000000 : ℝ)^55
        have hw : |(-28420483/1000000000 : ℝ)|=(28420483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5467902519/10000000000 : ℝ)|^71 ≤ (22936145997039/50000000000000 : ℝ)^55
        have hw : |(-5467902519/10000000000 : ℝ)|=(5467902519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6125833833/10000000000 : ℝ)|^71 ≤ (53118969044723/100000000000000 : ℝ)^55
        have hw : |(-6125833833/10000000000 : ℝ)|=(6125833833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (167836779/400000000 : ℝ)*x 0 + (2056937467/5000000000 : ℝ)*x 1 + (-224830087/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167836779/400000000 : ℝ)^71 ≤ (16295741878247/50000000000000 : ℝ)^55 := by
    have hnat : (167836779 : ℕ)^71*50000000000000^55 ≤ 16295741878247^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167836779 400000000 16295741878247 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2056937467/5000000000 : ℝ)^71 ≤ (6354234144473/20000000000000 : ℝ)^55 := by
    have hnat : (2056937467 : ℕ)^71*20000000000000^55 ≤ 6354234144473^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056937467 5000000000 6354234144473 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224830087/500000000 : ℝ)^71 ≤ (890933637689/2500000000000 : ℝ)^55 := by
    have hnat : (224830087 : ℕ)^71*2500000000000^55 ≤ 890933637689^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224830087 500000000 890933637689 2500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167836779/400000000 : ℝ), (2056937467/5000000000 : ℝ), (-224830087/500000000 : ℝ)] ![(16295741878247/50000000000000 : ℝ), (6354234144473/20000000000000 : ℝ), (890933637689/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167836779/400000000 : ℝ)|^71 ≤ (16295741878247/50000000000000 : ℝ)^55
        have hw : |(167836779/400000000 : ℝ)|=(167836779/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2056937467/5000000000 : ℝ)|^71 ≤ (6354234144473/20000000000000 : ℝ)^55
        have hw : |(2056937467/5000000000 : ℝ)|=(2056937467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224830087/500000000 : ℝ)|^71 ≤ (890933637689/2500000000000 : ℝ)^55
        have hw : |(-224830087/500000000 : ℝ)|=(224830087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1146665563/2000000000 : ℝ)*x 0 + (-415767831/1250000000 : ℝ)*x 1 + (1817792113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1146665563/2000000000 : ℝ)^71 ≤ (24383447704863/50000000000000 : ℝ)^55 := by
    have hnat : (1146665563 : ℕ)^71*50000000000000^55 ≤ 24383447704863^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146665563 2000000000 24383447704863 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415767831/1250000000 : ℝ)^71 ≤ (75460407449/312500000000 : ℝ)^55 := by
    have hnat : (415767831 : ℕ)^71*312500000000^55 ≤ 75460407449^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415767831 1250000000 75460407449 312500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1817792113/5000000000 : ℝ)^71 ≤ (1692860886833/6250000000000 : ℝ)^55 := by
    have hnat : (1817792113 : ℕ)^71*6250000000000^55 ≤ 1692860886833^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817792113 5000000000 1692860886833 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1146665563/2000000000 : ℝ), (-415767831/1250000000 : ℝ), (1817792113/5000000000 : ℝ)] ![(24383447704863/50000000000000 : ℝ), (75460407449/312500000000 : ℝ), (1692860886833/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1146665563/2000000000 : ℝ)|^71 ≤ (24383447704863/50000000000000 : ℝ)^55
        have hw : |(1146665563/2000000000 : ℝ)|=(1146665563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415767831/1250000000 : ℝ)|^71 ≤ (75460407449/312500000000 : ℝ)^55
        have hw : |(-415767831/1250000000 : ℝ)|=(415767831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1817792113/5000000000 : ℝ)|^71 ≤ (1692860886833/6250000000000 : ℝ)^55
        have hw : |(1817792113/5000000000 : ℝ)|=(1817792113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_19 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2383404843/2500000000 : ℝ)*x 0 + (-155418799/2500000000 : ℝ)*x 1 + (-34823947/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2383404843/2500000000 : ℝ)^71 ≤ (18804150242919/20000000000000 : ℝ)^55 := by
    have hnat : (2383404843 : ℕ)^71*20000000000000^55 ≤ 18804150242919^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383404843 2500000000 18804150242919 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155418799/2500000000 : ℝ)^71 ≤ (277076827341/10000000000000 : ℝ)^55 := by
    have hnat : (155418799 : ℕ)^71*10000000000000^55 ≤ 277076827341^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155418799 2500000000 277076827341 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34823947/500000000 : ℝ)^71 ≤ (128339219891/4000000000000 : ℝ)^55 := by
    have hnat : (34823947 : ℕ)^71*4000000000000^55 ≤ 128339219891^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34823947 500000000 128339219891 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2383404843/2500000000 : ℝ), (-155418799/2500000000 : ℝ), (-34823947/500000000 : ℝ)] ![(18804150242919/20000000000000 : ℝ), (277076827341/10000000000000 : ℝ), (128339219891/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2383404843/2500000000 : ℝ)|^71 ≤ (18804150242919/20000000000000 : ℝ)^55
        have hw : |(2383404843/2500000000 : ℝ)|=(2383404843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-155418799/2500000000 : ℝ)|^71 ≤ (277076827341/10000000000000 : ℝ)^55
        have hw : |(-155418799/2500000000 : ℝ)|=(155418799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34823947/500000000 : ℝ)|^71 ≤ (128339219891/4000000000000 : ℝ)^55
        have hw : |(-34823947/500000000 : ℝ)|=(34823947/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-142102331/5000000000 : ℝ)*x 0 + (-765729233/1250000000 : ℝ)*x 1 + (-2733951279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (142102331/5000000000 : ℝ)^71 ≤ (201747634287/20000000000000 : ℝ)^55 := by
    have hnat : (142102331 : ℕ)^71*20000000000000^55 ≤ 201747634287^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142102331 5000000000 201747634287 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (765729233/1250000000 : ℝ)^71 ≤ (53118969391733/100000000000000 : ℝ)^55 := by
    have hnat : (765729233 : ℕ)^71*100000000000000^55 ≤ 53118969391733^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765729233 1250000000 53118969391733 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733951279/5000000000 : ℝ)^71 ≤ (9174458483289/20000000000000 : ℝ)^55 := by
    have hnat : (2733951279 : ℕ)^71*20000000000000^55 ≤ 9174458483289^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733951279 5000000000 9174458483289 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-142102331/5000000000 : ℝ), (-765729233/1250000000 : ℝ), (-2733951279/5000000000 : ℝ)] ![(201747634287/20000000000000 : ℝ), (53118969391733/100000000000000 : ℝ), (9174458483289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-142102331/5000000000 : ℝ)|^71 ≤ (201747634287/20000000000000 : ℝ)^55
        have hw : |(-142102331/5000000000 : ℝ)|=(142102331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-765729233/1250000000 : ℝ)|^71 ≤ (53118969391733/100000000000000 : ℝ)^55
        have hw : |(-765729233/1250000000 : ℝ)|=(765729233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2733951279/5000000000 : ℝ)|^71 ≤ (9174458483289/20000000000000 : ℝ)^55
        have hw : |(-2733951279/5000000000 : ℝ)|=(2733951279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (716665957/1250000000 : ℝ)*x 0 + (727117183/2000000000 : ℝ)*x 1 + (-1663070551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (716665957/1250000000 : ℝ)^71 ≤ (48766893663859/100000000000000 : ℝ)^55 := by
    have hnat : (716665957 : ℕ)^71*100000000000000^55 ≤ 48766893663859^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716665957 1250000000 48766893663859 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (727117183/2000000000 : ℝ)^71 ≤ (5417158086661/20000000000000 : ℝ)^55 := by
    have hnat : (727117183 : ℕ)^71*20000000000000^55 ≤ 5417158086661^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727117183 2000000000 5417158086661 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1663070551/5000000000 : ℝ)^71 ≤ (377301810857/1562500000000 : ℝ)^55 := by
    have hnat : (1663070551 : ℕ)^71*1562500000000^55 ≤ 377301810857^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663070551 5000000000 377301810857 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(716665957/1250000000 : ℝ), (727117183/2000000000 : ℝ), (-1663070551/5000000000 : ℝ)] ![(48766893663859/100000000000000 : ℝ), (5417158086661/20000000000000 : ℝ), (377301810857/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(716665957/1250000000 : ℝ)|^71 ≤ (48766893663859/100000000000000 : ℝ)^55
        have hw : |(716665957/1250000000 : ℝ)|=(716665957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(727117183/2000000000 : ℝ)|^71 ≤ (5417158086661/20000000000000 : ℝ)^55
        have hw : |(727117183/2000000000 : ℝ)|=(727117183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1663070551/5000000000 : ℝ)|^71 ≤ (377301810857/1562500000000 : ℝ)^55
        have hw : |(-1663070551/5000000000 : ℝ)|=(1663070551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2097960197/5000000000 : ℝ)*x 0 + (-4496603233/10000000000 : ℝ)*x 1 + (4113872477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097960197/5000000000 : ℝ)^71 ≤ (16295746485671/50000000000000 : ℝ)^55 := by
    have hnat : (2097960197 : ℕ)^71*50000000000000^55 ≤ 16295746485671^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097960197 5000000000 16295746485671 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496603233/10000000000 : ℝ)^71 ≤ (35637360782391/100000000000000 : ℝ)^55 := by
    have hnat : (4496603233 : ℕ)^71*100000000000000^55 ≤ 35637360782391^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496603233 10000000000 35637360782391 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4113872477/10000000000 : ℝ)^71 ≤ (31771146227057/100000000000000 : ℝ)^55 := by
    have hnat : (4113872477 : ℕ)^71*100000000000000^55 ≤ 31771146227057^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4113872477 10000000000 31771146227057 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097960197/5000000000 : ℝ), (-4496603233/10000000000 : ℝ), (4113872477/10000000000 : ℝ)] ![(16295746485671/50000000000000 : ℝ), (35637360782391/100000000000000 : ℝ), (31771146227057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097960197/5000000000 : ℝ)|^71 ≤ (16295746485671/50000000000000 : ℝ)^55
        have hw : |(2097960197/5000000000 : ℝ)|=(2097960197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4496603233/10000000000 : ℝ)|^71 ≤ (35637360782391/100000000000000 : ℝ)^55
        have hw : |(-4496603233/10000000000 : ℝ)|=(4496603233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4113872477/10000000000 : ℝ)|^71 ≤ (31771146227057/100000000000000 : ℝ)^55
        have hw : |(4113872477/10000000000 : ℝ)|=(4113872477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s0_25 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1191702397/1250000000 : ℝ)*x 0 + (-139295833/2000000000 : ℝ)*x 1 + (-310837699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1191702397/1250000000 : ℝ)^71 ≤ (23505187179831/25000000000000 : ℝ)^55 := by
    have hnat : (1191702397 : ℕ)^71*25000000000000^55 ≤ 23505187179831^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191702397 1250000000 23505187179831 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139295833/2000000000 : ℝ)^71 ≤ (802120458829/25000000000000 : ℝ)^55 := by
    have hnat : (139295833 : ℕ)^71*25000000000000^55 ≤ 802120458829^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139295833 2000000000 802120458829 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310837699/5000000000 : ℝ)^71 ≤ (2770769435617/100000000000000 : ℝ)^55 := by
    have hnat : (310837699 : ℕ)^71*100000000000000^55 ≤ 2770769435617^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310837699 5000000000 2770769435617 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1191702397/1250000000 : ℝ), (-139295833/2000000000 : ℝ), (-310837699/5000000000 : ℝ)] ![(23505187179831/25000000000000 : ℝ), (802120458829/25000000000000 : ℝ), (2770769435617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1191702397/1250000000 : ℝ)|^71 ≤ (23505187179831/25000000000000 : ℝ)^55
        have hw : |(1191702397/1250000000 : ℝ)|=(1191702397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-139295833/2000000000 : ℝ)|^71 ≤ (802120458829/25000000000000 : ℝ)^55
        have hw : |(-139295833/2000000000 : ℝ)|=(139295833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-310837699/5000000000 : ℝ)|^71 ≤ (2770769435617/100000000000000 : ℝ)^55
        have hw : |(-310837699/5000000000 : ℝ)|=(310837699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s1_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2673362099/10000000000 : ℝ)*x 0 + (-5002284991/10000000000 : ℝ)*x 1 + (-5002284991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673362099/10000000000 : ℝ)^71 ≤ (9106546143849/50000000000000 : ℝ)^55 := by
    have hnat : (2673362099 : ℕ)^71*50000000000000^55 ≤ 9106546143849^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673362099 10000000000 9106546143849 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5002284991/10000000000 : ℝ)^71 ≤ (2555840865533/6250000000000 : ℝ)^55 := by
    have hnat : (5002284991 : ℕ)^71*6250000000000^55 ≤ 2555840865533^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002284991 10000000000 2555840865533 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5002284991/10000000000 : ℝ)^71 ≤ (2555840865533/6250000000000 : ℝ)^55 := by
    have hnat : (5002284991 : ℕ)^71*6250000000000^55 ≤ 2555840865533^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002284991 10000000000 2555840865533 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2673362099/10000000000 : ℝ), (-5002284991/10000000000 : ℝ), (-5002284991/10000000000 : ℝ)] ![(9106546143849/50000000000000 : ℝ), (2555840865533/6250000000000 : ℝ), (2555840865533/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2673362099/10000000000 : ℝ)|^71 ≤ (9106546143849/50000000000000 : ℝ)^55
        have hw : |(-2673362099/10000000000 : ℝ)|=(2673362099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5002284991/10000000000 : ℝ)|^71 ≤ (2555840865533/6250000000000 : ℝ)^55
        have hw : |(-5002284991/10000000000 : ℝ)|=(5002284991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5002284991/10000000000 : ℝ)|^71 ≤ (2555840865533/6250000000000 : ℝ)^55
        have hw : |(-5002284991/10000000000 : ℝ)|=(5002284991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s1_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2278191161/5000000000 : ℝ)*x 0 + (4124278797/10000000000 : ℝ)*x 1 + (-4124278797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2278191161/5000000000 : ℝ)^71 ≤ (9062534386281/25000000000000 : ℝ)^55 := by
    have hnat : (2278191161 : ℕ)^71*25000000000000^55 ≤ 9062534386281^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278191161 5000000000 9062534386281 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4124278797/10000000000 : ℝ)^71 ≤ (31874931220519/100000000000000 : ℝ)^55 := by
    have hnat : (4124278797 : ℕ)^71*100000000000000^55 ≤ 31874931220519^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124278797 10000000000 31874931220519 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4124278797/10000000000 : ℝ)^71 ≤ (31874931220519/100000000000000 : ℝ)^55 := by
    have hnat : (4124278797 : ℕ)^71*100000000000000^55 ≤ 31874931220519^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124278797 10000000000 31874931220519 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2278191161/5000000000 : ℝ), (4124278797/10000000000 : ℝ), (-4124278797/10000000000 : ℝ)] ![(9062534386281/25000000000000 : ℝ), (31874931220519/100000000000000 : ℝ), (31874931220519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2278191161/5000000000 : ℝ)|^71 ≤ (9062534386281/25000000000000 : ℝ)^55
        have hw : |(2278191161/5000000000 : ℝ)|=(2278191161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4124278797/10000000000 : ℝ)|^71 ≤ (31874931220519/100000000000000 : ℝ)^55
        have hw : |(4124278797/10000000000 : ℝ)|=(4124278797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4124278797/10000000000 : ℝ)|^71 ≤ (31874931220519/100000000000000 : ℝ)^55
        have hw : |(-4124278797/10000000000 : ℝ)|=(4124278797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s1_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2278191161/5000000000 : ℝ)*x 0 + (-4124278797/10000000000 : ℝ)*x 1 + (4124278797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2278191161/5000000000 : ℝ)^71 ≤ (9062534386281/25000000000000 : ℝ)^55 := by
    have hnat : (2278191161 : ℕ)^71*25000000000000^55 ≤ 9062534386281^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278191161 5000000000 9062534386281 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4124278797/10000000000 : ℝ)^71 ≤ (31874931220519/100000000000000 : ℝ)^55 := by
    have hnat : (4124278797 : ℕ)^71*100000000000000^55 ≤ 31874931220519^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124278797 10000000000 31874931220519 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4124278797/10000000000 : ℝ)^71 ≤ (31874931220519/100000000000000 : ℝ)^55 := by
    have hnat : (4124278797 : ℕ)^71*100000000000000^55 ≤ 31874931220519^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124278797 10000000000 31874931220519 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2278191161/5000000000 : ℝ), (-4124278797/10000000000 : ℝ), (4124278797/10000000000 : ℝ)] ![(9062534386281/25000000000000 : ℝ), (31874931220519/100000000000000 : ℝ), (31874931220519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2278191161/5000000000 : ℝ)|^71 ≤ (9062534386281/25000000000000 : ℝ)^55
        have hw : |(2278191161/5000000000 : ℝ)|=(2278191161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4124278797/10000000000 : ℝ)|^71 ≤ (31874931220519/100000000000000 : ℝ)^55
        have hw : |(-4124278797/10000000000 : ℝ)|=(4124278797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4124278797/10000000000 : ℝ)|^71 ≤ (31874931220519/100000000000000 : ℝ)^55
        have hw : |(4124278797/10000000000 : ℝ)|=(4124278797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309046_s1_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (157787431/250000000 : ℝ)*x 0 + (-3137785521/10000000000 : ℝ)*x 1 + (-3137785521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (157787431/250000000 : ℝ)^71 ≤ (27603178774211/50000000000000 : ℝ)^55 := by
    have hnat : (157787431 : ℕ)^71*50000000000000^55 ≤ 27603178774211^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157787431 250000000 27603178774211 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3137785521/10000000000 : ℝ)^71 ≤ (22396821219323/100000000000000 : ℝ)^55 := by
    have hnat : (3137785521 : ℕ)^71*100000000000000^55 ≤ 22396821219323^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3137785521 10000000000 22396821219323 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3137785521/10000000000 : ℝ)^71 ≤ (22396821219323/100000000000000 : ℝ)^55 := by
    have hnat : (3137785521 : ℕ)^71*100000000000000^55 ≤ 22396821219323^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3137785521 10000000000 22396821219323 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(157787431/250000000 : ℝ), (-3137785521/10000000000 : ℝ), (-3137785521/10000000000 : ℝ)] ![(27603178774211/50000000000000 : ℝ), (22396821219323/100000000000000 : ℝ), (22396821219323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(157787431/250000000 : ℝ)|^71 ≤ (27603178774211/50000000000000 : ℝ)^55
        have hw : |(157787431/250000000 : ℝ)|=(157787431/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3137785521/10000000000 : ℝ)|^71 ≤ (22396821219323/100000000000000 : ℝ)^55
        have hw : |(-3137785521/10000000000 : ℝ)|=(3137785521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3137785521/10000000000 : ℝ)|^71 ≤ (22396821219323/100000000000000 : ℝ)^55
        have hw : |(-3137785521/10000000000 : ℝ)|=(3137785521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309046 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
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
  have s0_pow0 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1206688653/10000000000 : ℝ)*X 0 0+(-693466671/1250000000 : ℝ)*X 0 1+(-5547733367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4748895213/10000000000 : ℝ)*X 2 0+(-4024233453/10000000000 : ℝ)*X 2 1+(4024233453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((8217469519/10000000000 : ℝ)*X 0 0+(-458377191/2500000000 : ℝ)*X 0 1+(-1833508763/10000000000 : ℝ)*X 0 2+(8217469519/10000000000 : ℝ)*X 1 0+(-458377191/2500000000 : ℝ)*X 1 1+(-1833508763/10000000000 : ℝ)*X 1 2+(8217469519/10000000000 : ℝ)*X 2 0+(-458377191/2500000000 : ℝ)*X 2 1+(-1833508763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-604079743/5000000000 : ℝ)*X 0 0+(-147740217/250000000 : ℝ)*X 0 1+(-5177887733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4556352383/10000000000 : ℝ)*X 1 0+(1221432241/2500000000 : ℝ)*X 1 1+(-3319228757/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((911270397/2000000000 : ℝ)*X 2 0+(-1623228537/5000000000 : ℝ)*X 2 1+(4950427747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((4096629229/5000000000 : ℝ)*X 0 0+(-146115087/1250000000 : ℝ)*X 0 1+(-2467323007/10000000000 : ℝ)*X 0 2+(4096629229/5000000000 : ℝ)*X 1 0+(-146115087/1250000000 : ℝ)*X 1 1+(-2467323007/10000000000 : ℝ)*X 1 2+(4096629229/5000000000 : ℝ)*X 2 0+(-146115087/1250000000 : ℝ)*X 2 1+(-2467323007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-28420483/1000000000 : ℝ)*X 0 0+(-5467902519/10000000000 : ℝ)*X 0 1+(-6125833833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((167836779/400000000 : ℝ)*X 1 0+(2056937467/5000000000 : ℝ)*X 1 1+(-224830087/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1146665563/2000000000 : ℝ)*X 2 0+(-415767831/1250000000 : ℝ)*X 2 1+(1817792113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((2383404843/2500000000 : ℝ)*X 0 0+(-155418799/2500000000 : ℝ)*X 0 1+(-34823947/500000000 : ℝ)*X 0 2+(2383404843/2500000000 : ℝ)*X 1 0+(-155418799/2500000000 : ℝ)*X 1 1+(-34823947/500000000 : ℝ)*X 1 2+(2383404843/2500000000 : ℝ)*X 2 0+(-155418799/2500000000 : ℝ)*X 2 1+(-34823947/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-142102331/5000000000 : ℝ)*X 0 0+(-765729233/1250000000 : ℝ)*X 0 1+(-2733951279/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((716665957/1250000000 : ℝ)*X 1 0+(727117183/2000000000 : ℝ)*X 1 1+(-1663070551/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2097960197/5000000000 : ℝ)*X 2 0+(-4496603233/10000000000 : ℝ)*X 2 1+(4113872477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((1191702397/1250000000 : ℝ)*X 0 0+(-139295833/2000000000 : ℝ)*X 0 1+(-310837699/5000000000 : ℝ)*X 0 2+(1191702397/1250000000 : ℝ)*X 1 0+(-139295833/2000000000 : ℝ)*X 1 1+(-310837699/5000000000 : ℝ)*X 1 2+(1191702397/1250000000 : ℝ)*X 2 0+(-139295833/2000000000 : ℝ)*X 2 1+(-310837699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2829/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2829/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2754134764255701118953/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (36131/125000000000 : ℝ)*(base3) + (178537564499/200000000000 : ℝ)*(base39) + (61480460853/1000000000000 : ℝ)*(base49) + (1309507/1000000000000 : ℝ)*(base59) + (407434675539/125000000000 : ℝ)*(major_s0_0) + (407434675539/125000000000 : ℝ)*(major_s0_1) + (407434675539/125000000000 : ℝ)*(major_s0_2) + (4844513/1000000000000 : ℝ)*(sp_s0_6) + (2236072855847/500000000000 : ℝ)*(sp_s0_7) + (4472044764187/1000000000000 : ℝ)*(sp_s0_8) + (559006633377/125000000000 : ℝ)*(sp_s0_9) + (2046801025621/1000000000000 : ℝ)*(sp_s0_13) + (50618277/500000000000 : ℝ)*(sp_s0_15) + (92644677/1000000000000 : ℝ)*(sp_s0_22) + (1023403079591/500000000000 : ℝ)*(f.failure) + (2236072855847/500000000000 : ℝ)*(f.sum) + (370465678189/312500000000000000000000000 : ℝ)*base62 + (165716151179099/1250000000000000000000000000 : ℝ)*base65 + (259355076179099/1250000000000000000000000000 : ℝ)*base67 + (99189706478061/625000000000000000000000000 : ℝ)*base69 + (157219915635221/1250000000000000000000000000 : ℝ)*base71 + (150034946695901/1250000000000000000000000000 : ℝ)*base72 + (181160161040561/625000000000000000000000000 : ℝ)*base75 + (155215011709439/625000000000000000000000000 : ℝ)*base76 + (254981510491599/625000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (27977/50000000000000000 : ℝ)*base87 + (27977/50000000000000000 : ℝ)*base89 + (27977/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-45023/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-45023/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16521778761554197251303/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21891943/1000000000000 : ℝ)*(base12) + (31921789433/100000000000 : ℝ)*(base39) + (4558921/1000000000000 : ℝ)*(base59) + (2784270703959/250000000000 : ℝ)*(major_s0_0) + (2370367394791/500000000000 : ℝ)*(major_s0_1) + (2370367394791/500000000000 : ℝ)*(major_s0_2) + (11155089/125000000000 : ℝ)*(sp_s0_0) + (3198174013127/500000000000 : ℝ)*(sp_s0_3) + (20218847/500000000000 : ℝ)*(sp_s0_9) + (1626096108499/250000000000 : ℝ)*(sp_s0_14) + (1300896753843/200000000000 : ℝ)*(sp_s0_15) + (6504455128957/1000000000000 : ℝ)*(sp_s0_16) + (29769696067/10000000000 : ℝ)*(sp_s0_19) + (2949359/250000000000 : ℝ)*(sp_s0_21) + (29769696067/10000000000 : ℝ)*(f.failure) + (6504495566651/1000000000000 : ℝ)*(f.sum) + (327275056693609/1250000000000000000000000000 : ℝ)*base63 + (1543646719744431/5000000000000000000000000000 : ℝ)*base65 + (749955864255569/5000000000000000000000000000 : ℝ)*base66 + (727057769443609/2500000000000000000000000000 : ℝ)*base69 + (329064900314999/1000000000000000000000000000 : ℝ)*base71 + (1561907967195681/2500000000000000000000000000 : ℝ)*base72 + (928780418443609/2500000000000000000000000000 : ℝ)*base75 + (265380131792359/1250000000000000000000000000 : ℝ)*base76 + (2631220920646931/5000000000000000000000000000 : ℝ)*base78 + (451/1000000000000000 : ℝ)*base86 + (451/1000000000000000 : ℝ)*base88 + (451/1000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-45023/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-45023/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (73716662854352098491861/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (840019/62500000000 : ℝ)*(base10) + (218479558147/250000000000 : ℝ)*(base39) + (2635983/1000000000000 : ℝ)*(base49) + (1845046358441/200000000000 : ℝ)*(major_s0_0) + (4740730224381/1000000000000 : ℝ)*(major_s0_1) + (4740730224381/1000000000000 : ℝ)*(major_s0_2) + (13452271/500000000000 : ℝ)*(sp_s0_2) + (179380062713/40000000000 : ℝ)*(sp_s0_3) + (38392101/500000000000 : ℝ)*(sp_s0_7) + (28403743/1000000000000 : ℝ)*(sp_s0_8) + (813049821231/125000000000 : ℝ)*(sp_s0_20) + (6504460390611/1000000000000 : ℝ)*(sp_s0_21) + (6504461889811/1000000000000 : ℝ)*(sp_s0_22) + (1488483369979/500000000000 : ℝ)*(sp_s0_25) + (1488483369979/500000000000 : ℝ)*(f.failure) + (3252244397177/500000000000 : ℝ)*(f.sum) + (198483203019981/2500000000000000000000000000 : ℝ)*base62 + (1121922942822379/10000000000000000000000000000 : ℝ)*base64 + (7318685510822379/10000000000000000000000000000 : ℝ)*base66 + (3742513434519981/5000000000000000000000000000 : ℝ)*base68 + (1141260521922789/10000000000000000000000000000 : ℝ)*base70 + (176327407645919/2000000000000000000000000000 : ℝ)*base72 + (1619641232019981/5000000000000000000000000000 : ℝ)*base74 + (862819767110041/1000000000000000000000000000 : ℝ)*base76 + (2487476385474013/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (45813/50000000000000000 : ℝ)*base87 + (4187/50000000000000000 : ℝ)*base88 + (4187/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (2829/25000 : ℝ) ^ (69/16 : ℝ) ≤ (8299478390864967/100000000000000000000 : ℝ) := by
    have hpowers : (2829/25000 : ℝ)^69 ≤ (8299478390864967/100000000000000000000 : ℝ)^16 := by
      have hnat : (2829 : ℕ)^69*100000000000000000000^16 ≤ 8299478390864967^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2829 25000 8299478390864967 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2829/25000 : ℝ)) (X := (8299478390864967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100008299478390864967/100000000000000000000 : ℝ) ≤ (2500048111384693/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (100008299478390864967/100000000000000000000 : ℝ)^16 ≤ (2500048111384693/2500000000000000 : ℝ)^69 := by
      have hnat : (100008299478390864967 : ℕ)^16*2500000000000000^69 ≤ 2500048111384693^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100008299478390864967 100000000000000000000 2500048111384693 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500048111384693/2500000000000000 : ℝ)) (X := (100008299478390864967/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50008299478390864967/50000000000000000000 : ℝ) ≤ (10000384878810623/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50008299478390864967/50000000000000000000 : ℝ)^16 ≤ (10000384878810623/10000000000000000 : ℝ)^69 := by
      have hnat : (50008299478390864967 : ℕ)^16*10000000000000000^69 ≤ 10000384878810623^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008299478390864967 50000000000000000000 10000384878810623 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000384878810623/10000000000000000 : ℝ)) (X := (50008299478390864967/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(16037128231/94300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(192433271851/1131600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (2829/25000 : ℝ)) (alpha := (16037128231/94300000000000 : ℝ)) (beta := (192433271851/1131600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2829/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(16037128231/94300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(192433271851/1131600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (45023/100000 : ℝ) ^ (69/16 : ℝ) ≤ (800527005359769349/25000000000000000000 : ℝ) := by
    have hpowers : (45023/100000 : ℝ)^69 ≤ (800527005359769349/25000000000000000000 : ℝ)^16 := by
      have hnat : (45023 : ℕ)^69*25000000000000000000^16 ≤ 800527005359769349^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45023 100000 800527005359769349 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45023/100000 : ℝ)) (X := (800527005359769349/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25800527005359769349/25000000000000000000 : ℝ) ≤ (10073355495720733/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25800527005359769349/25000000000000000000 : ℝ)^16 ≤ (10073355495720733/10000000000000000 : ℝ)^69 := by
      have hnat : (25800527005359769349 : ℕ)^16*10000000000000000^69 ≤ 10073355495720733^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25800527005359769349 25000000000000000000 10073355495720733 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10073355495720733/10000000000000000 : ℝ)) (X := (25800527005359769349/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (13300527005359769349/12500000000000000000 : ℝ) ≤ (1014498301728179/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (13300527005359769349/12500000000000000000 : ℝ)^16 ≤ (1014498301728179/1000000000000000 : ℝ)^69 := by
      have hnat : (13300527005359769349 : ℕ)^16*1000000000000000^69 ≤ 1014498301728179^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13300527005359769349 12500000000000000000 1014498301728179 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1014498301728179/1000000000000000 : ℝ)) (X := (13300527005359769349/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(73355495720733/4502300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(6511592869187/409300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (45023/100000 : ℝ)) (alpha := (73355495720733/4502300000000000 : ℝ)) (beta := (6511592869187/409300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (45023/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(73355495720733/4502300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(6511592869187/409300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (45023/100000 : ℝ) ^ (69/16 : ℝ) ≤ (800527005359769349/25000000000000000000 : ℝ) := by
    have hpowers : (45023/100000 : ℝ)^69 ≤ (800527005359769349/25000000000000000000 : ℝ)^16 := by
      have hnat : (45023 : ℕ)^69*25000000000000000000^16 ≤ 800527005359769349^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45023 100000 800527005359769349 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45023/100000 : ℝ)) (X := (800527005359769349/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25800527005359769349/25000000000000000000 : ℝ) ≤ (10073355495720733/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25800527005359769349/25000000000000000000 : ℝ)^16 ≤ (10073355495720733/10000000000000000 : ℝ)^69 := by
      have hnat : (25800527005359769349 : ℕ)^16*10000000000000000^69 ≤ 10073355495720733^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25800527005359769349 25000000000000000000 10073355495720733 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10073355495720733/10000000000000000 : ℝ)) (X := (25800527005359769349/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (13300527005359769349/12500000000000000000 : ℝ) ≤ (1014498301728179/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (13300527005359769349/12500000000000000000 : ℝ)^16 ≤ (1014498301728179/1000000000000000 : ℝ)^69 := by
      have hnat : (13300527005359769349 : ℕ)^16*1000000000000000^69 ≤ 1014498301728179^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13300527005359769349 12500000000000000000 1014498301728179 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1014498301728179/1000000000000000 : ℝ)) (X := (13300527005359769349/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(73355495720733/4502300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(6511592869187/409300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (45023/100000 : ℝ)) (alpha := (73355495720733/4502300000000000 : ℝ)) (beta := (6511592869187/409300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (45023/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(73355495720733/4502300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(6511592869187/409300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2673362099/10000000000 : ℝ)*X 0 0+(-5002284991/10000000000 : ℝ)*X 0 1+(-5002284991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2278191161/5000000000 : ℝ)*X 1 0+(4124278797/10000000000 : ℝ)*X 1 1+(-4124278797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2278191161/5000000000 : ℝ)*X 2 0+(-4124278797/10000000000 : ℝ)*X 2 1+(4124278797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((157787431/250000000 : ℝ)*X 0 0+(-3137785521/10000000000 : ℝ)*X 0 1+(-3137785521/10000000000 : ℝ)*X 0 2+(157787431/250000000 : ℝ)*X 1 0+(-3137785521/10000000000 : ℝ)*X 1 1+(-3137785521/10000000000 : ℝ)*X 1 2+(157787431/250000000 : ℝ)*X 2 0+(-3137785521/10000000000 : ℝ)*X 2 1+(-3137785521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309046_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-327741/50000 : ℝ) < ((-159247/100000 : ℝ)*P 0+(-159247/100000 : ℝ)*P 1+(-159247/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-327741/50000 : ℝ) < (-200714524451275130989957765303/30877592000000000000000000000 : ℝ) := by norm_num
    linear_combination (8879/500000000000 : ℝ)*(base8) + (769563174633/1000000000000 : ℝ)*(base39) + (76956315737/200000000000 : ℝ)*(base40) + (21184166753/125000000000 : ℝ)*(base49) + (21184166753/125000000000 : ℝ)*(base59) + (318494000491/200000000000 : ℝ)*(major_s1_0) + (159247/100000 : ℝ)*(major_s1_1) + (159247/100000 : ℝ)*(major_s1_2) + (2166776499539/1000000000000 : ℝ)*(sp_s1_0) + (270847064969/125000000000 : ℝ)*(sp_s1_1) + (270847064969/125000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2166776517297/1000000000000 : ℝ)*(f.sum) + (10097246326427/40930000000000000000000000 : ℝ)*base62 + (11347729323143/40930000000000000000000000 : ℝ)*base64 + (11347729323143/40930000000000000000000000 : ℝ)*base66 + (87772398663/2558125000000000000000000 : ℝ)*base69 + (26865896497980759/77193980000000000000000000000 : ℝ)*base70 + (69091117399751/226320000000000000000000000 : ℝ)*base72 + (87772398663/2558125000000000000000000 : ℝ)*base75 + (1508468672359/3772000000000000000000000 : ℝ)*base76 + (234730964935026731/926327760000000000000000000000 : ℝ)*base78 + (491/200000000000 : ℝ)*base83 + (491/200000000000 : ℝ)*base85 + (491/200000000000 : ℝ)*base86 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem rawFrame_weaken_k {p k k' A : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (hX : RawFrame p k A X) (hk : k' ≤ k) : RawFrame p k' A X := by
  have f := raw_linear_data hp X hX
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  refine ⟨hX.sum,hX.row_total,hX.total_one,hX.total_cap,?_⟩
  have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
  linarith only [hh,hX.linear_failure]
theorem orderedChart_weaken {p k k' A A' d d' : ℝ}
    {X : Fin 3 → Fin 3 → ℝ} {orders : Fin 3 → Fin 3 → Fin 3}
    {signs : Fin 3 → Fin 3 → Bool} (hp : 1 ≤ p)
    (hX : OrderedChart p k A d X orders signs)
    (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    OrderedChart p k' A' d' X orders signs := by
  have hr := rawFrame_weaken_k hp hX.raw hk
  refine ⟨⟨hr.sum,hr.row_total,hr.total_one,hr.total_cap.trans hA,hr.linear_failure⟩,
    hX.permutation,?_,hX.ordered⟩
  intro i
  exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (hX.main i)
end HlawkaSchatten.DiagonalCutoff4

namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p009_b026 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=46 ∨ c=47 ∨ c=48 ∨ c=49 ∨ c=50 ∨ c=51 ∨ c=52 ∨ c=53 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact collision_c309046 p hpa (by linarith only [hpb]) X hX
  · exact collision_c308047 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c308048 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c308049 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c308050 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c308051 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c308052 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c309053 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b026 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
