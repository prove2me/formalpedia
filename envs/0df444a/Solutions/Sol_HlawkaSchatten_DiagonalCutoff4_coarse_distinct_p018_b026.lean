-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p018_b026
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:20:11.827903+00:00
-- url     : https://prove2.me/submissions/90166a50-a964-4e06-8ff6-1a7e0a313ee8

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318052_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318052_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318052_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318053_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318053_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318053_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318053_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318054_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318054_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318054_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318055_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318055_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318055_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318055_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c318052 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by
  have h0 := collision_c318052_s0 p hpa hpb X hX
  have h1 := collision_c318052_s1 p hpa hpb X hX h0
  exact collision_c318052_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c318053 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : False := by
  have h0 := collision_c318053_s0 p hpa hpb X hX
  have h1 := collision_c318053_s1 p hpa hpb X hX h0
  have h2 := collision_c318053_s2 p hpa hpb X hX h1
  exact collision_c318053_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c318054 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : False := by
  have h0 := collision_c318054_s0 p hpa hpb X hX
  have h1 := collision_c318054_s1 p hpa hpb X hX h0
  exact collision_c318054_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c318055 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c318055_s0 p hpa hpb X hX
  have h1 := collision_c318055_s1 p hpa hpb X hX h0
  have h2 := collision_c318055_s2 p hpa hpb X hX h1
  exact collision_c318055_s3 p hpa hpb X hX h2

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
theorem collision_support_c318051_s0_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-3332435237/10000000000 : ℝ)*x 0 + (3332435217/10000000000 : ℝ)*x 1 + (2842363443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3332435237/10000000000 : ℝ)^5 ≤ (25319326405147/100000000000000 : ℝ)^4 := by
    have hnat : (3332435237 : ℕ)^5*100000000000000^4 ≤ 25319326405147^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3332435237 10000000000 25319326405147 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3332435217/10000000000 : ℝ)^5 ≤ (25319326215201/100000000000000 : ℝ)^4 := by
    have hnat : (3332435217 : ℕ)^5*100000000000000^4 ≤ 25319326215201^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3332435217 10000000000 25319326215201 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2842363443/5000000000 : ℝ)^5 ≤ (1974453894467/4000000000000 : ℝ)^4 := by
    have hnat : (2842363443 : ℕ)^5*4000000000000^4 ≤ 1974453894467^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842363443 5000000000 1974453894467 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3332435237/10000000000 : ℝ), (3332435217/10000000000 : ℝ), (2842363443/5000000000 : ℝ)] ![(25319326405147/100000000000000 : ℝ), (25319326215201/100000000000000 : ℝ), (1974453894467/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3332435237/10000000000 : ℝ)|^5 ≤ (25319326405147/100000000000000 : ℝ)^4
        have hw : |(-3332435237/10000000000 : ℝ)|=(3332435237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3332435217/10000000000 : ℝ)|^5 ≤ (25319326215201/100000000000000 : ℝ)^4
        have hw : |(3332435217/10000000000 : ℝ)|=(3332435217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2842363443/5000000000 : ℝ)|^5 ≤ (1974453894467/4000000000000 : ℝ)^4
        have hw : |(2842363443/5000000000 : ℝ)|=(2842363443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (590605701/2500000000 : ℝ)*x 0 + (-590605697/2500000000 : ℝ)*x 1 + (7263893877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (590605701/2500000000 : ℝ)^5 ≤ (16470130211123/100000000000000 : ℝ)^4 := by
    have hnat : (590605701 : ℕ)^5*100000000000000^4 ≤ 16470130211123^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590605701 2500000000 16470130211123 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (590605697/2500000000 : ℝ)^5 ≤ (16470130071689/100000000000000 : ℝ)^4 := by
    have hnat : (590605697 : ℕ)^5*100000000000000^4 ≤ 16470130071689^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590605697 2500000000 16470130071689 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7263893877/10000000000 : ℝ)^5 ≤ (3352986984997/5000000000000 : ℝ)^4 := by
    have hnat : (7263893877 : ℕ)^5*5000000000000^4 ≤ 3352986984997^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7263893877 10000000000 3352986984997 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(590605701/2500000000 : ℝ), (-590605697/2500000000 : ℝ), (7263893877/10000000000 : ℝ)] ![(16470130211123/100000000000000 : ℝ), (16470130071689/100000000000000 : ℝ), (3352986984997/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(590605701/2500000000 : ℝ)|^5 ≤ (16470130211123/100000000000000 : ℝ)^4
        have hw : |(590605701/2500000000 : ℝ)|=(590605701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-590605697/2500000000 : ℝ)|^5 ≤ (16470130071689/100000000000000 : ℝ)^4
        have hw : |(-590605697/2500000000 : ℝ)|=(590605697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7263893877/10000000000 : ℝ)|^5 ≤ (3352986984997/5000000000000 : ℝ)^4
        have hw : |(7263893877/10000000000 : ℝ)|=(7263893877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-532094903/2000000000 : ℝ)*x 0 + (1703102999/10000000000 : ℝ)*x 1 + (7513450867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532094903/2000000000 : ℝ)^5 ≤ (19107280486429/100000000000000 : ℝ)^4 := by
    have hnat : (532094903 : ℕ)^5*100000000000000^4 ≤ 19107280486429^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532094903 2000000000 19107280486429 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1703102999/10000000000 : ℝ)^5 ≤ (437634078863/4000000000000 : ℝ)^4 := by
    have hnat : (1703102999 : ℕ)^5*4000000000000^4 ≤ 437634078863^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703102999 10000000000 437634078863 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7513450867/10000000000 : ℝ)^5 ≤ (69951867521487/100000000000000 : ℝ)^4 := by
    have hnat : (7513450867 : ℕ)^5*100000000000000^4 ≤ 69951867521487^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7513450867 10000000000 69951867521487 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532094903/2000000000 : ℝ), (1703102999/10000000000 : ℝ), (7513450867/10000000000 : ℝ)] ![(19107280486429/100000000000000 : ℝ), (437634078863/4000000000000 : ℝ), (69951867521487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532094903/2000000000 : ℝ)|^5 ≤ (19107280486429/100000000000000 : ℝ)^4
        have hw : |(-532094903/2000000000 : ℝ)|=(532094903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1703102999/10000000000 : ℝ)|^5 ≤ (437634078863/4000000000000 : ℝ)^4
        have hw : |(1703102999/10000000000 : ℝ)|=(1703102999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7513450867/10000000000 : ℝ)|^5 ≤ (69951867521487/100000000000000 : ℝ)^4
        have hw : |(7513450867/10000000000 : ℝ)|=(7513450867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (277859081/2500000000 : ℝ)*x 0 + (-634145103/10000000000 : ℝ)*x 1 + (2306089973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277859081/2500000000 : ℝ)^5 ≤ (6417350098721/100000000000000 : ℝ)^4 := by
    have hnat : (277859081 : ℕ)^5*100000000000000^4 ≤ 6417350098721^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277859081 2500000000 6417350098721 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (634145103/10000000000 : ℝ)^5 ≤ (3182261054899/100000000000000 : ℝ)^4 := by
    have hnat : (634145103 : ℕ)^5*100000000000000^4 ≤ 3182261054899^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634145103 10000000000 3182261054899 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2306089973/2500000000 : ℝ)^5 ≤ (45200194416689/50000000000000 : ℝ)^4 := by
    have hnat : (2306089973 : ℕ)^5*50000000000000^4 ≤ 45200194416689^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306089973 2500000000 45200194416689 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(277859081/2500000000 : ℝ), (-634145103/10000000000 : ℝ), (2306089973/2500000000 : ℝ)] ![(6417350098721/100000000000000 : ℝ), (3182261054899/100000000000000 : ℝ), (45200194416689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(277859081/2500000000 : ℝ)|^5 ≤ (6417350098721/100000000000000 : ℝ)^4
        have hw : |(277859081/2500000000 : ℝ)|=(277859081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-634145103/10000000000 : ℝ)|^5 ≤ (3182261054899/100000000000000 : ℝ)^4
        have hw : |(-634145103/10000000000 : ℝ)|=(634145103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2306089973/2500000000 : ℝ)|^5 ≤ (45200194416689/50000000000000 : ℝ)^4
        have hw : |(2306089973/2500000000 : ℝ)|=(2306089973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3979071423/10000000000 : ℝ)*x 0 + (91495931/125000000 : ℝ)*x 1 + (-187326167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3979071423/10000000000 : ℝ)^5 ≤ (6320583367609/20000000000000 : ℝ)^4 := by
    have hnat : (3979071423 : ℕ)^5*20000000000000^4 ≤ 6320583367609^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979071423 10000000000 6320583367609 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91495931/125000000 : ℝ)^5 ≤ (67704059489943/100000000000000 : ℝ)^4 := by
    have hnat : (91495931 : ℕ)^5*100000000000000^4 ≤ 67704059489943^4*125000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91495931 125000000 67704059489943 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187326167/10000000000 : ℝ)^5 ≤ (693023654827/100000000000000 : ℝ)^4 := by
    have hnat : (187326167 : ℕ)^5*100000000000000^4 ≤ 693023654827^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187326167 10000000000 693023654827 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3979071423/10000000000 : ℝ), (91495931/125000000 : ℝ), (-187326167/10000000000 : ℝ)] ![(6320583367609/20000000000000 : ℝ), (67704059489943/100000000000000 : ℝ), (693023654827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3979071423/10000000000 : ℝ)|^5 ≤ (6320583367609/20000000000000 : ℝ)^4
        have hw : |(3979071423/10000000000 : ℝ)|=(3979071423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91495931/125000000 : ℝ)|^5 ≤ (67704059489943/100000000000000 : ℝ)^4
        have hw : |(91495931/125000000 : ℝ)|=(91495931/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-187326167/10000000000 : ℝ)|^5 ≤ (693023654827/100000000000000 : ℝ)^4
        have hw : |(-187326167/10000000000 : ℝ)|=(187326167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2695247091/10000000000 : ℝ)*x 0 + (8346871341/10000000000 : ℝ)*x 1 + (104860817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695247091/10000000000 : ℝ)^5 ≤ (3883991118449/20000000000000 : ℝ)^4 := by
    have hnat : (2695247091 : ℕ)^5*20000000000000^4 ≤ 3883991118449^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695247091 10000000000 3883991118449 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8346871341/10000000000 : ℝ)^5 ≤ (79781950401817/100000000000000 : ℝ)^4 := by
    have hnat : (8346871341 : ℕ)^5*100000000000000^4 ≤ 79781950401817^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8346871341 10000000000 79781950401817 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104860817/5000000000 : ℝ)^5 ≤ (399046995519/50000000000000 : ℝ)^4 := by
    have hnat : (104860817 : ℕ)^5*50000000000000^4 ≤ 399046995519^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104860817 5000000000 399046995519 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695247091/10000000000 : ℝ), (8346871341/10000000000 : ℝ), (104860817/5000000000 : ℝ)] ![(3883991118449/20000000000000 : ℝ), (79781950401817/100000000000000 : ℝ), (399046995519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695247091/10000000000 : ℝ)|^5 ≤ (3883991118449/20000000000000 : ℝ)^4
        have hw : |(2695247091/10000000000 : ℝ)|=(2695247091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8346871341/10000000000 : ℝ)|^5 ≤ (79781950401817/100000000000000 : ℝ)^4
        have hw : |(8346871341/10000000000 : ℝ)|=(8346871341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104860817/5000000000 : ℝ)|^5 ≤ (399046995519/50000000000000 : ℝ)^4
        have hw : |(104860817/5000000000 : ℝ)|=(104860817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-458381201/2500000000 : ℝ)*x 0 + (2734753019/10000000000 : ℝ)*x 1 + (3682373653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (458381201/2500000000 : ℝ)^5 ≤ (93734294983/781250000000 : ℝ)^4 := by
    have hnat : (458381201 : ℕ)^5*781250000000^4 ≤ 93734294983^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458381201 2500000000 93734294983 781250000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734753019/10000000000 : ℝ)^5 ≤ (2472052279439/12500000000000 : ℝ)^4 := by
    have hnat : (2734753019 : ℕ)^5*12500000000000^4 ≤ 2472052279439^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734753019 10000000000 2472052279439 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3682373653/5000000000 : ℝ)^5 ≤ (68225592002107/100000000000000 : ℝ)^4 := by
    have hnat : (3682373653 : ℕ)^5*100000000000000^4 ≤ 68225592002107^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3682373653 5000000000 68225592002107 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-458381201/2500000000 : ℝ), (2734753019/10000000000 : ℝ), (3682373653/5000000000 : ℝ)] ![(93734294983/781250000000 : ℝ), (2472052279439/12500000000000 : ℝ), (68225592002107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-458381201/2500000000 : ℝ)|^5 ≤ (93734294983/781250000000 : ℝ)^4
        have hw : |(-458381201/2500000000 : ℝ)|=(458381201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734753019/10000000000 : ℝ)|^5 ≤ (2472052279439/12500000000000 : ℝ)^4
        have hw : |(2734753019/10000000000 : ℝ)|=(2734753019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3682373653/5000000000 : ℝ)|^5 ≤ (68225592002107/100000000000000 : ℝ)^4
        have hw : |(3682373653/5000000000 : ℝ)|=(3682373653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (418114051/5000000000 : ℝ)*x 0 + (-625382463/5000000000 : ℝ)*x 1 + (282288039/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418114051/5000000000 : ℝ)^5 ≤ (112420614911/2500000000000 : ℝ)^4 := by
    have hnat : (418114051 : ℕ)^5*2500000000000^4 ≤ 112420614911^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418114051 5000000000 112420614911 2500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625382463/5000000000 : ℝ)^5 ≤ (3719115125049/50000000000000 : ℝ)^4 := by
    have hnat : (625382463 : ℕ)^5*50000000000000^4 ≤ 3719115125049^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625382463 5000000000 3719115125049 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282288039/312500000 : ℝ)^5 ≤ (88064945136523/100000000000000 : ℝ)^4 := by
    have hnat : (282288039 : ℕ)^5*100000000000000^4 ≤ 88064945136523^4*312500000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282288039 312500000 88064945136523 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418114051/5000000000 : ℝ), (-625382463/5000000000 : ℝ), (282288039/312500000 : ℝ)] ![(112420614911/2500000000000 : ℝ), (3719115125049/50000000000000 : ℝ), (88064945136523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418114051/5000000000 : ℝ)|^5 ≤ (112420614911/2500000000000 : ℝ)^4
        have hw : |(418114051/5000000000 : ℝ)|=(418114051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-625382463/5000000000 : ℝ)|^5 ≤ (3719115125049/50000000000000 : ℝ)^4
        have hw : |(-625382463/5000000000 : ℝ)|=(625382463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282288039/312500000 : ℝ)|^5 ≤ (88064945136523/100000000000000 : ℝ)^4
        have hw : |(282288039/312500000 : ℝ)|=(282288039/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1922739743/2500000000 : ℝ)*x 0 + (3564075753/10000000000 : ℝ)*x 1 + (-129816151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1922739743/2500000000 : ℝ)^5 ≤ (36011865759457/50000000000000 : ℝ)^4 := by
    have hnat : (1922739743 : ℕ)^5*50000000000000^4 ≤ 36011865759457^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922739743 2500000000 36011865759457 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3564075753/10000000000 : ℝ)^5 ≤ (13769040016419/50000000000000 : ℝ)^4 := by
    have hnat : (3564075753 : ℕ)^5*50000000000000^4 ≤ 13769040016419^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3564075753 10000000000 13769040016419 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129816151/10000000000 : ℝ)^5 ≤ (438188434243/100000000000000 : ℝ)^4 := by
    have hnat : (129816151 : ℕ)^5*100000000000000^4 ≤ 438188434243^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129816151 10000000000 438188434243 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1922739743/2500000000 : ℝ), (3564075753/10000000000 : ℝ), (-129816151/10000000000 : ℝ)] ![(36011865759457/50000000000000 : ℝ), (13769040016419/50000000000000 : ℝ), (438188434243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1922739743/2500000000 : ℝ)|^5 ≤ (36011865759457/50000000000000 : ℝ)^4
        have hw : |(1922739743/2500000000 : ℝ)|=(1922739743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3564075753/10000000000 : ℝ)|^5 ≤ (13769040016419/50000000000000 : ℝ)^4
        have hw : |(3564075753/10000000000 : ℝ)|=(3564075753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129816151/10000000000 : ℝ)|^5 ≤ (438188434243/100000000000000 : ℝ)^4
        have hw : |(-129816151/10000000000 : ℝ)|=(129816151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (7637517859/10000000000 : ℝ)*x 0 + (3594265537/10000000000 : ℝ)*x 1 + (25509607/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7637517859/10000000000 : ℝ)^5 ≤ (17849674756899/25000000000000 : ℝ)^4 := by
    have hnat : (7637517859 : ℕ)^5*25000000000000^4 ≤ 17849674756899^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7637517859 10000000000 17849674756899 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3594265537/10000000000 : ℝ)^5 ≤ (347874593167/1250000000000 : ℝ)^4 := by
    have hnat : (3594265537 : ℕ)^5*1250000000000^4 ≤ 347874593167^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3594265537 10000000000 347874593167 1250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25509607/1250000000 : ℝ)^5 ≤ (192833374967/25000000000000 : ℝ)^4 := by
    have hnat : (25509607 : ℕ)^5*25000000000000^4 ≤ 192833374967^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25509607 1250000000 192833374967 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7637517859/10000000000 : ℝ), (3594265537/10000000000 : ℝ), (25509607/1250000000 : ℝ)] ![(17849674756899/25000000000000 : ℝ), (347874593167/1250000000000 : ℝ), (192833374967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7637517859/10000000000 : ℝ)|^5 ≤ (17849674756899/25000000000000 : ℝ)^4
        have hw : |(7637517859/10000000000 : ℝ)|=(7637517859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3594265537/10000000000 : ℝ)|^5 ≤ (347874593167/1250000000000 : ℝ)^4
        have hw : |(3594265537/10000000000 : ℝ)|=(3594265537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25509607/1250000000 : ℝ)|^5 ≤ (192833374967/25000000000000 : ℝ)^4
        have hw : |(25509607/1250000000 : ℝ)|=(25509607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-5292322227/10000000000 : ℝ)*x 0 + (860930867/2000000000 : ℝ)*x 1 + (1379327929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292322227/10000000000 : ℝ)^5 ≤ (22569807381099/50000000000000 : ℝ)^4 := by
    have hnat : (5292322227 : ℕ)^5*50000000000000^4 ≤ 22569807381099^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292322227 10000000000 22569807381099 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (860930867/2000000000 : ℝ)^5 ≤ (8716916034867/25000000000000 : ℝ)^4 := by
    have hnat : (860930867 : ℕ)^5*25000000000000^4 ≤ 8716916034867^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860930867 2000000000 8716916034867 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379327929/5000000000 : ℝ)^5 ≤ (19992721076999/100000000000000 : ℝ)^4 := by
    have hnat : (1379327929 : ℕ)^5*100000000000000^4 ≤ 19992721076999^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379327929 5000000000 19992721076999 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5292322227/10000000000 : ℝ), (860930867/2000000000 : ℝ), (1379327929/5000000000 : ℝ)] ![(22569807381099/50000000000000 : ℝ), (8716916034867/25000000000000 : ℝ), (19992721076999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5292322227/10000000000 : ℝ)|^5 ≤ (22569807381099/50000000000000 : ℝ)^4
        have hw : |(-5292322227/10000000000 : ℝ)|=(5292322227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(860930867/2000000000 : ℝ)|^5 ≤ (8716916034867/25000000000000 : ℝ)^4
        have hw : |(860930867/2000000000 : ℝ)|=(860930867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1379327929/5000000000 : ℝ)|^5 ≤ (19992721076999/100000000000000 : ℝ)^4
        have hw : |(1379327929/5000000000 : ℝ)|=(1379327929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (191497987/2500000000 : ℝ)*x 0 + (-87682991/500000000 : ℝ)*x 1 + (8749560661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191497987/2500000000 : ℝ)^5 ≤ (503721245501/12500000000000 : ℝ)^4 := by
    have hnat : (191497987 : ℕ)^5*12500000000000^4 ≤ 503721245501^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191497987 2500000000 503721245501 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87682991/500000000 : ℝ)^5 ≤ (5674161513499/50000000000000 : ℝ)^4 := by
    have hnat : (87682991 : ℕ)^5*50000000000000^4 ≤ 5674161513499^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87682991 500000000 5674161513499 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8749560661/10000000000 : ℝ)^5 ≤ (84621906986119/100000000000000 : ℝ)^4 := by
    have hnat : (8749560661 : ℕ)^5*100000000000000^4 ≤ 84621906986119^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8749560661 10000000000 84621906986119 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(191497987/2500000000 : ℝ), (-87682991/500000000 : ℝ), (8749560661/10000000000 : ℝ)] ![(503721245501/12500000000000 : ℝ), (5674161513499/50000000000000 : ℝ), (84621906986119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(191497987/2500000000 : ℝ)|^5 ≤ (503721245501/12500000000000 : ℝ)^4
        have hw : |(191497987/2500000000 : ℝ)|=(191497987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87682991/500000000 : ℝ)|^5 ≤ (5674161513499/50000000000000 : ℝ)^4
        have hw : |(-87682991/500000000 : ℝ)|=(87682991/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8749560661/10000000000 : ℝ)|^5 ≤ (84621906986119/100000000000000 : ℝ)^4
        have hw : |(8749560661/10000000000 : ℝ)|=(8749560661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3443590153/5000000000 : ℝ)*x 0 + (563855509/1250000000 : ℝ)*x 1 + (-23407953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3443590153/5000000000 : ℝ)^5 ≤ (12548210971869/20000000000000 : ℝ)^4 := by
    have hnat : (3443590153 : ℕ)^5*20000000000000^4 ≤ 12548210971869^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3443590153 5000000000 12548210971869 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563855509/1250000000 : ℝ)^5 ≤ (36967686170707/100000000000000 : ℝ)^4 := by
    have hnat : (563855509 : ℕ)^5*100000000000000^4 ≤ 36967686170707^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563855509 1250000000 36967686170707 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23407953/2500000000 : ℝ)^5 ≤ (291258953757/100000000000000 : ℝ)^4 := by
    have hnat : (23407953 : ℕ)^5*100000000000000^4 ≤ 291258953757^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23407953 2500000000 291258953757 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3443590153/5000000000 : ℝ), (563855509/1250000000 : ℝ), (-23407953/2500000000 : ℝ)] ![(12548210971869/20000000000000 : ℝ), (36967686170707/100000000000000 : ℝ), (291258953757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3443590153/5000000000 : ℝ)|^5 ≤ (12548210971869/20000000000000 : ℝ)^4
        have hw : |(3443590153/5000000000 : ℝ)|=(3443590153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563855509/1250000000 : ℝ)|^5 ≤ (36967686170707/100000000000000 : ℝ)^4
        have hw : |(563855509/1250000000 : ℝ)|=(563855509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23407953/2500000000 : ℝ)|^5 ≤ (291258953757/100000000000000 : ℝ)^4
        have hw : |(-23407953/2500000000 : ℝ)|=(23407953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s0_27 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1300149083/5000000000 : ℝ)*x 0 + (8460356187/10000000000 : ℝ)*x 1 + (23407953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1300149083/5000000000 : ℝ)^5 ≤ (4642147608093/25000000000000 : ℝ)^4 := by
    have hnat : (1300149083 : ℕ)^5*25000000000000^4 ≤ 4642147608093^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300149083 5000000000 4642147608093 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8460356187/10000000000 : ℝ)^5 ≤ (81140150594753/100000000000000 : ℝ)^4 := by
    have hnat : (8460356187 : ℕ)^5*100000000000000^4 ≤ 81140150594753^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8460356187 10000000000 81140150594753 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23407953/2500000000 : ℝ)^5 ≤ (291258953757/100000000000000 : ℝ)^4 := by
    have hnat : (23407953 : ℕ)^5*100000000000000^4 ≤ 291258953757^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23407953 2500000000 291258953757 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1300149083/5000000000 : ℝ), (8460356187/10000000000 : ℝ), (23407953/2500000000 : ℝ)] ![(4642147608093/25000000000000 : ℝ), (81140150594753/100000000000000 : ℝ), (291258953757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1300149083/5000000000 : ℝ)|^5 ≤ (4642147608093/25000000000000 : ℝ)^4
        have hw : |(1300149083/5000000000 : ℝ)|=(1300149083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8460356187/10000000000 : ℝ)|^5 ≤ (81140150594753/100000000000000 : ℝ)^4
        have hw : |(8460356187/10000000000 : ℝ)|=(8460356187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(23407953/2500000000 : ℝ)|^5 ≤ (291258953757/100000000000000 : ℝ)^4
        have hw : |(23407953/2500000000 : ℝ)|=(23407953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-3643517763/10000000000 : ℝ)*x 0 + (1818414743/5000000000 : ℝ)*x 1 + (1283310547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3643517763/10000000000 : ℝ)^5 ≤ (28307473794529/100000000000000 : ℝ)^4 := by
    have hnat : (3643517763 : ℕ)^5*100000000000000^4 ≤ 28307473794529^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3643517763 10000000000 28307473794529 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1818414743/5000000000 : ℝ)^5 ≤ (7060633729247/25000000000000 : ℝ)^4 := by
    have hnat : (1818414743 : ℕ)^5*25000000000000^4 ≤ 7060633729247^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818414743 5000000000 7060633729247 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1283310547/2500000000 : ℝ)^5 ≤ (43449991279409/100000000000000 : ℝ)^4 := by
    have hnat : (1283310547 : ℕ)^5*100000000000000^4 ≤ 43449991279409^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283310547 2500000000 43449991279409 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3643517763/10000000000 : ℝ), (1818414743/5000000000 : ℝ), (1283310547/2500000000 : ℝ)] ![(28307473794529/100000000000000 : ℝ), (7060633729247/25000000000000 : ℝ), (43449991279409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3643517763/10000000000 : ℝ)|^5 ≤ (28307473794529/100000000000000 : ℝ)^4
        have hw : |(-3643517763/10000000000 : ℝ)|=(3643517763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1818414743/5000000000 : ℝ)|^5 ≤ (7060633729247/25000000000000 : ℝ)^4
        have hw : |(1818414743/5000000000 : ℝ)|=(1818414743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1283310547/2500000000 : ℝ)|^5 ≤ (43449991279409/100000000000000 : ℝ)^4
        have hw : |(1283310547/2500000000 : ℝ)|=(1283310547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (291967877/1000000000 : ℝ)*x 0 + (-2914319219/10000000000 : ℝ)*x 1 + (1277889219/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291967877/1000000000 : ℝ)^5 ≤ (21461933257231/100000000000000 : ℝ)^4 := by
    have hnat : (291967877 : ℕ)^5*100000000000000^4 ≤ 21461933257231^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291967877 1000000000 21461933257231 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2914319219/10000000000 : ℝ)^5 ≤ (10706349211541/50000000000000 : ℝ)^4 := by
    have hnat : (2914319219 : ℕ)^5*50000000000000^4 ≤ 10706349211541^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2914319219 10000000000 10706349211541 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1277889219/2000000000 : ℝ)^5 ≤ (14281342077917/25000000000000 : ℝ)^4 := by
    have hnat : (1277889219 : ℕ)^5*25000000000000^4 ≤ 14281342077917^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277889219 2000000000 14281342077917 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(291967877/1000000000 : ℝ), (-2914319219/10000000000 : ℝ), (1277889219/2000000000 : ℝ)] ![(21461933257231/100000000000000 : ℝ), (10706349211541/50000000000000 : ℝ), (14281342077917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(291967877/1000000000 : ℝ)|^5 ≤ (21461933257231/100000000000000 : ℝ)^4
        have hw : |(291967877/1000000000 : ℝ)|=(291967877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2914319219/10000000000 : ℝ)|^5 ≤ (10706349211541/50000000000000 : ℝ)^4
        have hw : |(-2914319219/10000000000 : ℝ)|=(2914319219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1277889219/2000000000 : ℝ)|^5 ≤ (14281342077917/25000000000000 : ℝ)^4
        have hw : |(1277889219/2000000000 : ℝ)|=(1277889219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2660492751/5000000000 : ℝ)*x 0 + (5329850437/10000000000 : ℝ)*x 1 + (-1458657967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2660492751/5000000000 : ℝ)^5 ≤ (45445417179889/100000000000000 : ℝ)^4 := by
    have hnat : (2660492751 : ℕ)^5*100000000000000^4 ≤ 45445417179889^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2660492751 5000000000 45445417179889 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5329850437/10000000000 : ℝ)^5 ≤ (11385019702779/25000000000000 : ℝ)^4 := by
    have hnat : (5329850437 : ℕ)^5*25000000000000^4 ≤ 11385019702779^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5329850437 10000000000 11385019702779 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1458657967/10000000000 : ℝ)^5 ≤ (4507251997319/50000000000000 : ℝ)^4 := by
    have hnat : (1458657967 : ℕ)^5*50000000000000^4 ≤ 4507251997319^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458657967 10000000000 4507251997319 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2660492751/5000000000 : ℝ), (5329850437/10000000000 : ℝ), (-1458657967/10000000000 : ℝ)] ![(45445417179889/100000000000000 : ℝ), (11385019702779/25000000000000 : ℝ), (4507251997319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2660492751/5000000000 : ℝ)|^5 ≤ (45445417179889/100000000000000 : ℝ)^4
        have hw : |(2660492751/5000000000 : ℝ)|=(2660492751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5329850437/10000000000 : ℝ)|^5 ≤ (11385019702779/25000000000000 : ℝ)^4
        have hw : |(5329850437/10000000000 : ℝ)|=(5329850437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1458657967/10000000000 : ℝ)|^5 ≤ (4507251997319/50000000000000 : ℝ)^4
        have hw : |(-1458657967/10000000000 : ℝ)|=(1458657967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318051_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5055096189/10000000000 : ℝ)*x 0 + (79117471/156250000 : ℝ)*x 1 + (2152524441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5055096189/10000000000 : ℝ)^5 ≤ (42624743616273/100000000000000 : ℝ)^4 := by
    have hnat : (5055096189 : ℕ)^5*100000000000000^4 ≤ 42624743616273^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5055096189 10000000000 42624743616273 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79117471/156250000 : ℝ)^5 ≤ (42713529859871/100000000000000 : ℝ)^4 := by
    have hnat : (79117471 : ℕ)^5*100000000000000^4 ≤ 42713529859871^4*156250000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79117471 156250000 42713529859871 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152524441/10000000000 : ℝ)^5 ≤ (14661726510697/100000000000000 : ℝ)^4 := by
    have hnat : (2152524441 : ℕ)^5*100000000000000^4 ≤ 14661726510697^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152524441 10000000000 14661726510697 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5055096189/10000000000 : ℝ), (79117471/156250000 : ℝ), (2152524441/10000000000 : ℝ)] ![(42624743616273/100000000000000 : ℝ), (42713529859871/100000000000000 : ℝ), (14661726510697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5055096189/10000000000 : ℝ)|^5 ≤ (42624743616273/100000000000000 : ℝ)^4
        have hw : |(5055096189/10000000000 : ℝ)|=(5055096189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(79117471/156250000 : ℝ)|^5 ≤ (42713529859871/100000000000000 : ℝ)^4
        have hw : |(79117471/156250000 : ℝ)|=(79117471/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2152524441/10000000000 : ℝ)|^5 ≤ (14661726510697/100000000000000 : ℝ)^4
        have hw : |(2152524441/10000000000 : ℝ)|=(2152524441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318051 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (34269/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3332435237/10000000000 : ℝ)*X 0 0+(3332435217/10000000000 : ℝ)*X 0 1+(2842363443/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((590605701/2500000000 : ℝ)*X 1 0+(-590605697/2500000000 : ℝ)*X 1 1+(7263893877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-532094903/2000000000 : ℝ)*X 0 0+(1703102999/10000000000 : ℝ)*X 0 1+(7513450867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((277859081/2500000000 : ℝ)*X 1 0+(-634145103/10000000000 : ℝ)*X 1 1+(2306089973/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3979071423/10000000000 : ℝ)*X 2 0+(91495931/125000000 : ℝ)*X 2 1+(-187326167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2695247091/10000000000 : ℝ)*X 0 0+(8346871341/10000000000 : ℝ)*X 0 1+(104860817/5000000000 : ℝ)*X 0 2+(2695247091/10000000000 : ℝ)*X 1 0+(8346871341/10000000000 : ℝ)*X 1 1+(104860817/5000000000 : ℝ)*X 1 2+(2695247091/10000000000 : ℝ)*X 2 0+(8346871341/10000000000 : ℝ)*X 2 1+(104860817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-458381201/2500000000 : ℝ)*X 0 0+(2734753019/10000000000 : ℝ)*X 0 1+(3682373653/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((418114051/5000000000 : ℝ)*X 1 0+(-625382463/5000000000 : ℝ)*X 1 1+(282288039/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1922739743/2500000000 : ℝ)*X 2 0+(3564075753/10000000000 : ℝ)*X 2 1+(-129816151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7637517859/10000000000 : ℝ)*X 0 0+(3594265537/10000000000 : ℝ)*X 0 1+(25509607/1250000000 : ℝ)*X 0 2+(7637517859/10000000000 : ℝ)*X 1 0+(3594265537/10000000000 : ℝ)*X 1 1+(25509607/1250000000 : ℝ)*X 1 2+(7637517859/10000000000 : ℝ)*X 2 0+(3594265537/10000000000 : ℝ)*X 2 1+(25509607/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-5292322227/10000000000 : ℝ)*X 0 0+(860930867/2000000000 : ℝ)*X 0 1+(1379327929/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((191497987/2500000000 : ℝ)*X 1 0+(-87682991/500000000 : ℝ)*X 1 1+(8749560661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3443590153/5000000000 : ℝ)*X 2 0+(563855509/1250000000 : ℝ)*X 2 1+(-23407953/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1300149083/5000000000 : ℝ)*X 0 0+(8460356187/10000000000 : ℝ)*X 0 1+(23407953/2500000000 : ℝ)*X 0 2+(1300149083/5000000000 : ℝ)*X 1 0+(8460356187/10000000000 : ℝ)*X 1 1+(23407953/2500000000 : ℝ)*X 1 2+(1300149083/5000000000 : ℝ)*X 2 0+(8460356187/10000000000 : ℝ)*X 2 1+(23407953/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((8849/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8849/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (191817556633261419/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (431939893253/500000000000 : ℝ)*(base7) + (7927771/1000000000000 : ℝ)*(base19) + (1590571/500000000000 : ℝ)*(base49) + (51520590301/1000000000000 : ℝ)*(base60) + (1742029756309/1000000000000 : ℝ)*(major_s0_0) + (1742029756309/1000000000000 : ℝ)*(major_s0_1) + (1742029756309/1000000000000 : ℝ)*(major_s0_2) + (2822207/500000000000 : ℝ)*(sp_s0_0) + (2035901602601/1000000000000 : ℝ)*(sp_s0_7) + (1017986310851/500000000000 : ℝ)*(sp_s0_8) + (2035980549473/1000000000000 : ℝ)*(sp_s0_9) + (1818305236631/1000000000000 : ℝ)*(sp_s0_13) + (36651229/500000000000 : ℝ)*(sp_s0_14) + (121089517/500000000000 : ℝ)*(sp_s0_27) + (23866690729/25000000000 : ℝ)*(f.failure) + (2035980549473/1000000000000 : ℝ)*(f.sum) + (5310221/50000000000000000000 : ℝ)*base62 + (1213341465679201/5000000000000000000000000000 : ℝ)*base64 + (1398472108820799/5000000000000000000000000000 : ℝ)*base66 + (2012941471415369/5000000000000000000000000000 : ℝ)*base68 + (8445546467021/625000000000000000000000000 : ℝ)*base71 + (2038669654679201/5000000000000000000000000000 : ℝ)*base72 + (1193057357084631/5000000000000000000000000000 : ℝ)*base74 + (443643569584631/5000000000000000000000000000 : ℝ)*base76 + (539155329/10000000000000000000000 : ℝ)*base79 + (71/100000000000000 : ℝ)*base87 + (71/100000000000000 : ℝ)*base89 + (71/100000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70093/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70093/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (21542586705857255107383/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (266065094167/1000000000000 : ℝ)*(base5) + (841841185773/1000000000000 : ℝ)*(base7) + (7621/125000000000 : ℝ)*(base49) + (36637358457/200000000000 : ℝ)*(base60) + (948324648819/500000000000 : ℝ)*(major_s0_0) + (948324648819/500000000000 : ℝ)*(major_s0_1) + (948324648819/500000000000 : ℝ)*(major_s0_2) + (14020169/1000000000000 : ℝ)*(sp_s0_0) + (78378237/1000000000000 : ℝ)*(sp_s0_7) + (2272980585933/1000000000000 : ℝ)*(sp_s0_14) + (568255881873/250000000000 : ℝ)*(sp_s0_15) + (507827615701/200000000000 : ℝ)*(sp_s0_16) + (403794591149/250000000000 : ℝ)*(sp_s0_20) + (24728423/500000000000 : ℝ)*(sp_s0_22) + (103940227299/100000000000 : ℝ)*(f.failure) + (1136536492169/500000000000 : ℝ)*(f.sum) + (879771819/2500000000000000000000 : ℝ)*base63 + (675559176134409/2500000000000000000000000000 : ℝ)*base65 + (735088201634409/2500000000000000000000000000 : ℝ)*base66 + (641737890278721/2500000000000000000000000000 : ℝ)*base69 + (109455889450711/312500000000000000000000000 : ℝ)*base71 + (378215880384409/2500000000000000000000000000 : ℝ)*base73 + (988286135278721/2500000000000000000000000000 : ℝ)*base74 + (206111258528721/2500000000000000000000000000 : ℝ)*base76 + (3081544079/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (201/400000000000000 : ℝ)*base87 + (201/400000000000000 : ℝ)*base89 + (201/400000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(989/3125 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(989/3125 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (260369647445297227107/31250000000000000000000000 : ℝ) := by norm_num
    linear_combination (90541881383/1000000000000 : ℝ)*(base5) + (159730813311/1000000000000 : ℝ)*(base7) + (536377907753/1000000000000 : ℝ)*(base39) + (346453/125000000000 : ℝ)*(base44) + (275071129749/500000000000 : ℝ)*(base49) + (1703496402017/1000000000000 : ℝ)*(major_s0_0) + (1703493630393/1000000000000 : ℝ)*(major_s0_1) + (1703496402017/1000000000000 : ℝ)*(major_s0_2) + (14765023/500000000000 : ℝ)*(sp_s0_1) + (4412817/250000000000 : ℝ)*(sp_s0_16) + (2382209203053/1000000000000 : ℝ)*(sp_s0_21) + (2382176901383/1000000000000 : ℝ)*(sp_s0_22) + (154545839573/62500000000 : ℝ)*(sp_s0_23) + (1002736729981/1000000000000 : ℝ)*(sp_s0_27) + (233387642419/250000000000 : ℝ)*(f.failure) + (2382209203053/1000000000000 : ℝ)*(f.sum) + (17903343984027/625000000000000000000000000 : ℝ)*base63 + (1370985985559613/5000000000000000000000000000 : ℝ)*base64 + (2008283162797877/5000000000000000000000000000 : ℝ)*base67 + (873924165730203/5000000000000000000000000000 : ℝ)*base69 + (6208490401273/625000000000000000000000000 : ℝ)*base71 + (1087738576940387/5000000000000000000000000000 : ℝ)*base73 + (654366161642013/5000000000000000000000000000 : ℝ)*base75 + (1246111796230203/5000000000000000000000000000 : ℝ)*base76 + (63170369654783/625000000000000000000000000 : ℝ)*base79 + (719/1000000000000000 : ℝ)*base86 + (719/1000000000000000 : ℝ)*base88 + (719/1000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (8849/12500 : ℝ) ^ (39/8 : ℝ) ≤ (9282028382049475383/50000000000000000000 : ℝ) := by
    have hpowers : (8849/12500 : ℝ)^39 ≤ (9282028382049475383/50000000000000000000 : ℝ)^8 := by
      have hnat : (8849 : ℕ)^39*50000000000000000000^8 ≤ 9282028382049475383^8*12500^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8849 12500 9282028382049475383 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8849/12500 : ℝ)) (X := (9282028382049475383/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (59282028382049475383/50000000000000000000 : ℝ) ≤ (2071094198830613/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (59282028382049475383/50000000000000000000 : ℝ)^8 ≤ (2071094198830613/2000000000000000 : ℝ)^39 := by
      have hnat : (59282028382049475383 : ℕ)^8*2000000000000000^39 ≤ 2071094198830613^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59282028382049475383 50000000000000000000 2071094198830613 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2071094198830613/2000000000000000 : ℝ)) (X := (59282028382049475383/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (34282028382049475383/25000000000000000000 : ℝ) ≤ (10669117869446129/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (34282028382049475383/25000000000000000000 : ℝ)^8 ≤ (10669117869446129/10000000000000000 : ℝ)^39 := by
      have hnat : (34282028382049475383 : ℕ)^8*10000000000000000^39 ≤ 10669117869446129^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34282028382049475383 25000000000000000000 10669117869446129 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10669117869446129/10000000000000000 : ℝ)) (X := (34282028382049475383/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(71094198830613/1415840000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(39205859411633/884900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (8849/12500 : ℝ)) (alpha := (71094198830613/1415840000000000 : ℝ)) (beta := (39205859411633/884900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (8849/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(71094198830613/1415840000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(39205859411633/884900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (70093/100000 : ℝ) ^ (39/8 : ℝ) ≤ (17687396457117590411/100000000000000000000 : ℝ) := by
    have hpowers : (70093/100000 : ℝ)^39 ≤ (17687396457117590411/100000000000000000000 : ℝ)^8 := by
      have hnat : (70093 : ℕ)^39*100000000000000000000^8 ≤ 17687396457117590411^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70093 100000 17687396457117590411 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70093/100000 : ℝ)) (X := (17687396457117590411/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (117687396457117590411/100000000000000000000 : ℝ) ≤ (5169859173447367/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (117687396457117590411/100000000000000000000 : ℝ)^8 ≤ (5169859173447367/5000000000000000 : ℝ)^39 := by
      have hnat : (117687396457117590411 : ℕ)^8*5000000000000000^39 ≤ 5169859173447367^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117687396457117590411 100000000000000000000 5169859173447367 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5169859173447367/5000000000000000 : ℝ)) (X := (117687396457117590411/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (67687396457117590411/50000000000000000000 : ℝ) ≤ (106409919318723/100000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (67687396457117590411/50000000000000000000 : ℝ)^8 ≤ (106409919318723/100000000000000 : ℝ)^39 := by
      have hnat : (67687396457117590411 : ℕ)^8*100000000000000^39 ≤ 106409919318723^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67687396457117590411 50000000000000000000 106409919318723 100000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (106409919318723/100000000000000 : ℝ)) (X := (67687396457117590411/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(169859173447367/3504650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(150636792488783/3504650000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (70093/100000 : ℝ)) (alpha := (169859173447367/3504650000000000 : ℝ)) (beta := (150636792488783/3504650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (70093/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(169859173447367/3504650000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(150636792488783/3504650000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (989/3125 : ℝ) ^ (39/8 : ℝ) ≤ (366596290262915023/100000000000000000000 : ℝ) := by
    have hpowers : (989/3125 : ℝ)^39 ≤ (366596290262915023/100000000000000000000 : ℝ)^8 := by
      have hnat : (989 : ℕ)^39*100000000000000000000^8 ≤ 366596290262915023^8*3125^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        989 3125 366596290262915023 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (989/3125 : ℝ)) (X := (366596290262915023/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100366596290262915023/100000000000000000000 : ℝ) ≤ (5003754495727013/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (100366596290262915023/100000000000000000000 : ℝ)^8 ≤ (5003754495727013/5000000000000000 : ℝ)^39 := by
      have hnat : (100366596290262915023 : ℕ)^8*5000000000000000^39 ≤ 5003754495727013^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100366596290262915023 100000000000000000000 5003754495727013 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003754495727013/5000000000000000 : ℝ)) (X := (100366596290262915023/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50366596290262915023/50000000000000000000 : ℝ) ≤ (2002999242679979/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (50366596290262915023/50000000000000000000 : ℝ)^8 ≤ (2002999242679979/2000000000000000 : ℝ)^39 := by
      have hnat : (50366596290262915023 : ℕ)^8*2000000000000000^39 ≤ 2002999242679979^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50366596290262915023 50000000000000000000 2002999242679979 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002999242679979/2000000000000000 : ℝ)) (X := (50366596290262915023/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(3754495727013/1582400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(7487221945869/3164800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (989/3125 : ℝ)) (alpha := (3754495727013/1582400000000000 : ℝ)) (beta := (7487221945869/3164800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (989/3125 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(3754495727013/1582400000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(7487221945869/3164800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3643517763/10000000000 : ℝ)*X 0 0+(1818414743/5000000000 : ℝ)*X 0 1+(1283310547/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((291967877/1000000000 : ℝ)*X 1 0+(-2914319219/10000000000 : ℝ)*X 1 1+(1277889219/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2660492751/5000000000 : ℝ)*X 2 0+(5329850437/10000000000 : ℝ)*X 2 1+(-1458657967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5055096189/10000000000 : ℝ)*X 0 0+(79117471/156250000 : ℝ)*X 0 1+(2152524441/10000000000 : ℝ)*X 0 2+(5055096189/10000000000 : ℝ)*X 1 0+(79117471/156250000 : ℝ)*X 1 1+(2152524441/10000000000 : ℝ)*X 1 2+(5055096189/10000000000 : ℝ)*X 2 0+(79117471/156250000 : ℝ)*X 2 1+(2152524441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318051_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15897/2000 : ℝ) < ((-7299/4000 : ℝ)*P 0+(-7299/4000 : ℝ)*P 1+(-7299/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15897/2000 : ℝ) < (-194741393901647210960964496511251689/24537206978920000000000000000000000 : ℝ) := by norm_num
    linear_combination (2437/1600000000 : ℝ)*(base5) + (50671/1000000000000 : ℝ)*(base8) + (71363/1000000000000 : ℝ)*(base11) + (8699/100000000000 : ℝ)*(base34) + (10709/62500000000 : ℝ)*(base40) + (173054517087/1000000000000 : ℝ)*(base49) + (181919659929/1000000000000 : ℝ)*(base59) + (542503239243/1000000000000 : ℝ)*(base60) + (182474991301/100000000000 : ℝ)*(major_s1_0) + (7299/4000 : ℝ)*(major_s1_1) + (7299/4000 : ℝ)*(major_s1_2) + (1322762466283/500000000000 : ℝ)*(sp_s1_0) + (264552514159/100000000000 : ℝ)*(sp_s1_1) + (529105332943/200000000000 : ℝ)*(sp_s1_2) + (199999677977/200000000000 : ℝ)*(sp_s1_6) + (264552514159/100000000000 : ℝ)*(f.sum) + (153613907399261861/693219770000000000000000000000 : ℝ)*base63 + (2559665056213/4945000000000000000000000 : ℝ)*base65 + (160267314063449/700930000000000000000000000 : ℝ)*base66 + (1172753523143/1978000000000000000000000 : ℝ)*base69 + (26408225420268891/140026576000000000000000000000 : ℝ)*base70 + (32764234005059/44245000000000000000000000 : ℝ)*base73 + (61571616520373/140186000000000000000000000 : ℝ)*base75 + (12925701913891/28316800000000000000000000 : ℝ)*base76 + (554994452557921409/6202529570000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p018_b026 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 56)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=51 ∨ c=52 ∨ c=53 ∨ c=54 ∨ c=55 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl
  · exact collision_c318051 p hpa (by linarith only [hpb]) X hX
  · exact collision_c318052 p hpa (by linarith only [hpb]) X hX
  · exact collision_c318053 p hpa (by linarith only [hpb]) X hX
  · exact collision_c318054 p hpa (by linarith only [hpb]) X hX
  · exact collision_c318055 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 56)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p018_b026 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
