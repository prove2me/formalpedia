-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.deficitHessian_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-29T00:09:48.657737+00:00
-- url     : https://prove2.me/submissions/4a94522a-b51f-49bc-91cb-71f6c4f21a3c

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_HessianBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_joint_radial_residual_bound
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_lpNorm_eq_zero_iff
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normHessian_lower
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normHessian_upper
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Nonnegative second variation on the entire cyclic box -/

open HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Coordinate norms for the diagonal construction

The explicit finite power sum keeps coordinate arguments independent of
the exponent-indexed `PiLp` type. Its norm laws are inherited from `PiLp`.
-/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]



theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _











theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]



theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))





























end HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Quadratic geometry of the cyclic box

The joint radial estimate uses the convenient bound `300`. This weaker
intermediate constant leaves the exponent cutoff unchanged.
-/

namespace HlawkaSchatten.DiagonalConstruction









theorem euclideanSq_nonneg (v : Fin 3 → ℝ) : 0 ≤ euclideanSq v :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i)

theorem frobeniusSq_nonneg (X : Triple) : 0 ≤ frobeniusSq X :=
  Finset.sum_nonneg fun j _ ↦ euclideanSq_nonneg (X j)









theorem euclideanSq_total_le (X : Triple) : euclideanSq (totalTriple X) ≤ 3 * frobeniusSq X := by
  have hi (i : Fin 3) : ((∑ j, X j i) ^ 2) ≤ 3 * ∑ j, (X j i) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 3 ↦ (1 : ℝ)) (fun j ↦ X j i)
  calc
    _ ≤ ∑ i, 3 * ∑ j, (X j i) ^ 2 := Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := by
      simp only [frobeniusSq, euclideanSq, ← Finset.mul_sum]
      rw [Finset.sum_comm]











end HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Coordinate ranges of the seven vectors on the cyclic box -/

namespace HlawkaSchatten.DiagonalConstruction



theorem totalTriple_eq (X : Triple) : totalTriple X = X 0 + X 1 + X 2 := by
  simp [totalTriple, Fin.sum_univ_three]

theorem entryBox_column_bounds {X : Triple} (hX : X ∈ entryBox) (j i : Fin 3) :
    81 / 100 ≤ |X j i| ∧ |X j i| ≤ 119 / 100 := by
  have h := abs_le.mp (hX j i)
  by_cases hij : i = j
  · simp only [cyclicCenter, if_pos hij] at h
    rw [abs_of_neg (by linarith : X j i < 0)]
    constructor <;> linarith
  · simp only [cyclicCenter, if_neg hij] at h
    rw [abs_of_pos (by linarith : 0 < X j i)]
    constructor <;> linarith

theorem entryBox_total_bounds {X : Triple} (hX : X ∈ entryBox) (i : Fin 3) :
    43 / 100 ≤ totalTriple X i ∧ totalTriple X i ≤ 157 / 100 := by
  have h0 := abs_le.mp (hX 0 i)
  have h1 := abs_le.mp (hX 1 i)
  have h2 := abs_le.mp (hX 2 i)
  rw [totalTriple_eq]
  simp only [Pi.add_apply]
  fin_cases i <;> norm_num [cyclicCenter, Fin.ext_iff] at h0 h1 h2 ⊢ <;>
    constructor <;> linarith!

theorem entryBox_pair_large {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    81 / 50 ≤ |pairTriple X j j| := by
  have h0 := abs_le.mp (hX 0 j)
  have h1 := abs_le.mp (hX 1 j)
  have h2 := abs_le.mp (hX 2 j)
  have hl : 81 / 50 ≤ pairTriple X j j := by
    fin_cases j <;> norm_num [pairTriple, cyclicCenter, Fin.ext_iff] at h0 h1 h2 ⊢ <;>
      linarith!
  exact hl.trans (le_abs_self _)

theorem entryBox_pair_small {X : Triple} (hX : X ∈ entryBox) (j i : Fin 3) (hij : i ≠ j) :
    |pairTriple X j i| ≤ 19 / 50 := by
  have h0 := abs_le.mp (hX 0 i)
  have h1 := abs_le.mp (hX 1 i)
  have h2 := abs_le.mp (hX 2 i)
  fin_cases j <;> fin_cases i <;> first
  | exact (hij rfl).elim
  | norm_num [pairTriple, cyclicCenter, Fin.ext_iff, abs_le] at h0 h1 h2 ⊢
    constructor <;> linarith!





theorem entryBox_pair_ne_zero {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    pairTriple X j ≠ 0 := by
  intro he
  have h := entryBox_pair_large hX j
  norm_num [he] at h

theorem euclideanSq_pairs_le (X : Triple) :
    (∑ j, euclideanSq (pairTriple X j)) ≤ 4 * frobeniusSq X := by
  have he : (∑ j, euclideanSq (pairTriple X j)) = frobeniusSq X + euclideanSq (totalTriple X) := by
    rw [totalTriple_eq]
    simp only [pairTriple, frobeniusSq, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp only [euclideanSq, Pi.add_apply, Fin.sum_univ_three]
    ring
  rw [he]
  linarith [euclideanSq_total_le X]

end HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Uniform lower and upper bounds for the norm Hessian -/

namespace HlawkaSchatten.DiagonalConstruction





theorem lowerHessianCoefficient_pos {p : ℝ} (hp : 1 < p) : 0 < lowerHessianCoefficient p := by
  unfold lowerHessianCoefficient
  positivity

theorem upperHessianCoefficient_pos {p : ℝ} (hp : 1 < p) : 0 < upperHessianCoefficient p := by
  unfold upperHessianCoefficient
  positivity









end HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Uniform scalar comparison of the Hessian coefficients -/

namespace HlawkaSchatten.DiagonalConstruction

theorem hessianCoefficient_ratio (p : ℝ) :
    upperHessianCoefficient p = lowerHessianCoefficient p * (157 / 27) *
      (2983 / 3483 : ℝ) ^ (p - 2) := by
  have hM : (157 / 100 : ℝ) ^ (p - 1) = (157 / 100 : ℝ) ^ (p - 2) * (157 / 100) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (81 / 50 : ℝ) ^ (p - 1) = (81 / 50 : ℝ) ^ (p - 2) * (81 / 50) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (2983 / 3483 : ℝ) ^ (p - 2) =
      ((19 / 50 : ℝ) ^ (p - 2) * (157 / 100 : ℝ) ^ (p - 2)) /
        ((81 / 50 : ℝ) ^ (p - 2) * (43 / 100 : ℝ) ^ (p - 2)) := by
    rw [show (2983 / 3483 : ℝ) = ((19 / 50) * (157 / 100)) / ((81 / 50) * (43 / 100)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num)]
  rw [upperHessianCoefficient, lowerHessianCoefficient, hM, hL, hbase]
  field_simp
  ring

theorem upperHessianCoefficient_lt {p : ℝ} (hp : 2 < p) :
    upperHessianCoefficient p < 8 * lowerHessianCoefficient p * (6 / 7 : ℝ) ^ (p - 2) := by
  have hb := lowerHessianCoefficient_pos (show 1 < p by linarith)
  have hr := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6 / 7) (p - 2)
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2983 / 3483)
    (by norm_num : (2983 / 3483 : ℝ) ≤ 6 / 7) (show 0 ≤ p - 2 by linarith)
  have hm := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ lowerHessianCoefficient p * (157 / 27) by positivity)
  rw [hessianCoefficient_ratio]
  nlinarith [mul_pos hb hr]

theorem exponential_curvature_margin {p : ℝ} (hp : 256 ≤ p) :
    9600 * p * (6 / 7 : ℝ) ^ (p - 2) < 1 := by
  have hp0 : 0 < p := by linarith
  have hbase : (9600 * 256 : ℝ) < (7 / 6 : ℝ) ^ (254 : ℕ) := by norm_num
  have hlog : (1 / 7 : ℝ) ≤ Real.log (7 / 6) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 7 / 6 by norm_num)
    norm_num at h
    exact h
  have hgrowth : p / 256 ≤ (7 / 6 : ℝ) ^ (p - 256) := by
    have h := Real.add_one_le_exp (Real.log (7 / 6) * (p - 256))
    have hm := mul_le_mul_of_nonneg_right hlog (show 0 ≤ p - 256 by linarith)
    rw [Real.rpow_def_of_pos (by norm_num)]
    linarith
  have hr : 0 < (7 / 6 : ℝ) ^ (p - 256) := by positivity
  have hprod := mul_lt_mul_of_pos_right hbase hr
  have he : (7 / 6 : ℝ) ^ (254 : ℕ) * (7 / 6 : ℝ) ^ (p - 256) =
      (7 / 6 : ℝ) ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    norm_num
    ring
  rw [he] at hprod
  have hlarge : 9600 * p < (7 / 6 : ℝ) ^ (p - 2) := by linarith
  have hinv : (6 / 7 : ℝ) ^ (p - 2) = ((7 / 6 : ℝ) ^ (p - 2))⁻¹ := by
    rw [show (6 / 7 : ℝ) = (7 / 6 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num)]
  rw [hinv, ← div_eq_mul_inv, div_lt_one (by positivity)]
  exact hlarge

/-- This comparison includes the geometric constant `300` and pair-sum factor `4`. -/
theorem hessian_curvature_margin {p : ℝ} (hp : 256 ≤ p) :
    1200 * p * upperHessianCoefficient p < lowerHessianCoefficient p := by
  have hb := lowerHessianCoefficient_pos (show 1 < p by linarith)
  have hU := upperHessianCoefficient_lt (show 2 < p by linarith)
  have hsmall := exponential_curvature_margin hp
  have hm := mul_lt_mul_of_pos_left hU (show 0 < 1200 * p by linarith)
  have hbsmall := mul_lt_mul_of_pos_left hsmall hb
  nlinarith

end HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Directional second derivatives of the finite real coordinate norm -/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]















theorem powerSum_nonneg (p : ℝ) (v : ι → ℝ) : 0 ≤ powerSum p v :=
  Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p

theorem powerSum_eq_lpNorm_rpow {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v = lpNorm p v ^ p := by
  rw [lpNorm_rpow hp]
  rfl

theorem powerSum_pos {p : ℝ} (hp : 0 < p) {v : ι → ℝ} (hv : v ≠ 0) : 0 < powerSum p v := by
  rw [powerSum_eq_lpNorm_rpow hp]
  exact Real.rpow_pos_of_pos (lpNorm_pos hp hv) p

omit [Fintype ι] in
private theorem abs_rpow_mul_sq {q : ℝ} (hq : 0 < q) (x : ℝ) :
    |x| ^ q * x ^ 2 = |x| ^ (q + 2) := by
  by_cases hx : x = 0
  · simp [hx, hq.ne', show q + 2 ≠ 0 by linarith]
  · rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_add (abs_pos.mpr hx)]

theorem powerQuad_self {p : ℝ} (hp : 2 < p) (v : ι → ℝ) :
    powerQuad p v v = powerSum p v := by
  unfold powerQuad powerSum
  apply Finset.sum_congr rfl
  intro i _
  simpa only [sub_add_cancel] using abs_rpow_mul_sq (by linarith : 0 < p - 2) (v i)

theorem powerResidual_eq {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerResidual p v h a = powerQuad p v h - 2 * a * powerPair p v h + a ^ 2 * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerResidual, powerQuad, powerPair, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem powerResidual_radial {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) :
    powerResidual p v h (radialCoefficient p v h) =
      powerQuad p v h - powerPair p v h ^ 2 / powerSum p v := by
  rw [powerResidual_eq hp, radialCoefficient]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring



theorem powerResidual_nonneg (p : ℝ) (v h : ι → ℝ) (a : ℝ) : 0 ≤ powerResidual p v h a :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (Real.rpow_nonneg (abs_nonneg (v i)) (p - 2)) (sq_nonneg (h i - a * v i))

theorem normHessian_nonneg {p : ℝ} (hp : 1 ≤ p) (v h : ι → ℝ) : 0 ≤ normHessian p v h :=
  mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) (Real.rpow_nonneg (powerSum_nonneg p v) _))
    (powerResidual_nonneg p v h _)













theorem powerPair_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerPair p v (h - a • v) = powerPair p v h - a * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerPair, powerQuad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem normHessian_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v (h - a • v) = normHessian p v h := by
  simp only [normHessian, powerResidual_radial hp v _ hv, powerPair_sub_smul hp]
  congr 1
  have hquad : powerQuad p v (h - a • v) = powerResidual p v h a := rfl
  rw [hquad, powerResidual_eq hp]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring





end HlawkaSchatten.DiagonalConstruction

theorem pairTriple_sub_smul (X Z : Triple) (a : ℝ) :
    pairTriple (Z - a • X) = pairTriple Z - a • pairTriple X := by
  ext j i
  fin_cases j <;> simp [pairTriple] <;> ring

theorem pair_hessian_sum_upper {p : ℝ} (hp : 2 < p) {X : Triple} (hX : X ∈ entryBox)
    (Z : Triple) (a : ℝ) :
    (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
      4 * upperHessianCoefficient p * frobeniusSq (Z - a • X) := by
  have hi (j : Fin 3) : normHessian p (pairTriple X j) (pairTriple Z j) ≤
      upperHessianCoefficient p * euclideanSq (pairTriple (Z - a • X) j) := by
    rw [pairTriple_sub_smul]
    change normHessian p (pairTriple X j) (pairTriple Z j) ≤
      upperHessianCoefficient p * euclideanSq (pairTriple Z j - a • pairTriple X j)
    rw [← normHessian_sub_smul hp _ _ (entryBox_pair_ne_zero hX j) a]
    exact normHessian_upper hp _ _ j (entryBox_pair_large hX j) (entryBox_pair_small hX j)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hi j)
  rw [← Finset.mul_sum] at hh
  have hm := mul_le_mul_of_nonneg_left (euclideanSq_pairs_le (Z - a • X))
    (upperHessianCoefficient_pos (by linarith : 1 < p)).le
  nlinarith

theorem solution {p K : ℝ} (hp : 256 ≤ p) (hK : 1 ≤ K) (hKp : K ≤ p)
    {X : Triple} (hX : X ∈ entryBox) (Z : Triple) : 0 ≤ deficitHessian p K X Z := by
  have hp1 : 1 < p := by linarith
  have hp2 : 2 < p := by linarith
  let a : Fin 3 → ℝ := fun j ↦ radialCoefficient p (X j) (Z j)
  let b := radialCoefficient p (totalTriple X) (totalTriple Z)
  let U : Triple := fun j ↦ Z j - a j • X j
  let D := totalTriple Z - b • totalTriple X
  have hcol (j : Fin 3) : lowerHessianCoefficient p * euclideanSq (U j) ≤
      normHessian p (X j) (Z j) := by
    exact normHessian_lower hp2 _ _
      (fun i ↦ by linarith [(entryBox_column_bounds hX j i).1])
      (fun i ↦ by linarith [(entryBox_column_bounds hX j i).2])
  have hcols : lowerHessianCoefficient p * frobeniusSq U ≤
      ∑ j, normHessian p (X j) (Z j) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcol j)
    rwa [← Finset.mul_sum] at hh
  have htotal : lowerHessianCoefficient p * euclideanSq D ≤
      normHessian p (totalTriple X) (totalTriple Z) := by
    apply normHessian_lower hp2
    · intro i
      have hi := entryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.1
    · intro i
      have hi := entryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.2
  have hcols0 : 0 ≤ ∑ j, normHessian p (X j) (Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hpositive : lowerHessianCoefficient p * (frobeniusSq U + euclideanSq D) ≤
      (2 * K - 1) * (∑ j, normHessian p (X j) (Z j)) +
        normHessian p (totalTriple X) (totalTriple Z) := by
    have hm := mul_nonneg (by linarith : 0 ≤ 2 * K - 2) hcols0
    nlinarith
  have hgeom : frobeniusSq (Z - b • X) ≤ 300 * (frobeniusSq U + euclideanSq D) :=
    joint_radial_residual_bound hX Z a b
  have hpairs := pair_hessian_sum_upper hp2 hX Z b
  have hpair0 : 0 ≤ ∑ j, normHessian p (pairTriple X j) (pairTriple Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hd := (upperHessianCoefficient_pos hp1).le
  have hneg1 := mul_le_mul_of_nonneg_left hpairs (show 0 ≤ p by linarith)
  have hneg2 := mul_le_mul_of_nonneg_left hgeom
    (show 0 ≤ 4 * p * upperHessianCoefficient p by positivity)
  have hneg3 := mul_le_mul_of_nonneg_right hKp hpair0
  have hcurv := mul_le_mul_of_nonneg_right (hessian_curvature_margin hp).le
    (add_nonneg (frobeniusSq_nonneg U) (euclideanSq_nonneg D))
  dsimp only [deficitHessian]
  nlinarith
