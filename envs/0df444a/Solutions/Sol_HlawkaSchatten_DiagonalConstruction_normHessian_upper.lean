-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.normHessian_upper
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T23:38:19.654903+00:00
-- url     : https://prove2.me/submissions/a4ba5351-d8f6-4c7f-800e-60b0168a5d2f

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_HessianBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_lpNorm_eq_zero_iff
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

/-! # Uniform lower and upper bounds for the norm Hessian -/

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

theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]







theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

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

theorem powerResidual_min {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    powerResidual p v h (radialCoefficient p v h) ≤ powerResidual p v h a := by
  have hS := powerSum_pos (by linarith : 0 < p) hv
  rw [powerResidual_radial hp v h hv, powerResidual_eq hp]
  have hn := mul_nonneg hS.le (sq_nonneg (a - powerPair p v h / powerSum p v))
  have hmul : powerSum p v * (powerPair p v h / powerSum p v) = powerPair p v h :=
    mul_div_cancel₀ _ hS.ne'
  have hmul2 : powerSum p v * (powerPair p v h / powerSum p v) ^ 2 =
      powerPair p v h ^ 2 / powerSum p v := by field_simp
  nlinarith [congrArg (fun x : ℝ ↦ a * x) hmul]





theorem normHessian_le_residual {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v h ≤ (p - 1) * powerSum p v ^ (1 / p - 1) * powerResidual p v h a := by
  exact mul_le_mul_of_nonneg_left (powerResidual_min hp v h hv a)
    (mul_nonneg (by linarith) (Real.rpow_nonneg (powerSum_nonneg p v) _))















theorem powerSum_root_pred {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v ^ (1 / p - 1) = (lpNorm p v ^ (p - 1))⁻¹ := by
  rw [powerSum_eq_lpNorm_rpow hp, ← Real.rpow_mul (lpNorm_nonneg p v),
    show p * (1 / p - 1) = -(p - 1) by field_simp; ring,
    Real.rpow_neg (lpNorm_nonneg p v)]



end HlawkaSchatten.DiagonalConstruction

private theorem erased_residual_sq_le (v h : Fin 3 → ℝ) (k : Fin 3)
    (hk : 81 / 50 ≤ |v k|) (hi : ∀ i, i ≠ k → |v i| ≤ 19 / 50) :
    (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) ≤ 2 * euclideanSq h := by
  have hkv : 0 < |v k| := by linarith
  have hr (i : Fin 3) (hik : i ≠ k) : |v i / v k| ≤ 19 / 81 := by
    rw [abs_div, div_le_iff₀ hkv]
    linarith [hi i hik]
  have hsq (i : Fin 3) (hik : i ≠ k) : (v i / v k) ^ 2 ≤ (19 / 81 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hr i hik)
  have hterm (i : Fin 3) (hik : i ≠ k) : (h i - h k / v k * v i) ^ 2 ≤
      2 * (h i) ^ 2 + 2 * (h k) ^ 2 * (19 / 81 : ℝ) ^ 2 := by
    have hyoung := sq_nonneg (h i + h k * (v i / v k))
    have hm := mul_le_mul_of_nonneg_left (hsq i hik) (sq_nonneg (h k))
    have he : h k / v k * v i = h k * (v i / v k) := by ring
    rw [he]
    nlinarith
  have hh := Finset.sum_le_sum (s := Finset.univ.erase k)
    (fun i hi ↦ hterm i (Finset.mem_erase.mp hi).1)
  have hsum : (∑ i ∈ Finset.univ.erase k, (h i) ^ 2) + (h k) ^ 2 = euclideanSq h := by
    exact Finset.sum_erase_add _ _ (Finset.mem_univ k)
  norm_num only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hh
  nlinarith [sq_nonneg (h k)]

theorem solution {p : ℝ} (hp : 2 < p) (v h : Fin 3 → ℝ) (k : Fin 3)
    (hk : 81 / 50 ≤ |v k|) (hi : ∀ i, i ≠ k → |v i| ≤ 19 / 50) :
    normHessian p v h ≤ upperHessianCoefficient p * euclideanSq h := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hkv : v k ≠ 0 := by intro he; norm_num [he] at hk
  have hv : v ≠ 0 := by intro he; apply hkv; simp [he]
  have hN := lpNorm_pos hp0 hv
  have hlarge : 81 / 50 ≤ lpNorm p v := hk.trans (norm_apply_le_lpNorm hp1 v k)
  have hden : (81 / 50 : ℝ) ^ (p - 1) ≤ lpNorm p v ^ (p - 1) :=
    Real.rpow_le_rpow (by norm_num) hlarge (by linarith)
  have hres : powerResidual p v h (h k / v k) ≤
      (19 / 50 : ℝ) ^ (p - 2) * (2 * euclideanSq h) := by
    have hz : |v k| ^ (p - 2) * (h k - h k / v k * v k) ^ 2 = 0 := by
      simp [div_mul_cancel₀ _ hkv]
    have he : powerResidual p v h (h k / v k) =
        ∑ i ∈ Finset.univ.erase k, |v i| ^ (p - 2) * (h i - h k / v k * v i) ^ 2 := by
      rw [powerResidual, ← Finset.sum_erase_add _ _ (Finset.mem_univ k), hz, add_zero]
    rw [he]
    calc
      _ ≤ ∑ i ∈ Finset.univ.erase k, (19 / 50 : ℝ) ^ (p - 2) *
          (h i - h k / v k * v i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi'
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (abs_nonneg _) (hi i (Finset.mem_erase.mp hi').1) (by linarith))
          (sq_nonneg _)
      _ = (19 / 50 : ℝ) ^ (p - 2) *
          (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (erased_residual_sq_le v h k hk hi) (by positivity)
  have hcoef : (p - 1) / lpNorm p v ^ (p - 1) ≤ (p - 1) / (81 / 50 : ℝ) ^ (p - 1) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) hden
  have hmin := normHessian_le_residual hp v h hv (h k / v k)
  rw [powerSum_root_pred hp0] at hmin
  change normHessian p v h ≤
    (p - 1) / lpNorm p v ^ (p - 1) * powerResidual p v h (h k / v k) at hmin
  calc
    _ ≤ _ := hmin
    _ ≤ ((p - 1) / lpNorm p v ^ (p - 1)) * ((19 / 50 : ℝ) ^ (p - 2) * (2 * euclideanSq h)) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    _ ≤ ((p - 1) / (81 / 50 : ℝ) ^ (p - 1)) * ((19 / 50 : ℝ) ^ (p - 2) * (2 * euclideanSq h)) :=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by positivity)
        (mul_nonneg (by norm_num) (euclideanSq_nonneg h)))
    _ = _ := by unfold upperHessianCoefficient; ring
