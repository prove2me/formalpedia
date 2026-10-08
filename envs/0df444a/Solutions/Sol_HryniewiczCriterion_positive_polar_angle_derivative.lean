-- Prove2me | solution 1 for HryniewiczCriterion.positive_polar_angle_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T21:01:57.142989+00:00
-- url     : https://prove2.me/submissions/3536c5a6-f2ea-4ef2-b550-489db1f7f7fe

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

open HryniewiczCriterion Filter Topology
set_option maxHeartbeats 800000

theorem solution
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det = 1)
    (θ : ℝ → ℝ) (hθ : Continuous θ)
    (hp : ∀ u, ∃ r : ℝ, 0 < r ∧
      A.mulVec (rotationVector u) = r • rotationVector (θ u))
    (s r : ℝ) (hr : 0 < r)
    (hs : A.mulVec (rotationVector s) = r • rotationVector (θ s)) :
    HasDerivAt θ (1 / r^2) s := by
  let x : ℝ → ℝ := fun u => A 0 0 * Real.cos u + A 0 1 * Real.sin u
  let y : ℝ → ℝ := fun u => A 1 0 * Real.cos u + A 1 1 * Real.sin u
  let X : ℝ → ℝ := fun u => Real.cos (θ s) * x u + Real.sin (θ s) * y u
  let Y : ℝ → ℝ := fun u => Real.cos (θ s) * y u - Real.sin (θ s) * x u
  let xp := A 0 0 * (-Real.sin s) + A 0 1 * Real.cos s
  let yp := A 1 0 * (-Real.sin s) + A 1 1 * Real.cos s
  let Xp := Real.cos (θ s) * xp + Real.sin (θ s) * yp
  let Yp := Real.cos (θ s) * yp - Real.sin (θ s) * xp
  have hx : HasDerivAt x xp s :=
    ((Real.hasDerivAt_cos s).const_mul _).add ((Real.hasDerivAt_sin s).const_mul _)
  have hy : HasDerivAt y yp s :=
    ((Real.hasDerivAt_cos s).const_mul _).add ((Real.hasDerivAt_sin s).const_mul _)
  have hX : HasDerivAt X Xp s := (hx.const_mul _).add (hy.const_mul _)
  have hY : HasDerivAt Y Yp s := (hy.const_mul _).sub (hx.const_mul _)
  have hpol (u : ℝ) : ∃ a : ℝ, 0 < a ∧
      X u = a * Real.cos (θ u - θ s) ∧ Y u = a * Real.sin (θ u - θ s) := by
    obtain ⟨a, ha, hv⟩ := hp u
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    simp only [rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    refine ⟨a, ha, ?_, ?_⟩ <;> dsimp [X, Y, x, y] <;>
      rw [h0, h1] <;> simp only [Real.cos_sub, Real.sin_sub] <;> ring
  have h0 := congrFun hs 0
  have h1 := congrFun hs 1
  simp only [rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hXs : X s = r := by
    dsimp [X, x, y]
    rw [h0, h1]
    nlinarith [Real.cos_sq_add_sin_sq (θ s)]
  have hYs : Y s = 0 := by dsimp [Y, x, y]; rw [h0, h1]; ring
  have harea : X s * Yp - Y s * Xp = 1 := by
    have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using hA
    calc
      X s * Yp - Y s * Xp =
          (Real.cos (θ s)^2 + Real.sin (θ s)^2) *
          (A 0 0 * A 1 1 - A 0 1 * A 1 0) *
          (Real.cos s^2 + Real.sin s^2) := by dsimp [X, Y, Xp, Yp, xp, yp, x, y]; ring
      _ = 1 := by rw [Real.cos_sq_add_sin_sq, Real.cos_sq_add_sin_sq, hdet]; norm_num
  have hratio : HasDerivAt (fun u => Y u / X u)
      ((Yp * X s - Y s * Xp) / (X s)^2) s :=
    hY.div hX (by rw [hXs]; exact ne_of_gt hr)
  have hg : HasDerivAt (fun u => θ u - θ s) (1 / r^2) s := by
    have ht : HasDerivAt Real.tan 1 (θ s - θ s) := by
      simpa using (Real.hasDerivAt_tan (x := (0 : ℝ)) (by simp))
    have he : (Real.tan ∘ (fun u => θ u - θ s)) =ᶠ[𝓝 s] (fun u => Y u / X u) := by
      filter_upwards [] with u
      obtain ⟨a, ha, hXu, hYu⟩ := hpol u
      simp only [Function.comp_apply, Real.tan_eq_sin_div_cos, hXu, hYu]
      exact (mul_div_mul_left _ _ (ne_of_gt ha)).symm
    have hd := ht.of_comp_left (hθ.continuousAt.sub continuousAt_const)
      hratio (by norm_num) he
    convert! hd using 1
    rw [div_one, hXs, hYs, zero_mul, sub_zero]
    have hmul : Yp * r = 1 := by rw [hXs, hYs] at harea; nlinarith [harea]
    rw [hmul]
  convert! hg.add_const (θ s) using 1; simp


