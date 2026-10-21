-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.coefficient_determinant_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T07:38:53.185923+00:00
-- url     : https://prove2.me/submissions/2f0fcfa6-cca9-4637-bb5b-f3da8faf2287

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analytic_collision_factor_bound
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_periodModel_coeff_eq_rowTest
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_norm_le
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (transverse : κ → Fin m → ℕ)
    (j ell h : ι → ℕ) (a : ι → Fin m → ℕ) (w : Fin m → ℝ)
    {K : ℕ} {H w0 wstar : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hj : ∀ r, j r < K)
    (hcol : ∀ c, w0 * (h c : ℝ) + ∑ i, w i * (a c i : ℝ) ≤ H) :
    ‖Matrix.det (fun r c => PowerSeries.coeff (ell r)
      ((periodModel (j r) (h c) (a c)).coeff
        (InterpolationMatrix.exponentVector (transverse (group r)))))‖ ≤
      (((Fintype.card ι).factorial : ℝ) *
        (Real.exp (H * (100 * (K : ℝ) / w0 +
          Real.log (200 * (K : ℝ)) / wstar))) ^ Fintype.card ι *
        (2 : ℝ) ^ (∑ r, ell r)) *
      (Real.exp (-Real.log 2 / 2)) ^
        (∑ b : κ, (((Finset.univ : Finset ι).filter (fun r => group r = b)).card).choose 2) *
      ((1 - Real.exp (-Real.log 2 / 2))⁻¹) ^ Fintype.card ι := by
  let R : NNReal := ⟨100 * (K : ℝ), by positivity⟩
  have hR : 0 < R := by
    change (0 : ℝ) < 100 * (K : ℝ)
    positivity
  have hK1 : (1 : ℝ) ≤ K := by
    exact_mod_cast (Nat.succ_le_iff.mpr hK)
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
    change (1 : ℝ) ≤ 100 * (K : ℝ)
    linarith
  have hs0 : 0 ≤ Real.exp (-Real.log 2 / 2) := (Real.exp_pos _).le
  have hs1 : Real.exp (-Real.log 2 / 2) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hss : Real.exp (-Real.log 2 / 2) * Real.exp (-Real.log 2 / 2) =
      (1 / 2 : ℝ) := by
    rw [← Real.exp_add]
    have heq : -Real.log 2 / 2 + -Real.log 2 / 2 = -Real.log 2 := by ring
    rw [heq, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hf : ∀ b c, Differentiable ℂ
      (analyticColumn (h c) (a c) (transverse b)) := by
    intro b c
    unfold analyticColumn
    exact ((Complex.differentiable_exp.comp
      (differentiable_id.const_mul (h c : ℂ))).const_mul _).mul
        (differentiable_id.pow _)
  have hbound : ∀ b c z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) →
      ‖analyticColumn (h c) (a c) (transverse b) z‖ ≤
        Real.exp (H * ((R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar)) := by
    intro b c z hz
    have hzR : ‖z‖ = (R : ℝ) := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    exact analyticColumn_norm_le (h c) (a c) (transverse b) w
      hR1 hH.le hw0 hws hw (hcol c) hzR.le
  have hcenter : ∀ r : ι,
      ‖(j r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ + 3 / 4 ≤
        (R : ℝ) / 2 := by
    intro r
    have hjK : (j r : ℝ) ≤ K := by exact_mod_cast (hj r).le
    have hnorm : ‖(j r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ =
        (j r : ℝ) * (2 * Real.pi) := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hpi : 2 * Real.pi ≤ (8 : ℝ) := by linarith [Real.pi_lt_four]
    have hprod : (j r : ℝ) * (2 * Real.pi) ≤ (K : ℝ) * 8 :=
      mul_le_mul hjK hpi (by positivity) (by positivity)
    change ‖(j r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ + 3 / 4 ≤
      (100 * (K : ℝ)) / 2
    rw [hnorm]
    linarith
  have hb := analytic_collision_factor_bound group
    (fun b c => analyticColumn (h c) (a c) (transverse b))
    (fun r => (j r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) ell R hR
    (Real.exp (H * ((R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar)))
    (Real.exp (-Real.log 2 / 2)) (Real.exp_pos _).le hs0 hs1 hss hf hbound hcenter
  have hRv : (R : ℝ) = 100 * (K : ℝ) := rfl
  have he : 2 * (100 * (K : ℝ)) = 200 * (K : ℝ) := by ring
  rw [hRv, he] at hb
  simpa only [periodModel_coeff_eq_rowTest] using hb
