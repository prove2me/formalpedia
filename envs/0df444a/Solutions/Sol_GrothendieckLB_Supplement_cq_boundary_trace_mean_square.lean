-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_boundary_trace_mean_square
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T19:30:57.339796+00:00
-- url     : https://prove2.me/submissions/8afcc919-0b25-4d40-b576-b5e5787f5d67

import Theorems.Thm_GrothendieckLB_Supplement_diagonal_hermite_sobolev_bound
import Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_gaussian_bessel
import Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_energy_reflection
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory ProbabilityTheory GrothendieckLB.Supplement
open CQBoundary

set_option maxHeartbeats 1400000

private theorem point_bound (θ : ℝ) : ‖CQBoundary.trace θ‖^2 ≤ Real.pi^2/6*energy θ := by
  obtain ⟨huv,h0,hp⟩ := cq_boundary_gaussian_bessel θ
  have hz : ‖-unitPoint θ‖≤1 := by simp [unitPoint,Complex.norm_exp]
  let d (n : ℕ) : ℂ := ∫ x : ℝ, ∫ y : ℝ, phiThree (unitPoint θ) x y *
    ↑(QuadSDE.hermiteN n x * QuadSDE.hermiteN n y) ∂gaussianReal 0 1 ∂gaussianReal 0 1
  obtain ⟨_,hs⟩ := diagonal_hermite_sobolev_bound d _ hz _ _ h0 hp
  rw [huv] at hs
  have hE : 0≤energy θ := integral_nonneg fun x => integral_nonneg fun y => add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _))
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ hE
  nlinarith only [Real.pi_gt_three, sq_nonneg (Real.pi-3)]

theorem solution :
    (2*Real.pi)⁻¹ * (∫ θ in (0:ℝ)..2*Real.pi, ‖CQBoundary.trace θ‖^2) ≤
      Real.pi^2 / 6 * (Real.pi⁻¹ * ∫ θ in (0:ℝ)..Real.pi, energy θ) := by
  obtain ⟨hint,he⟩ := cq_boundary_energy_reflection
  have hpos : (0:ℝ)≤2*Real.pi := by positivity
  have h : (∫ θ in (0:ℝ)..2*Real.pi, ‖CQBoundary.trace θ‖^2) ≤
      ∫ θ in (0:ℝ)..2*Real.pi, Real.pi^2/6 * energy θ := by
    simp only [intervalIntegral.integral_of_le hpos]
    exact integral_mono_of_nonneg (ae_of_all _ fun θ => sq_nonneg _)
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le hpos).mp hint).const_mul _)
      (ae_of_all _ point_bound)
  rw [intervalIntegral.integral_const_mul,he] at h
  calc
    _ ≤ (2*Real.pi)⁻¹ * (Real.pi^2/6*(2*∫ θ in (0:ℝ)..Real.pi, energy θ)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring
