-- Prove2me | solution 1 for Malliavin.IsSmoothBounded.comp_continuousLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:47:51.127353+00:00
-- url     : https://prove2.me/submissions/39e713d9-8ca6-436d-8719-fa7af43bc89d

import Definitions.Def_Malliavin_NaturalClarkOcone
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_PastCylinderDensity

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E F W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
namespace Malliavin
namespace IsSmoothBounded
theorem _root_.solution
    {f : F → ℝ} (hf : IsSmoothBounded f) (L : E →L[ℝ] F) :
    IsSmoothBounded (f ∘ L) where
  contDiff := hf.contDiff.comp L.contDiff
  bounded := hf.bounded.imp fun C hC x ↦ hC (L x)
  bounded_fderiv := by
    obtain ⟨C, hC⟩ := hf.bounded_fderiv
    refine ⟨C * ‖L‖, fun x ↦ ?_⟩
    rw [fderiv_comp x (hf.differentiable (L x)) L.differentiableAt, L.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hC (L x)) (ContinuousLinearMap.opNorm_nonneg L))
end IsSmoothBounded
end Malliavin
