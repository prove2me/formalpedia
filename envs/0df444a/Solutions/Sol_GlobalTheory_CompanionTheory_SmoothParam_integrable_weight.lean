-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothParam.integrable_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:58.56935+00:00
-- url     : https://prove2.me/submissions/edf490db-b1cb-4e3c-9b2f-879cfe88e6cd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContDiffIntegralDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothParam
variable {Ω P Y F : Type} [MeasurableSpace Ω] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
omit [FiniteDimensional ℝ P] [NormedSpace ℝ P] [FiniteDimensional ℝ Y] [NormedSpace ℝ Y]
namespace GlobalTheory.CompanionTheory.SmoothParam
theorem _root_.solution {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) {H : P × Y → F} (hH : Continuous H) (p : P) :
    Integrable (fun x => u x • H (p, ψ x)) ν := by
  obtain ⟨C, hC⟩ := (isCompact_singleton.prod hK).exists_bound_of_continuousOn
    (f := H) (s := {p} ×ˢ K) hH.continuousOn
  have hc : Continuous fun y => H (p, y) := hH.comp (by fun_prop)
  have meas : AEStronglyMeasurable (fun x => u x • H (p, ψ x)) ν :=
    hu.aestronglyMeasurable.smul (hc.comp_aestronglyMeasurable hψ)
  refine (hu.norm.mul_const C).mono' meas ?_
  filter_upwards [hψK] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hC _ ⟨rfl, hx⟩) (norm_nonneg _)
end GlobalTheory.CompanionTheory.SmoothParam
