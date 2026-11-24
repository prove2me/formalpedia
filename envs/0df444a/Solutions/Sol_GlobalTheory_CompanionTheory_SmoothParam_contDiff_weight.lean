-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothParam.contDiff_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:00:45.12603+00:00
-- url     : https://prove2.me/submissions/a40d9ecf-2fe3-4789-bc45-376b74f351a6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContDiffIntegralDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_contDiff_weight_nat

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
namespace GlobalTheory.CompanionTheory.SmoothParam
theorem _root_.solution {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) [CompleteSpace F] {H : P × Y → F} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun p => ∫ x, u x • H (p, ψ x) ∂ν) :=
  contDiff_infty.2 fun n => contDiff_weight_nat hu hψ hK hψK n F H hH
end GlobalTheory.CompanionTheory.SmoothParam
