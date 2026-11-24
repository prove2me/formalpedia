-- Prove2me | solution 1 for GlobalTheory.T.partial_integral_mem_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:21:13.859805+00:00
-- url     : https://prove2.me/submissions/b37a1a7d-d07b-4b02-85a2-6ad694226cbc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhat
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhatStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TestFunctionFibreIntegral_integral_mem_SB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B] [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B] (μ : Measure B) [IsFiniteMeasureOnCompacts μ] (w : B → ℂ), Continuous w → ∀ F : SB (A × B), (fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) ∈ SB A := by
  first | exact @GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB | exact GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB | (intros; apply GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB <;> assumption)
end _root_.GlobalTheory.T
