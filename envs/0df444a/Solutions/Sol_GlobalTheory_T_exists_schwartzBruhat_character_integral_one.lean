-- Prove2me | solution 1 for GlobalTheory.T.exists_schwartzBruhat_character_integral_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:05:14.71641+00:00
-- url     : https://prove2.me/submissions/50d189f1-390b-4a07-8fb9-a1d886f5dd30

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzBruhatCharacterIntegralOne
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzBruhatCharacterIntegralOneStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobNz_exists_SB_integral_mul_char_eq_one


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
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (χ : G →* ℂˣ), Continuous (fun g => (χ g : ℂ)) → ∃ α : SB G, ∫ x, (α : G → ℂ) x * (χ x : ℂ) ∂μ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one | exact GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one | (intros; apply GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one <;> assumption)
end _root_.GlobalTheory.T
