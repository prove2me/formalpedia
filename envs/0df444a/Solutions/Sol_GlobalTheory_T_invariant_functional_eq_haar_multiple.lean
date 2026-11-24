-- Prove2me | solution 1 for GlobalTheory.T.invariant_functional_eq_haar_multiple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:14:28.67435+00:00
-- url     : https://prove2.me/submissions/bc23c5f7-f79f-41c5-9de1-ff6600a1d290

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultipleStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_exists_eq_mul_integral


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
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G], IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure] (L : SB G →ₗ[ℂ] ℂ), (∀ (g : G) (α : SB G), L (pullHomeo (Homeomorph.mulRight g) α) = L α) → ∃ c : ℂ, ∀ α : SB G, L α = c * ∫ x, (α : G → ℂ) x ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.FrobHaarR.exists_eq_mul_integral | exact GlobalTheory.CompanionTheory.FrobHaarR.exists_eq_mul_integral | (intros; apply GlobalTheory.CompanionTheory.FrobHaarR.exists_eq_mul_integral <;> assumption)
end _root_.GlobalTheory.T
