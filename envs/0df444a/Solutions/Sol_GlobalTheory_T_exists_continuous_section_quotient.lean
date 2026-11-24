-- Prove2me | solution 1 for GlobalTheory.T.exists_continuous_section_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:06:33.892257+00:00
-- url     : https://prove2.me/submissions/27f6743b-4f13-4d8b-be8b-3224acd61dc0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotient
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotientStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_LGroupSection_exists_continuous_section


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
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G] (H : Subgroup G), IsClosed (H : Set G) → ∃ s : G ⧸ H → G, Continuous s ∧ ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c := by
  first | exact @GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section | exact GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section | (intros; apply GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section <;> assumption)
end _root_.GlobalTheory.T
