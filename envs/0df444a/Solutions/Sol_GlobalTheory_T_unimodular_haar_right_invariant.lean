-- Prove2me | solution 1 for GlobalTheory.T.unimodular_haar_right_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:05:16.925117+00:00
-- url     : https://prove2.me/submissions/992e0505-c472-420c-a274-2af96fb57af9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariant
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariantStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarUnimod_isMulRightInvariant_of_isUnimod


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
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G], IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod | exact GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod | (intros; apply GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod <;> assumption)
end _root_.GlobalTheory.T
