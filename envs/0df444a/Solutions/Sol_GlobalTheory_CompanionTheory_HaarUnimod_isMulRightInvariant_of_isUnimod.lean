-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:49:41.01325+00:00
-- url     : https://prove2.me/submissions/67c3ca4a-6a78-4309-bc5f-a2ae5103a281

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariant
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarUnimod_modularCharacterFun_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarUnimod
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
namespace GlobalTheory.CompanionTheory.HaarUnimod
theorem _root_.solution :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G], IsUnimod G →
      ∀ (μ : Measure G) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro G _ _ _ _ _ _ _ hG μ _
  refine ⟨fun g => ?_⟩
  rw [isMulLeftInvariant_eq_smul (map (· * g) μ) μ,
    ← modularCharacterFun_eq_haarScalarFactor, modularCharacterFun_eq_one hG g, one_smul]
end GlobalTheory.CompanionTheory.HaarUnimod
