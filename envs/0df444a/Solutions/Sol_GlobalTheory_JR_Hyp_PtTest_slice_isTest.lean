-- Prove2me | solution 1 for GlobalTheory.JR.Hyp.PtTest.slice_isTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:56.061141+00:00
-- url     : https://prove2.me/submissions/b4aa3541-c4d9-44fd-bbc8-b08767d90534

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierPsiKPreservesTestFunctions
import Theorems.Thm_GlobalTheory_JR_Hyp_PtTest_hasCompactSupport_of_loc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp GlobalTheory.JR.Hyp.PtTest
namespace GlobalTheory.JR.Hyp.PtTest
theorem _root_.solution {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Φ : X × Y → ℂ) (hΦ : IsTest Φ)
    (a : X) : IsTest fun b => Φ (a, b) := by
  have hl : IsLocallyConstant fun b => Φ (a, b) :=
    hΦ.1.comp_continuous (continuous_const.prodMk continuous_id)
  refine ⟨hl, hasCompactSupport_of_loc _ hl _ (hΦ.2.isCompact.image continuous_snd) fun b hb => ?_⟩
  by_contra hne
  exact hb ⟨(a, b), subset_tsupport _ hne, rfl⟩
end GlobalTheory.JR.Hyp.PtTest
