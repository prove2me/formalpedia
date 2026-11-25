-- Prove2me | solution 1 for GlobalTheory.WigSh.exists_splitCasimir_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:42:52.143885+00:00
-- url     : https://prove2.me/submissions/f86b7389-e823-4081-b0b9-126cfd1a0a0a

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WignerExtremeNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirEigenspaceIrreducibleStandardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_StarProjectionSplitCasimirRaisingLastStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PieriRaisingSubmoduleGlSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open GlobalTheory GlobalTheory.WigSh
namespace GlobalTheory.WigSh
theorem _root_.solution (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) :
    ∃ Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), ∀ y b, Om y b = ∑ c, E c b (y c) := by
  refine ⟨(WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun b => ∑ c, E c b ∘ₗ LinearMap.proj c) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).toLinearMap, ?_⟩
  intro y b
  simp [LinearMap.sum_apply]
end GlobalTheory.WigSh
