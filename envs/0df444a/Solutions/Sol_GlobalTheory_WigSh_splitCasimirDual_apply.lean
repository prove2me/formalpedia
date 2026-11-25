-- Prove2me | solution 1 for GlobalTheory.WigSh.splitCasimirDual_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:00:04.168361+00:00
-- url     : https://prove2.me/submissions/e0909d5f-b33f-47de-9887-74c4797662f9

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirEigenspaceIrreducibleDualStandardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReducedWignerCoefficientLoweringStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WignerExtremeNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PieriLoweringStepGlTensorDualStandard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
noncomputable section
open GlobalTheory GlobalTheory.WigSh
namespace GlobalTheory.WigSh
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (y : PiLp 2 (fun _ : Fin (n + 1) => V))
    (a : Fin (n + 1)) : splitCasimirDual E y a = ∑ c, E a c (y c) := rfl
end GlobalTheory.WigSh
