-- Prove2me | solution 1 for GlobalTheory.JR.Step.full_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:12.001719+00:00
-- url     : https://prove2.me/submissions/76fc3ea8-d87a-4210-82ad-532667ee5506

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftMatch
import Theorems.Thm_GlobalTheory_JR_Step_blocks_full

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
variable {r : ℕ} {k : Type} [CommRing k]
namespace GlobalTheory.JR.Step
theorem _root_.solution : Function.Injective (full : Gl r k → _) :=
  Function.LeftInverse.injective blocks_full
end GlobalTheory.JR.Step
