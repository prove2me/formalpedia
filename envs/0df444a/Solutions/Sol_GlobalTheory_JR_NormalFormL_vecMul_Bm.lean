-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.vecMul_Bm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:08:34.288934+00:00
-- url     : https://prove2.me/submissions/f31b3c6c-91fb-43ac-989a-122b9147c4ae

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.NormalFormL
theorem _root_.solution (Y : Gl r k) : Y.2.2.1 ᵥ* Bm Y = (inv Y).2.1 := by
  funext j
  simp [vecMul, dotProduct, Bm, inv, mom, mulVec]
end GlobalTheory.JR.NormalFormL
