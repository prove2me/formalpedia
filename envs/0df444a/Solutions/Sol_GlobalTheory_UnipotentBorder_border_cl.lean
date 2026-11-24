-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.border_cl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:49:56.149559+00:00
-- url     : https://prove2.me/submissions/bcc09ff7-504b-4b3b-8828-5fcad120c316

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (col row : Fin n → O) (x : O)
omit [CommRing O]
namespace GlobalTheory.UnipotentBorder
theorem _root_.solution (i : Fin n) : border A col row x i.castSucc (Fin.last n) = col i := by simp [border]
end GlobalTheory.UnipotentBorder
