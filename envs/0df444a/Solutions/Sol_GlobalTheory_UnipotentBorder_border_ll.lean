-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.border_ll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:49:58.330715+00:00
-- url     : https://prove2.me/submissions/e472cd62-b8db-4562-9111-69a25db85c1c

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
theorem _root_.solution : border A col row x (Fin.last n) (Fin.last n) = x := by simp [border]
end GlobalTheory.UnipotentBorder
