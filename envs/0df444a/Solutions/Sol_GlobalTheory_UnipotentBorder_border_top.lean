-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.border_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:44.189196+00:00
-- url     : https://prove2.me/submissions/e13a5a0f-089d-49f6-af14-15847a9b1793

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Theorems.Thm_GlobalTheory_UnipotentBorder_border_cc

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
theorem _root_.solution : (border A col row x).submatrix Fin.castSucc Fin.castSucc = A :=
  Matrix.ext fun i j ↦ border_cc A col row x i j
end GlobalTheory.UnipotentBorder
