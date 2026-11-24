-- Prove2me | solution 1 for GlobalTheory.IwahoriFactor.flip_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:57:35.618078+00:00
-- url     : https://prove2.me/submissions/f6e5c40c-26a8-4c1c-94c4-d0a0f0fc4d24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IwahoriFactor
variable {O : Type} [CommRing O] {n : ℕ}
namespace GlobalTheory.IwahoriFactor
theorem _root_.solution (g : Matrix (Fin n) (Fin n) O) (i j : Fin n) :
    flip g i j = g i.rev j.rev := rfl
end GlobalTheory.IwahoriFactor
