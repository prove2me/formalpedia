-- Prove2me | solution 1 for GlobalTheory.LeviDesc.Krylov.krylov_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:40:40.589177+00:00
-- url     : https://prove2.me/submissions/86190851-bcba-4f89-9e4b-911247bdeca8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LeviDesc GlobalTheory.LeviDesc.Krylov
namespace GlobalTheory.LeviDesc.Krylov
theorem _root_.solution {F : Type} [CommRing F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) (i j : Fin r) :
    krylov y e i j = Matrix.mulVec (y ^ (j : ℕ)) e i := rfl
end GlobalTheory.LeviDesc.Krylov
