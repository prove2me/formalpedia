-- Prove2me | solution 1 for GlobalTheory.ddChar_det_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:51.491459+00:00
-- url     : https://prove2.me/submissions/c178c16d-6e17-49ef-ab4f-45c9fdf79572

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
  {A : Type} [CommGroup A]
namespace GlobalTheory
theorem _root_.solution {x y : n → R} (h : y ⬝ᵥ x = 0) :
    ((ddCharUnip _ (ddChar_vecMulVec_sq h) : GL n R) : Matrix n n R).det = 1 := by
  show (1 + vecMulVec x y).det = 1
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, h, add_zero]
end GlobalTheory
