-- Prove2me | solution 1 for GlobalTheory.ddChar_unip_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:56.658437+00:00
-- url     : https://prove2.me/submissions/412d9c5e-4b76-4edf-be02-04dafc16424c

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
theorem _root_.solution {x y : n → R} (h : y ⬝ᵥ x = 0) (g : GL n R) (i j : n) :
    ((ddCharUnip _ (ddChar_vecMulVec_sq h) * g : GL n R) : Matrix n n R) i j
      = (g : Matrix n n R) i j + x i * ∑ k, y k * (g : Matrix n n R) k j := by
  show ((1 + vecMulVec x y) * (g : Matrix n n R)) i j = _
  rw [add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [vecMulVec_apply]; ring
end GlobalTheory
