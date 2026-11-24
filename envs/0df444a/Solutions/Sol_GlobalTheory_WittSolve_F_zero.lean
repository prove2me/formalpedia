-- Prove2me | solution 1 for GlobalTheory.WittSolve.F_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:44.045808+00:00
-- url     : https://prove2.me/submissions/45ba2a39-c503-4472-ac32-61c73f6ec3bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittSolve
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type} [Fintype ι]
namespace GlobalTheory.WittSolve
theorem _root_.solution (M : Matrix ι ι (WittVector p R)) : F M 0 = 0 := by
  simp only [F, Pi.zero_apply, map_zero, sub_eq_zero]
  exact (Matrix.mulVec_zero M).symm
end GlobalTheory.WittSolve
