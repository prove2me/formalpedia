-- Prove2me | solution 1 for GlobalTheory.WittSolve.F_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:25.6438+00:00
-- url     : https://prove2.me/submissions/820ae99d-e293-495d-868b-82985f1aa245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq
import Theorems.Thm_GlobalTheory_WittSolve_F_add

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
theorem _root_.solution (M : Matrix ι ι (WittVector p R)) (v w : ι → WittVector p R) :
    F M (v - w) = F M v - F M w := by
  have := F_add M (v - w) w
  rw [sub_add_cancel] at this
  rw [this]; abel
end GlobalTheory.WittSolve
