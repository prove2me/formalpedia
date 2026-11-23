-- Prove2me | solution 1 for GlobalTheory.WittSolve.F_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:24.271022+00:00
-- url     : https://prove2.me/submissions/58a76720-3699-4e1c-baf7-df1b59b006dc

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
theorem _root_.solution (M : Matrix ι ι (WittVector p R)) (v w : ι → WittVector p R) :
    F M (v + w) = F M v + F M w := by
  have : (fun k => WittVector.frobenius ((v + w) k)) =
      (fun k => WittVector.frobenius (v k)) + (fun k => WittVector.frobenius (w k)) := by
    funext k; simp [map_add]
  simp only [F, this, Matrix.mulVec_add]; abel
end GlobalTheory.WittSolve
