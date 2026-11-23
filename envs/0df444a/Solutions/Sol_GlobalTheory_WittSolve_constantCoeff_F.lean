-- Prove2me | solution 1 for GlobalTheory.WittSolve.constantCoeff_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:24.479153+00:00
-- url     : https://prove2.me/submissions/dd7da6cf-07e7-4a87-9bd0-3dd8bf2ef611

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
theorem _root_.solution (M : Matrix ι ι (WittVector p R)) (v : ι → WittVector p R) (k : ι) :
    WittVector.constantCoeff (F M v k) =
      ((fun j => WittVector.constantCoeff (v j)) - (M.map WittVector.constantCoeff).mulVec
        (fun j => frobenius R p (WittVector.constantCoeff (v j)))) k := by
  simp only [F, Pi.sub_apply, map_sub, RingHom.map_mulVec]
  congr 2
  funext j
  simp [Function.comp_def, WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
    frobenius_def]
end GlobalTheory.WittSolve
