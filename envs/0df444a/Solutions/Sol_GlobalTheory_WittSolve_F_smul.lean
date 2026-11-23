-- Prove2me | solution 1 for GlobalTheory.WittSolve.F_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:24.629694+00:00
-- url     : https://prove2.me/submissions/5a90bfe7-b25a-495c-8b4e-167fe06719a9

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
theorem _root_.solution (M : Matrix ι ι (WittVector p R)) (n : ℕ) (v : ι → WittVector p R) :
    F M (((p : WittVector p R) ^ n) • v) = ((p : WittVector p R) ^ n) • F M v := by
  have : (fun k => WittVector.frobenius ((((p : WittVector p R) ^ n) • v) k)) =
      ((p : WittVector p R) ^ n) • (fun k => WittVector.frobenius (v k)) := by
    funext k; simp [map_mul, map_pow, map_natCast]
  simp only [F, this, Matrix.mulVec_smul, smul_sub]
end GlobalTheory.WittSolve
