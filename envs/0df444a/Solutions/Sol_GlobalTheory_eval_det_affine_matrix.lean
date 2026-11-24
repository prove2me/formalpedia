-- Prove2me | solution 1 for GlobalTheory.eval_det_affine_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:38:06.321114+00:00
-- url     : https://prove2.me/submissions/e1f89ec8-6ce3-4368-a1d1-4f8e47d7af55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsHermitianDetNeZeroTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial Matrix
namespace GlobalTheory
theorem _root_.solution {κ ι : Type} [Field κ] {n : ℕ} (c d : Matrix (Fin n) (Fin n) κ)
    (G : Matrix (Fin n) (Fin n) (MvPolynomial ι κ)) (u : ι → κ) :
    MvPolynomial.eval u (c.map C * G + d.map C).det =
      (c * G.map (MvPolynomial.eval u) + d).det := by
  rw [RingHom.map_det, map_add, map_mul]
  congr 1
  ext i j
  simp [Matrix.mul_apply]
end GlobalTheory
