-- Prove2me | solution 1 for GlobalTheory.det_gram_two_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:19.155395+00:00
-- url     : https://prove2.me/submissions/58b871bc-2443-472d-b4aa-6eb31da8cbf1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Theorems.Thm_GlobalTheory_det_fromBlocks_corner

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
namespace GlobalTheory
theorem _root_.solution {K : Type} [CommRing K] (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (T T' : K) :
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -T else 0) Z W
      (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0)).det
      = (-1) ^ (r + 1) * (Z.det * W.det - T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det
          * (W.submatrix Fin.castSucc Fin.castSucc).det)) := by
  have hs : (Matrix.fromBlocks 0 1 1 0 :
      Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K).det = (-1) ^ (r + 1) := by
    have h : (Matrix.fromBlocks 0 1 1 0 :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K)
        = Matrix.fromBlocks 1 (-1) 0 1 * Matrix.fromBlocks 1 1 1 0 := by
      simp [Matrix.fromBlocks_multiply]
    rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_one₁₁]
    simp [Matrix.det_neg]
  have hm : Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -T else 0) Z W
      (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0)
      = Matrix.fromBlocks Z (Matrix.diagonal fun i => if i = Fin.last r then -T else 0)
        (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0) W
        * Matrix.fromBlocks 0 1 1 0 := by
    simp [Matrix.fromBlocks_multiply]
  rw [hm, Matrix.det_mul, hs, det_fromBlocks_corner]
  ring
end GlobalTheory
