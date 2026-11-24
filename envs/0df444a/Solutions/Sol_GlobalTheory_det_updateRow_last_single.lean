-- Prove2me | solution 1 for GlobalTheory.det_updateRow_last_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:57.774272+00:00
-- url     : https://prove2.me/submissions/35c17b6f-d4dc-44e0-9231-574137879fd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle

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
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (Z.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).det
      = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [← Matrix.adjugate_apply, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [← two_mul, pow_mul]
end GlobalTheory
