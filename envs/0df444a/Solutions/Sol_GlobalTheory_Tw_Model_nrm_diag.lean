-- Prove2me | solution 1 for GlobalTheory.Tw.Model.nrm_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:04.987895+00:00
-- url     : https://prove2.me/submissions/9b8922c1-75a3-4a67-a017-d11e375a8b1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Theorems.Thm_GlobalTheory_Tw_Model_Phi_two
import Theorems.Thm_GlobalTheory_Tw_Model_inv_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.Model
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
namespace GlobalTheory.Tw.Model
theorem _root_.solution : nrm (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![2, 1/2] := by
  rw [nrm, theta, inv_diag, Phi_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct, map_ofNat]
end GlobalTheory.Tw.Model
