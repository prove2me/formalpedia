-- Prove2me | solution 1 for GlobalTheory.Tw.Model.reg_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:28.119678+00:00
-- url     : https://prove2.me/submissions/6b9cc487-70aa-4ab4-bba3-ba4e81f1dfde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Theorems.Thm_GlobalTheory_Tw_Model_nrm_diag

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
theorem _root_.solution : Reg (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det]; simp [Matrix.det_fin_two]
  · rw [nrm_diag, Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all <;> norm_num at h
end GlobalTheory.Tw.Model
