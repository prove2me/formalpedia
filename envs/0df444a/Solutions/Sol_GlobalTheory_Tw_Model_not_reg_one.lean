-- Prove2me | solution 1 for GlobalTheory.Tw.Model.not_reg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:21.331832+00:00
-- url     : https://prove2.me/submissions/2c4efdf6-7ccc-4454-8e92-013ea28ac8f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Theorems.Thm_GlobalTheory_Tw_Model_theta_one

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
theorem _root_.solution : ¬ Reg (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rintro ⟨-, h⟩
  rw [nrm, theta_one, Matrix.mul_one, ← Matrix.diagonal_one, Matrix.charpoly_diagonal,
    Polynomial.separable_prod_X_sub_C_iff] at h
  exact absurd (@h 0 1 rfl) (by decide)
end GlobalTheory.Tw.Model
