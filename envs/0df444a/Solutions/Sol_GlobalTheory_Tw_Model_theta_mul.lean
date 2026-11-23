-- Prove2me | solution 1 for GlobalTheory.Tw.Model.theta_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:46.49643+00:00
-- url     : https://prove2.me/submissions/322a80f0-e187-488d-a443-015c7e108180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Theorems.Thm_GlobalTheory_Tw_Model_transpose_mul_Phi

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
theorem _root_.solution (g h : Matrix (Fin n) (Fin n) R) : theta (g * h) = theta g * theta h := by
  simp only [theta, Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R), transpose_mul_Phi, Matrix.one_mul]
end GlobalTheory.Tw.Model
