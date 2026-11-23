-- Prove2me | solution 1 for GlobalTheory.Tw.Model.theta_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:28.640134+00:00
-- url     : https://prove2.me/submissions/c2d04ead-bc37-4632-8558-0f7bcd8869cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Theorems.Thm_GlobalTheory_Tw_Model_Phi_mul_transpose

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
theorem _root_.solution : theta (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp [theta, Phi_mul_transpose]
end GlobalTheory.Tw.Model
