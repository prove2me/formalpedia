-- Prove2me | solution 1 for GlobalTheory.Tw.thetaGL_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:42:19.775175+00:00
-- url     : https://prove2.me/submissions/79882486-cdd0-4c34-8a3e-f6e730b29e06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_thetaGL_val
import Theorems.Thm_GlobalTheory_Tw_Model_theta_mul


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
open GlobalTheory GlobalTheory.Tw
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
namespace GlobalTheory.Tw
theorem _root_.solution (g h : GL (Fin n) R) : thetaGL (g * h) = thetaGL g * thetaGL h :=
  Units.ext (by simp only [Units.val_mul, thetaGL_val, Model.theta_mul])
end GlobalTheory.Tw
