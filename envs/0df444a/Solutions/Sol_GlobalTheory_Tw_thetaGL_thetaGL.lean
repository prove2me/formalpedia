-- Prove2me | solution 1 for GlobalTheory.Tw.thetaGL_thetaGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:42:20.729822+00:00
-- url     : https://prove2.me/submissions/3ddfa936-af88-463a-a76e-66f5eea488bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_thetaGL_val
import Theorems.Thm_GlobalTheory_Tw_Model_theta_theta


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
theorem _root_.solution (g : GL (Fin n) R) : thetaGL (thetaGL g) = g :=
  Units.ext (by rw [thetaGL_val, thetaGL_val, Model.theta_theta g.isUnit])
end GlobalTheory.Tw
