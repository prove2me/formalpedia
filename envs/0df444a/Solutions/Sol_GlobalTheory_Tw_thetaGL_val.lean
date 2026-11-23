-- Prove2me | solution 1 for GlobalTheory.Tw.thetaGL_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:15.934033+00:00
-- url     : https://prove2.me/submissions/b6e8f515-188d-4a11-911c-fa53cb9da792

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_Phi_inv

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
theorem _root_.solution (g : GL (Fin n) R) : (thetaGL g).val = theta g.val := by
  simp [thetaGL, theta, Matrix.star_eq_conjTranspose, Phi_inv]
end GlobalTheory.Tw
