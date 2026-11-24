-- Prove2me | solution 1 for GlobalTheory.Tw.star_PhiGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:31.276684+00:00
-- url     : https://prove2.me/submissions/2a9f2eb9-6cc8-446b-aa85-39baa0756932

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_Phi_inv
import Theorems.Thm_GlobalTheory_Tw_Model_Phi_conjTranspose


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
theorem _root_.solution : star (PhiGL n R) = (PhiGL n R)⁻¹ :=
  Units.ext (by simp [Matrix.star_eq_conjTranspose, Model.Phi_conjTranspose, Phi_inv])
end GlobalTheory.Tw
