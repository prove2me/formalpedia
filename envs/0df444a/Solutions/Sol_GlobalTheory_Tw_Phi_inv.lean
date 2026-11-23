-- Prove2me | solution 1 for GlobalTheory.Tw.Phi_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:51.716863+00:00
-- url     : https://prove2.me/submissions/e16d2c8a-8d26-4879-9c54-87ec3a38f91b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
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
open GlobalTheory GlobalTheory.Tw
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
omit [StarRing R]
namespace GlobalTheory.Tw
theorem _root_.solution : (Phi n R)⁻¹ = (Phi n R)ᵀ := Matrix.inv_eq_right_inv Model.Phi_mul_transpose
end GlobalTheory.Tw
