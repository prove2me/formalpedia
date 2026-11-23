-- Prove2me | solution 1 for GlobalTheory.Tw.Model.transpose_mul_Phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:13.962792+00:00
-- url     : https://prove2.me/submissions/96388c2c-4d80-4470-b422-a2cb26acd839

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
omit [StarRing R]
namespace GlobalTheory.Tw.Model
theorem _root_.solution : (Phi n R)ᵀ * Phi n R = 1 := mul_eq_one_comm.mp Phi_mul_transpose
end GlobalTheory.Tw.Model
