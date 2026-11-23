-- Prove2me | solution 1 for GlobalTheory.Tw.mulVec_dot_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:53.669412+00:00
-- url     : https://prove2.me/submissions/7355ac3e-0cf2-4857-85b2-d275ab5ce2bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars

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
variable {n : ℕ}
namespace GlobalTheory.Tw
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    (X *ᵥ v) ⬝ᵥ star w = v ⬝ᵥ star (Xᴴ *ᵥ w) := by
  rw [star_mulVec, conjTranspose_conjTranspose, dotProduct_comm v, ← dotProduct_mulVec, dotProduct_comm]
end GlobalTheory.Tw
