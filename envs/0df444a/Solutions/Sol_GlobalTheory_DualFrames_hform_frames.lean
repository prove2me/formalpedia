-- Prove2me | solution 1 for GlobalTheory.DualFrames.hform_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:45.919926+00:00
-- url     : https://prove2.me/submissions/c809ecbb-000d-4ec0-acb1-ac9c08857b0c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DualOfDualFrames
import Theorems.Thm_GlobalTheory_DualFrames_hform_eq_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.UG
open GlobalTheory GlobalTheory.DualFrames
variable {A : Type} [CommRing A] {k : ℕ}
namespace GlobalTheory.DualFrames
theorem _root_.solution (τ : A →+* A) (J B C : Matrix (Fin k) (Fin k) A)
    (h : cT τ B * J * C = 1) (x y : Fin k → A) :
    hform τ J (B *ᵥ x) (C *ᵥ y) = ∑ i, τ (x i) * y i := by
  rw [hform_eq_dot]
  have hmap : (τ ∘ (B *ᵥ x)) = (B.map τ) *ᵥ (τ ∘ x) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hct : (B.map τ)ᵀ = cT τ B := by
    unfold cT
    rfl
  rw [hmap, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hct, h, Matrix.one_mulVec]
  simp [dotProduct]
end GlobalTheory.DualFrames
