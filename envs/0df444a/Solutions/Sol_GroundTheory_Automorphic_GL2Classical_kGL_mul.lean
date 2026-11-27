-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.kGL_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:44:19.234434+00:00
-- url     : https://prove2.me/submissions/e5558b56-317b-4833-8204-2efcb58b1863

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Iwasawa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix UpperHalfPlane
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.GL2Classical
namespace GroundTheory.Automorphic.GL2Classical
theorem _root_.solution (w₁ w₂ : ℂ) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) :
    kGL w₁ hw₁ * kGL w₂ hw₂ = kGL (w₁ * w₂) (mul_ne_zero hw₁ hw₂) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, coe_kGL, coe_kGL, coe_kGL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
end GroundTheory.Automorphic.GL2Classical
