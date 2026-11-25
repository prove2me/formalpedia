-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.diagGL_inv_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:58.64363+00:00
-- url     : https://prove2.me/submissions/cec0a0bb-a227-464a-bd7a-2118422ae539

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa
variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (d : Fin n → Fˣ) (g : GL (Fin n) F) (i j : Fin n) :
    ((diagGL F n d)⁻¹ * g * diagGL F n d : GL (Fin n) F) i j =
      (((d i)⁻¹ : Fˣ) : F) * g i j * (d j : F) := by
  rw [← map_inv]
  show ((diagGL F n d⁻¹ : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) *
    (diagGL F n d : Matrix (Fin n) (Fin n) F)) i j = _
  rw [coe_diagGL, coe_diagGL, mul_diagonal, diagonal_mul]
  rfl
end GroundTheory.Automorphic.Parabolic
