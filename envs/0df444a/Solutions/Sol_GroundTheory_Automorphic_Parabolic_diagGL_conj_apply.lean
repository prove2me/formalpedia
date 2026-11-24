-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.diagGL_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:55.782016+00:00
-- url     : https://prove2.me/submissions/beff89d1-c0ca-407b-93d2-7be73d66b4bc

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
    (diagGL F n d * g * (diagGL F n d)⁻¹ : GL (Fin n) F) i j =
      (d i : F) * g i j * ((d j)⁻¹ : Fˣ) := by
  rw [← map_inv]
  show ((diagGL F n d : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) *
    (diagGL F n d⁻¹ : Matrix (Fin n) (Fin n) F)) i j = _
  rw [coe_diagGL, coe_diagGL, mul_diagonal, diagonal_mul]
  rfl
end GroundTheory.Automorphic.Parabolic
