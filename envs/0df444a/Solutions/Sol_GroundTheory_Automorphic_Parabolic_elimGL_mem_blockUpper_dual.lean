-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.elimGL_mem_blockUpper_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:35:54.52949+00:00
-- url     : https://prove2.me/submissions/00018bfc-116c-4a4e-a8c7-ae278e4e13ea

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_le_of_elimKey_lt
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_blockUpper


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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
variable (β)
variable {β}
variable (β)
variable {β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (h : Matrix (Fin n) (Fin n) F) (a : Fin n) :
    elimGL β h a ∈ blockUpper F n (OrderDual.toDual ∘ β) := by
  rw [mem_blockUpper]
  intro i k hik
  have hik' : β i < β k := hik
  show (1 : Matrix (Fin n) (Fin n) F) i k - elimCol β h a i k = 0
  rw [one_apply_ne (fun e => hik'.ne (by rw [e])), elimCol_apply, if_neg, sub_zero]
  rintro ⟨rfl, hk⟩
  exact (le_of_elimKey_lt hk).not_gt hik'
end GroundTheory.Automorphic.Parabolic
