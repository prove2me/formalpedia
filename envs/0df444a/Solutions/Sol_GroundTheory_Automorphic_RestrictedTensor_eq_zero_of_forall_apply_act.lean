-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.eq_zero_of_forall_apply_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:22.269444+00:00
-- url     : https://prove2.me/submissions/dc2d942f-1bb4-41a0-815f-00bc6f56c124

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_forall_apply

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
open Set
open GroundTheory.Automorphic.RestrictedTensor
variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ρ : Representation ℂ G V} [ρ.IsIrreducible]
    {l : Module.Dual ℂ V} (hl : l ≠ 0) {x : V} (h : ∀ g, l (ρ g x) = 0) : x = 0 := by
  by_contra hx
  exact hl (eq_zero_of_forall_apply (ρ := ρ) hx h)
end GroundTheory.Automorphic.RestrictedTensor
