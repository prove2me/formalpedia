-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.tprod_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:14.272799+00:00
-- url     : https://prove2.me/submissions/02233051-60d8-48b7-ae2f-795d19d66a82

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_IsStable_mono
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_evalForm_tprod


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
open GroundTheory.Automorphic.RestrictedTensor
open PiTensorProduct Filter Function Module Set Topology
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ξ x : ∀ v, V v} (hx : IsRestricted ξ x) (h0 : ∀ v, x v ≠ 0) :
    tprod ℂ x ≠ 0 := by
  have hex : ∀ v, ∃ f : Dual ℂ (V v), f (x v) = 1 := by
    intro v
    obtain ⟨f, hf⟩ : ∃ f : Dual ℂ (V v), f (x v) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h0 v ((Module.forall_dual_apply_eq_zero_iff ℂ (x v)).1 hcon)
    exact ⟨(f (x v))⁻¹ • f, by simp [hf]⟩
  choose l hl using hex
  have hl' : ∀ᶠ v in cofinite, l v (ξ v) = 1 :=
    (show ∀ᶠ v in cofinite, x v = ξ v from hx).mono fun v h => by rw [← h, hl v]
  intro h
  have := evalForm_tprod (l := l) (hl := hl') hx
  rw [h, map_zero] at this
  simp [hl] at this
end GroundTheory.Automorphic.RestrictedTensor
