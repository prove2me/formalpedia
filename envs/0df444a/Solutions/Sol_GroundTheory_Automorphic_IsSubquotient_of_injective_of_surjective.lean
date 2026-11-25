-- Prove2me | solution 1 for GroundTheory.Automorphic.IsSubquotient.of_injective_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:21.896339+00:00
-- url     : https://prove2.me/submissions/8a5014f8-f215-4ee2-8c64-bd520841c35c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Function Parabolic
universe u
variable {G : Type*} [Group G] {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup U] [Module ℂ U]
variable {π : Representation ℂ G W} {ρ : Representation ℂ G V} {θ : Representation ℂ G U}
namespace GroundTheory.Automorphic
namespace IsSubquotient
theorem _root_.solution {X : Type*} [AddCommGroup X] [Module ℂ X]
    {α : Representation ℂ G X} (i : Representation.IntertwiningMap α ρ) (hi : Injective i)
    (q : Representation.IntertwiningMap α π) (hq : Surjective q) : IsSubquotient π ρ := by
  let e : X ≃ₗ[ℂ] LinearMap.range i.toLinearMap := LinearEquiv.ofInjective i.toLinearMap hi
  let R : Subrepresentation ρ := ⟨LinearMap.range i.toLinearMap, by
    rintro g _ ⟨x, rfl⟩
    exact ⟨α g x, Representation.IntertwiningMap.isIntertwining _ _ i g x⟩⟩
  have he : ∀ x, ((e x : LinearMap.range i.toLinearMap) : V) = i x := fun x => rfl
  refine ⟨R, ⟨q.toLinearMap ∘ₗ e.symm.toLinearMap, fun g => ?_⟩, ?_⟩
  · refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    have h1 : R.toRepresentation g (e x) = e (α g x) := by
      apply Subtype.ext
      show ρ g ((e x : LinearMap.range i.toLinearMap) : V) = _
      rw [he, he]
      exact (Representation.IntertwiningMap.isIntertwining _ _ i g x).symm
    simp only [LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe, h1,
      LinearEquiv.symm_apply_apply, Representation.IntertwiningMap.toLinearMap_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _ q g x
  · intro y
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨e x, by simp⟩
end IsSubquotient
end GroundTheory.Automorphic
