-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.finiteEmbed_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:46.030862+00:00
-- url     : https://prove2.me/submissions/a2dcf2c7-1e40-491f-8bf6-f11b6827e743

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_restrictedLift_apply_of
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isRestricted_extend
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_finiteEmbed_tprod

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
open PiTensorProduct Filter Function Module Set
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable [DecidableEq ι]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ξ : ∀ v, V v} {T : Finset ι} (hξ : ∀ v ∉ T, ξ v ≠ 0) :
    Injective (finiteEmbed ξ T) := by
  have hex : ∀ v, ∃ f : Dual ℂ (V v), v ∉ T → f (ξ v) = 1 := by
    intro v
    by_cases hv : v ∈ T
    · exact ⟨0, fun h => absurd hv h⟩
    · obtain ⟨f, hf⟩ : ∃ f : Dual ℂ (V v), f (ξ v) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hξ v hv ((Module.forall_dual_apply_eq_zero_iff ℂ (ξ v)).1 hcon)
      exact ⟨(f (ξ v))⁻¹ • f, fun _ => by simp [hf]⟩
  choose l hl using hex
  have hl' : ∀ᶠ v in cofinite, l v (ξ v) = 1 :=
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra hvT
      exact hv (hl v hvT))
  let P := lift (restrictedLift ξ T l hl' (PiTensorProduct.tprod ℂ))
  have hP : P ∘ₗ finiteEmbed ξ T = LinearMap.id := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun y => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, finiteEmbed_tprod,
      LinearMap.id_apply, P, lift.tprod]
    rw [restrictedLift_apply_of _ (isRestricted_extend ξ T y)]
    have hw : weight T l (extend ξ T y) = fun _ => 1 := by
      funext v
      by_cases hv : v ∈ T
      · exact weight_of_mem l _ hv
      · rw [weight_of_notMem l _ hv]
        simp [extend, hv, hl v hv]
    rw [hw, finprod_one, one_smul]
    congr 1
    funext ⟨v, hv⟩
    simp [extend, hv]
  exact Function.LeftInverse.injective (g := P) fun t => by
    simpa using congrArg (fun F => F t) hP
end GroundTheory.Automorphic.RestrictedTensor
