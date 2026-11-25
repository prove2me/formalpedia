-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.contract_tensorRep_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:13:54.392063+00:00
-- url     : https://prove2.me/submissions/171ec1b2-94ef-4106-88f1-6346fee37fe3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Uniqueness
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contract_tprod
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isRestricted_update_iff
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_tensorRep_mulSingle_tprod


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
open Filter Function Module Set PiTensorProduct
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}
  {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution [DecidableEq ι] (π : ∀ v, Representation ℂ (G v) (V v))
    {ξ : ∀ v, V v} {l : ∀ v, Dual ℂ (V v)} (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1) (v : ι)
    (g : G v) (t : ⨂[ℂ] w, V w) :
    contract ξ l hl v (tensorRep K π (singleHom K v g) t) = π v g (contract ξ l hl v t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, map_smul, map_smul, map_smul]
    congr 1
    have h1 : tensorRep K π (singleHom K v g) (tprod ℂ x) =
        tprod ℂ (Function.update x v (π v g (x v))) := tensorRep_mulSingle_tprod v g x
    rw [h1]
    by_cases hx : IsRestricted ξ x
    · rw [contract_tprod v (hx.update v _), contract_tprod v hx, map_smul,
        weight_update_of_mem l x (Finset.mem_singleton_self v), Function.update_self]
    · have hx' : ¬ IsRestricted ξ (Function.update x v (π v g (x v))) :=
        fun h => hx (isRestricted_update_iff.1 h)
      rw [contract, lift.tprod, lift.tprod]
      show restrictedIndicator ξ _ • _ = π v g (restrictedIndicator ξ x • _)
      rw [restrictedIndicator_of_not hx, restrictedIndicator_of_not hx', zero_smul, zero_smul,
        map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
end GroundTheory.Automorphic.RestrictedTensor
