-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.apply_contract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:38.875745+00:00
-- url     : https://prove2.me/submissions/1d99d71e-2e98-4262-8ad0-e3d8be348c89

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_evalForm_tprod
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contract_tprod
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_finprod_eq_mul_weight

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
variable {N : Type*} [AddCommGroup N] [Module ℂ N]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ξ : ∀ v, V v} {l : ∀ v, Dual ℂ (V v)}
    {hl : ∀ᶠ v in cofinite, l v (ξ v) = 1} (v : ι) (t : ⨂[ℂ] w, V w) :
    l v (contract ξ l hl v t) = evalForm ξ l hl t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, map_smul, map_smul]
    congr 1
    by_cases hx : IsRestricted ξ x
    · rw [contract_tprod v hx, evalForm_tprod hx, map_smul, smul_eq_mul, mul_comm,
        finprod_eq_mul_weight hx hl v]
    · rw [contract, evalForm, lift.tprod, lift.tprod]
      show l v (restrictedIndicator ξ x • _) = restrictedIndicator ξ x • _
      simp [restrictedIndicator_of_not hx]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
end GroundTheory.Automorphic.RestrictedTensor
