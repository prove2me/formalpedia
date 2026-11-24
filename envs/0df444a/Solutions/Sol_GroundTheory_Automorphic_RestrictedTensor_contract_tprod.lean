-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.contract_tprod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:07.982305+00:00
-- url     : https://prove2.me/submissions/3b6f6917-059b-4b9c-93a6-909ea64bc8ab

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_restrictedLift_apply_of

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
    {hl : ∀ᶠ v in cofinite, l v (ξ v) = 1} (v : ι) {x : ∀ v, V v} (hx : IsRestricted ξ x) :
    contract ξ l hl v (tprod ℂ x) = (∏ᶠ w, weight {v} l x w) • x v := by
  rw [contract, lift.tprod, restrictedLift_apply_of _ hx]
  rfl
end GroundTheory.Automorphic.RestrictedTensor
