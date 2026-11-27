-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.range_finiteEmbed_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:51.305968+00:00
-- url     : https://prove2.me/submissions/92a762be-6778-4574-94e3-572459bd9803

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
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
theorem _root_.solution (ξ : ∀ v, V v) (T : Finset ι) :
    LinearMap.range (finiteEmbed ξ T) ≤ restrictedTensor ξ := by
  rintro _ ⟨t, rfl⟩
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    rw [map_smul, finiteEmbed_tprod]
    exact Submodule.smul_mem _ _ (tprod_mem_restrictedTensor (isRestricted_extend ξ T y))
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
end GroundTheory.Automorphic.RestrictedTensor
