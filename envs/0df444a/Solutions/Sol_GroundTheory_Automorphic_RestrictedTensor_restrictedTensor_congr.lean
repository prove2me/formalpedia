-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.restrictedTensor_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:52.771501+00:00
-- url     : https://prove2.me/submissions/454af811-d6cd-43ec-8182-618bab2ace3a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted

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
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ξ ξ' : ∀ v, V v} (h : ∀ᶠ v in cofinite, ξ v = ξ' v) :
    restrictedTensor ξ = restrictedTensor ξ' := by
  have key : ∀ {ξ ξ' : ∀ v, V v}, (∀ᶠ v in cofinite, ξ v = ξ' v) →
      restrictedTensor ξ ≤ restrictedTensor ξ' := by
    intro ξ ξ' h
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine tprod_mem_restrictedTensor ?_
    filter_upwards [show ∀ᶠ v in cofinite, x v = ξ v from hx, h] with v h1 h2 using h1.trans h2
  exact le_antisymm (key h) (key (h.mono fun v hv => hv.symm))
end GroundTheory.Automorphic.RestrictedTensor
