-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isRestricted_update_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:59:29.941211+00:00
-- url     : https://prove2.me/submissions/07f9dcd4-3fd2-4391-b2b7-651e91dc5b79

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
theorem _root_.solution [DecidableEq ι] {ξ x : ∀ v, V v} {i : ι} {a : V i} :
    IsRestricted ξ (Function.update x i a) ↔ IsRestricted ξ x := by
  refine ⟨fun h => ?_, fun h => h.update i a⟩
  have := h.update i (x i)
  rwa [Function.update_idem, Function.update_eq_self] at this
end GroundTheory.Automorphic.RestrictedTensor
