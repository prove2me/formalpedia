-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.restrictedLift_apply_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:44.179072+00:00
-- url     : https://prove2.me/submissions/47cdbe21-1179-44e2-b194-3a4e34e0705f

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
variable {N : Type*} [AddCommGroup N] [Module ℂ N]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ξ : ∀ v, V v} {T : Finset ι} {l : ∀ v, Dual ℂ (V v)}
    {hl : ∀ᶠ v in cofinite, l v (ξ v) = 1} (f : MultilinearMap ℂ (fun v : T => V v) N)
    {x : ∀ v, V v} (hx : IsRestricted ξ x) :
    restrictedLift ξ T l hl f x = (∏ᶠ v, weight T l x v) • f (fun v => x v) := by
  show restrictedIndicator ξ x • ((∏ᶠ v, weight T l x v) • f (fun v => x v)) = _
  rw [restrictedIndicator_of hx, one_smul]
end GroundTheory.Automorphic.RestrictedTensor
