-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isRestricted_extend
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:34.654064+00:00
-- url     : https://prove2.me/submissions/39785941-ea5f-49ae-8fc3-bebc49308350

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
variable [DecidableEq ι]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (ξ : ∀ v, V v) (T : Finset ι) (y : ∀ v : T, V v) :
    IsRestricted ξ (extend ξ T y) := by
  rw [isRestricted_iff_finite]
  refine T.finite_toSet.subset fun v hv => ?_
  by_contra hvT
  have hvT' : v ∉ T := by simpa using hvT
  exact hv (by simp [extend, hvT'])
end GroundTheory.Automorphic.RestrictedTensor
