-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.extend_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:31.298873+00:00
-- url     : https://prove2.me/submissions/c71aa227-5d51-4c53-9031-cd3abe6aa3a9

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
theorem _root_.solution {ξ x : ∀ v, V v} {T : Finset ι} (h : ∀ v ∉ T, x v = ξ v) :
    extend ξ T (fun v => x v) = x := by
  funext v
  unfold extend
  split_ifs with hv
  · rfl
  · exact (h v hv).symm
end GroundTheory.Automorphic.RestrictedTensor
