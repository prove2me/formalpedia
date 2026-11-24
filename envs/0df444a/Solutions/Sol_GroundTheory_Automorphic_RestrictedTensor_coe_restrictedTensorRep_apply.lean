-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.coe_restrictedTensorRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:49.157207+00:00
-- url     : https://prove2.me/submissions/06d01ab7-ecd9-40f3-acd9-4cb5639fbdf4

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
variable {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (π : ∀ v, Representation ℂ (G v) (V v)) (ξ : ∀ v, V v)
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)) (g : Πʳ v, [G v, K v])
    (t : restrictedTensor ξ) :
    (restrictedTensorRep π ξ hξ g t : ⨂[ℂ] v, V v) = tensorRep K π g t :=
  rfl
end GroundTheory.Automorphic.RestrictedTensor
