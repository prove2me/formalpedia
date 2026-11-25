-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.commute_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:42.651796+00:00
-- url     : https://prove2.me/submissions/0ed96cda-682e-41fe-98ac-29088aed6a8a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Existence
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_commute_of_mem_adjoin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Filter Function Module Set PiTensorProduct
open scoped TensorProduct RestrictedProduct
variable {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
variable {ι : Type*} {T : ι → Set (End ℂ M)}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (hcomm : ∀ v w, v ≠ w → ∀ a ∈ T v, ∀ b ∈ T w, Commute a b)
    {v w : ι} (hvw : v ≠ w) {a b : End ℂ M} (ha : a ∈ Algebra.adjoin ℂ (T v))
    (hb : b ∈ Algebra.adjoin ℂ (T w)) : Commute a b :=
  commute_of_mem_adjoin (fun t ht =>
    (commute_of_mem_adjoin (fun s hs => (hcomm v w hvw s hs t ht).symm) a ha).symm) b hb
end GroundTheory.Automorphic.RestrictedTensor
