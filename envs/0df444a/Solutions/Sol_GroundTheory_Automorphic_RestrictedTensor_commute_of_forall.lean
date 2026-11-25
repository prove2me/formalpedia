-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.commute_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:13:52.816334+00:00
-- url     : https://prove2.me/submissions/636a2233-dcab-4392-aac9-e5167330915b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places

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
open Filter Function Module Set
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}
variable [DecidableEq ι]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {a b : Πʳ w, [G w, K w]} (h : ∀ w, a w = 1 ∨ b w = 1) :
    a * b = b * a := by
  ext w
  simp only [RestrictedProduct.mul_apply]
  rcases h w with h | h <;> simp [h]
end GroundTheory.Automorphic.RestrictedTensor
