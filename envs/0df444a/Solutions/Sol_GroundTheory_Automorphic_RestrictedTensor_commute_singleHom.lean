-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.commute_singleHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:19:52.141838+00:00
-- url     : https://prove2.me/submissions/c074f7ae-3378-4d10-9fb8-521f5c310d6e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_singleHom_apply_of_ne
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_commute_of_forall

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
theorem _root_.solution {v : ι} (x : G v) {b : Πʳ w, [G w, K w]} (hb : b v = 1) :
    singleHom K v x * b = b * singleHom K v x :=
  commute_of_forall fun w => by
    by_cases hw : w = v
    · subst hw; exact Or.inr hb
    · exact Or.inl (singleHom_apply_of_ne _ hw)
end GroundTheory.Automorphic.RestrictedTensor
