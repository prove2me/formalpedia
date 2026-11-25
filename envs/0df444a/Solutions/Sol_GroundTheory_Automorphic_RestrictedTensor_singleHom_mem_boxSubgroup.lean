-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.singleHom_mem_boxSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:52.332373+00:00
-- url     : https://prove2.me/submissions/1782f123-9cb7-432d-82fb-6f6ca973c5be

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_singleHom_apply_self
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_singleHom_apply_of_ne

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
theorem _root_.solution {K' : ∀ v, Subgroup (G v)} {v : ι} {x : G v}
    (hx : x ∈ K' v) : singleHom K v x ∈ boxSubgroup K K' := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [singleHom_apply_self]
    exact hx
  · rw [singleHom_apply_of_ne _ hw]
    exact (K' w).one_mem
end GroundTheory.Automorphic.RestrictedTensor
