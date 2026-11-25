-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.eraseAt_mem_boxSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:18:57.754534+00:00
-- url     : https://prove2.me/submissions/f47ed41d-644d-4d65-896f-839bc5750394

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eraseAt_apply_self
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eraseAt_apply_of_ne

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
theorem _root_.solution {K' : ∀ v, Subgroup (G v)} (v : ι) {g : Πʳ w, [G w, K w]}
    (hg : g ∈ boxSubgroup K K') : eraseAt v g ∈ boxSubgroup K K' := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [eraseAt_apply_self]
    exact (K' w).one_mem
  · rw [eraseAt_apply_of_ne _ hw]
    exact hg w
end GroundTheory.Automorphic.RestrictedTensor
