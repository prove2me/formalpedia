-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.hcProjLin_capelli_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:01.721978+00:00
-- url     : https://prove2.me/submissions/ccbd6471-36ea-4789-82d5-fa4b22abbdf7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_word_sub_mem
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_sum_diagMain_capelliWord
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_capelli_eq_sum_word


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (k : ℕ) :
    hcProjLin (capelli (n := n) (k + 1)) - psum (Fin n) ℂ (k + 1) ∈ polyLE n k := by
  rw [capelli_eq_sum_word, map_sum, ← sum_diagMain_capelliWord, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  have := hcProjLin_word_sub_mem (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t)))
  rwa [List.length_ofFn, Nat.add_sub_cancel] at this
end GroundTheory.Automorphic.HarishChandra
