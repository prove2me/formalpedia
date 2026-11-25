-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.hcProjLin_word_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:42:18.348796+00:00
-- url     : https://prove2.me/submissions/5fd5bdb4-2b6e-4426-8e9a-3d3e01e683d2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_mem_polyLE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_monomial_diagExp_toFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_sub_canon_mem_filt


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
theorem _root_.solution (w : List (Fin n × Fin n)) :
    hcProjLin (word w) - diagMain w ∈ polyLE n (w.length - 1) := by
  classical
  set M := Multiset.toFinsupp (w : Multiset (Fin n × Fin n))
  have h1 := hcProjLin_mem_polyLE (word_sub_canon_mem_filt w)
  rw [map_sub] at h1
  have h2 : hcProjLin (canon M) = diagMain w := by
    by_cases hw : ∀ a ∈ w, a.1 = a.2
    · have hd : IsDiagExp M := by
        intro a ha
        have : a ∈ w := by
          by_contra h'
          apply ha
          rw [Multiset.toFinsupp_apply]
          exact Multiset.count_eq_zero.2 (fun hm => h' (Multiset.mem_coe.1 hm))
        exact hw a this
      rw [hcProjLin_canon_of_isDiagExp hd, monomial_diagExp_toFinsupp w hw, diagMain, if_pos hw]
    · have hd : ¬ IsDiagExp M := by
        push Not at hw
        obtain ⟨a, ha, hne⟩ := hw
        intro hd
        refine hne (hd a ?_)
        rw [Multiset.toFinsupp_apply]
        exact (Multiset.count_pos.2 (Multiset.mem_coe.2 ha)).ne'
      rw [hcProjLin_canon_of_not hd, diagMain, if_neg hw]
  rwa [h2] at h1
end GroundTheory.Automorphic.HarishChandra
