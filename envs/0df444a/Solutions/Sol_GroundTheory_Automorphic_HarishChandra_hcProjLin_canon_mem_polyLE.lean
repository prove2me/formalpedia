-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.hcProjLin_canon_mem_polyLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:19.526478+00:00
-- url     : https://prove2.me/submissions/f61cef64-abd5-4442-ac49-1b031555cf11

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_polyLE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_sum_diagExp_le

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
theorem _root_.solution {d : ℕ} {m : Fin n × Fin n →₀ ℕ} (hm : m.degree ≤ d) :
    hcProjLin (canon m) ∈ polyLE n d := by
  by_cases h : IsDiagExp m
  · rw [hcProjLin_canon_of_isDiagExp h, mem_polyLE]
    exact (totalDegree_monomial_le _ _).trans ((sum_diagExp_le m).trans hm)
  · rw [hcProjLin_canon_of_not h]
    exact Submodule.zero_mem _
end GroundTheory.Automorphic.HarishChandra
