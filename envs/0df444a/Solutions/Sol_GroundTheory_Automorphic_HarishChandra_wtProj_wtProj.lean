-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.wtProj_wtProj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:50.092008+00:00
-- url     : https://prove2.me/submissions/ef55345a-850c-4148-bcb6-d111ee5b9f34

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_coeff_wtProj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (μ ν : Fin n → ℕ) (f : Poly n) :
    wtProj μ (wtProj ν f) = if μ = ν then wtProj ν f else 0 := by
  by_cases h : μ = ν
  · subst h
    rw [if_pos rfl]
    ext m
    rw [coeff_wtProj, coeff_wtProj]
    split_ifs <;> rfl
  · rw [if_neg h]
    ext m
    rw [coeff_wtProj, coeff_wtProj, coeff_zero]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) h
    · rfl
    · rfl
end GroundTheory.Automorphic.HarishChandra
