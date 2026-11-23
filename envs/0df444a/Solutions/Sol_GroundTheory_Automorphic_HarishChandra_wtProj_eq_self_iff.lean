-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.wtProj_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:50.12555+00:00
-- url     : https://prove2.me/submissions/e0729be3-c08a-487e-9c9e-3c4d86580542

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
theorem _root_.solution (μ : Fin n → ℕ) (f : Poly n) :
    wtProj μ f = f ↔ ∀ m ∈ f.support, rowWt m = μ := by
  constructor
  · intro h m hm
    by_contra hne
    have := congrArg (coeff m) h
    rw [coeff_wtProj, if_neg hne] at this
    exact MvPolynomial.mem_support_iff.1 hm this.symm
  · intro h
    ext m
    rw [coeff_wtProj]
    split_ifs with hm
    · rfl
    · by_contra hc
      exact hm (h m (MvPolynomial.mem_support_iff.2 (Ne.symm hc)))
end GroundTheory.Automorphic.HarishChandra
