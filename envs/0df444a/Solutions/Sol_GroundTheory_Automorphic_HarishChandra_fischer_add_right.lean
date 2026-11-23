-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:33.305958+00:00
-- url     : https://prove2.me/submissions/f857dd46-f06a-4f76-858c-2f9e10d2324e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_eq_sum

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
variable {σ : Type*}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (f g g' : MvPolynomial σ ℂ) :
    fischer f (g + g') = fischer f g + fischer f g' := by
  classical
  set s := g.support ∪ g'.support
  rw [fischer_eq_sum f (g + g') s (MvPolynomial.support_add),
    fischer_eq_sum f g s Finset.subset_union_left, fischer_eq_sum f g' s Finset.subset_union_right]
  simp only [coeff_add, mul_add, Finset.sum_add_distrib]
end GroundTheory.Automorphic.HarishChandra
