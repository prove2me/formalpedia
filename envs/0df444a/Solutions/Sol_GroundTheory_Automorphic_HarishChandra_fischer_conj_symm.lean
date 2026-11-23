-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_conj_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:35.443927+00:00
-- url     : https://prove2.me/submissions/f208062b-e85a-4c47-9cee-f46deb5f9fa5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_eq_sum
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_left
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_right

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {σ : Type*}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (f g : MvPolynomial σ ℂ) : star (fischer f g) = fischer g f := by
  classical
  rw [fischer_eq_sum g f (f.support ∪ g.support) Finset.subset_union_left,
    fischer_eq_sum f g (f.support ∪ g.support) Finset.subset_union_right, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', Complex.star_def, Complex.conj_natCast, Complex.conj_conj]
  ring
end GroundTheory.Automorphic.HarishChandra
