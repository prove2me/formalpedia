-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_wtProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:43.122643+00:00
-- url     : https://prove2.me/submissions/de830623-8bbf-44ff-9102-16ce004a0ca3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_coeff_wtProj
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
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (μ : Fin n → ℕ) (f g : Poly n) :
    fischer (wtProj μ f) g = fischer f (wtProj μ g) := by
  classical
  set s := f.support ∪ g.support
  have hg : (wtProj μ g).support ⊆ s := fun m hm => by
    rw [MvPolynomial.mem_support_iff, coeff_wtProj] at hm
    split_ifs at hm
    · exact Finset.mem_union_right _ (MvPolynomial.mem_support_iff.2 hm)
    · exact absurd rfl hm
  rw [fischer_eq_sum _ _ s Finset.subset_union_right, fischer_eq_sum _ _ s hg]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_wtProj, coeff_wtProj]
  split_ifs <;> simp
end GroundTheory.Automorphic.HarishChandra
