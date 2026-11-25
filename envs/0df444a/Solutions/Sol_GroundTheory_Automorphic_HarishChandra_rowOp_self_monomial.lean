-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rowOp_self_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:44.528963+00:00
-- url     : https://prove2.me/submissions/6e300b21-fb80-4218-80c1-acd408222b3a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_right
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_apply
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
theorem _root_.solution (i : Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ) :
    rowOp i i (monomial s c) = monomial s (c * (rowWt s i : ℂ)) := by
  rw [rowOp_apply, rowWt, Nat.cast_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_monomial, X, monomial_mul, one_mul]
  by_cases hk : s (i, k) = 0
  · simp [hk]
  · have hle : Finsupp.single (i, k) 1 ≤ s := by
      intro v
      rw [Finsupp.single_apply]
      split_ifs with hv
      · subst hv; omega
      · exact Nat.zero_le _
    rw [add_tsub_cancel_of_le hle]
end GroundTheory.Automorphic.HarishChandra
