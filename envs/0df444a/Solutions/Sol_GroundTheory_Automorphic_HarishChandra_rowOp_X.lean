-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rowOp_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:42.101912+00:00
-- url     : https://prove2.me/submissions/4fa0899e-4831-4c14-868d-9cae2e94f332

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
theorem _root_.solution (i j b c : Fin n) :
    rowOp i j (X (b, c) : Poly n) = if b = j then X (i, c) else 0 := by
  rw [rowOp_apply]
  by_cases hb : b = j
  · subst hb
    rw [if_pos rfl, Finset.sum_eq_single c]
    · rw [pderiv_X_self, mul_one]
    · intro k _ hk
      rw [pderiv_X_of_ne (by intro h; exact hk (Prod.ext_iff.1 h).2.symm), mul_zero]
    · simp
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [pderiv_X_of_ne (by intro h; exact hb (Prod.ext_iff.1 h).1), mul_zero]
end GroundTheory.Automorphic.HarishChandra
