-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rowOp_self_of_wtProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:16.175883+00:00
-- url     : https://prove2.me/submissions/474d4cdb-689d-4dc0-abc7-cd503a44318e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_coeff_rowOp_self
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wtProj_eq_self_iff
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
theorem _root_.solution (μ : Fin n → ℕ) (v : Poly n) (i : Fin n) (h : wtProj μ v = v) :
    rowOp i i v = (μ i : ℂ) • v := by
  ext m
  rw [coeff_rowOp_self, coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ v.support
  · rw [(wtProj_eq_self_iff μ v).1 h m hm]
  · rw [MvPolynomial.notMem_support_iff.1 hm]; simp
end GroundTheory.Automorphic.HarishChandra
