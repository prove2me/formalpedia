-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.pow_mul_h_sub_mem_vermaIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:19.643809+00:00
-- url     : https://prove2.me/submissions/8063081c-8ffc-47b4-ba37-b1daeb6e14b0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_e_sub_mem_vermaIdeal
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProj0_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.diagExp_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcEmb_X
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcProj0_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.pbw_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
variable {i j : Fin n}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (lam : Fin n → ℂ) (m : ℕ) (hm : lam i - lam j = m) :
    e (j, i) ^ m * (e (i, i) - e (j, j)) - (m : ℂ) • e (j, i) ^ m ∈ vermaIdeal lam := by
  have : e (j, i) ^ m * (e (i, i) - e (j, j)) - (m : ℂ) • e (j, i) ^ m =
      e (j, i) ^ m * (e (i, i) - algebraMap ℂ (U n) (lam i)) -
        e (j, i) ^ m * (e (j, j) - algebraMap ℂ (U n) (lam j)) := by
    rw [← hm]
    simp only [mul_sub, sub_smul, ← Algebra.commutes, ← Algebra.smul_def]
    abel
  rw [this]
  exact Submodule.sub_mem _ (mul_e_sub_mem_vermaIdeal lam _ i) (mul_e_sub_mem_vermaIdeal lam _ j)
end GroundTheory.Automorphic.HarishChandra
