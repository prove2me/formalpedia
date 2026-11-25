-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.e_upper_simple_mul_pow_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:03:39.534602+00:00
-- url     : https://prove2.me/submissions/62114f27-4972-4f00-bab0-edca109bf9f9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_diag_mul_e_pow
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rootAt_lower_self
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rootAt_lower_other
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_mul_sub_mul
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProj0_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_mem_nPlusU
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
theorem _root_.solution (hij : (j : ℕ) = i + 1) (m : ℕ) :
    e (i, j) * e (j, i) ^ (m + 1) -
      (((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j))) - (((m : ℂ) + 1) * m) • e (j, i) ^ m)
      ∈ nPlusU n := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hxy : e (i, j) * e (j, i) = e (j, i) * e (i, j) + (e (i, i) - e (j, j)) := by
    have := e_mul_sub_mul (i, j) (j, i)
    simp only [if_true] at this
    rw [← this]; abel
  have hh : ∀ p : ℕ, (e (i, i) - e (j, j)) * e (j, i) ^ p =
      e (j, i) ^ p * (e (i, i) - e (j, j)) - (2 * (p : ℂ)) • e (j, i) ^ p := by
    intro p
    rw [sub_mul, e_diag_mul_e_pow, e_diag_mul_e_pow, rootAt_lower_self hne, rootAt_lower_other hne,
      mul_sub]
    module
  induction m with
  | zero =>
    simp only [pow_zero, pow_one, one_mul, Nat.cast_zero, zero_add, one_smul, mul_zero, zero_smul,
      sub_zero]
    rw [hxy, add_sub_cancel_right]
    exact Submodule.subset_span ⟨_, _, by simp only [IsUpper]; rw [Fin.lt_def, hij]; omega, rfl⟩
  | succ m ih =>
    have key : e (i, j) * e (j, i) ^ (m + 1 + 1) -
        ((((m + 1 : ℕ) : ℂ) + 1) • (e (j, i) ^ (m + 1) * (e (i, i) - e (j, j))) -
          ((((m + 1 : ℕ) : ℂ) + 1) * ((m + 1 : ℕ) : ℂ)) • e (j, i) ^ (m + 1)) =
        e (j, i) * (e (i, j) * e (j, i) ^ (m + 1) -
          (((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j))) -
            (((m : ℂ) + 1) * m) • e (j, i) ^ m)) := by
      have e1 : e (i, j) * e (j, i) ^ (m + 1 + 1) =
          e (j, i) * (e (i, j) * e (j, i) ^ (m + 1)) + (e (i, i) - e (j, j)) * e (j, i) ^ (m + 1) := by
        rw [pow_succ' _ (m + 1), ← mul_assoc, hxy, add_mul, mul_assoc]
      rw [e1, hh]
      simp only [mul_sub, sub_mul, mul_smul_comm, ← mul_assoc, ← pow_succ']
      push_cast
      module
    rw [key]
    exact mul_mem_nPlusU _ ih
end GroundTheory.Automorphic.HarishChandra
