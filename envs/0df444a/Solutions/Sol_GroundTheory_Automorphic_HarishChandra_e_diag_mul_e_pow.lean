-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.e_diag_mul_e_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:59:35.812721+00:00
-- url     : https://prove2.me/submissions/98206373-440f-4519-8cb1-36ce662f4546

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_diag_mul_sub
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
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (k : Fin n) (a : Fin n × Fin n) (p : ℕ) :
    e (k, k) * e a ^ p = e a ^ p * e (k, k) + ((p : ℂ) * rootAt a k) • e a ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h : e (k, k) * e a = e a * e (k, k) + (rootAt a k : ℂ) • e a := by
      rw [← e_diag_mul_sub k a]; abel
    calc e (k, k) * e a ^ (p + 1) = (e (k, k) * e a ^ p) * e a := by rw [pow_succ, mul_assoc]
      _ = e a ^ p * (e (k, k) * e a) + ((p : ℂ) * rootAt a k) • (e a ^ p * e a) := by
          rw [ih, add_mul, mul_assoc, smul_mul_assoc]
      _ = e a ^ (p + 1) * e (k, k) + (((p + 1 : ℕ) : ℂ) * rootAt a k) • e a ^ (p + 1) := by
          rw [h, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ]
          push_cast
          rw [add_mul, one_mul, add_smul]
          abel
end GroundTheory.Automorphic.HarishChandra
