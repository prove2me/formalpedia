-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.hcEmb_mul_e_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:05:33.642049+00:00
-- url     : https://prove2.me/submissions/630caada-a015-4907-bf8f-931dddf23747

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_diag_mul_e_pow
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
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
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (a : Fin n × Fin n) (p : ℕ) (q : MvPolynomial (Fin n) ℂ) :
    hcEmb q * e a ^ p = e a ^ p * hcEmb (translate (fun k => (p : ℂ) * rootAt a k) q) := by
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [show translate (fun k => (p : ℂ) * rootAt a k) (C c) = C c by simp [translate],
      ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.commutes]
  | add q r hq hr => rw [map_add, add_mul, hq, hr, map_add, map_add, mul_add]
  | mul_X q k hq =>
    set T := translate (fun k => (p : ℂ) * rootAt a k)
    have hTX : hcEmb (T (X k)) = e (k, k) + ((p : ℂ) * rootAt a k) • 1 := by
      simp only [T, translate, aeval_X, map_add, hcEmb_X, ← MvPolynomial.algebraMap_eq,
        Algebra.algebraMap_eq_smul_one, map_smul, map_one]
    calc hcEmb (q * X k) * e a ^ p = hcEmb q * (e (k, k) * e a ^ p) := by
          rw [map_mul, hcEmb_X, mul_assoc]
      _ = (hcEmb q * e a ^ p) * e (k, k) + ((p : ℂ) * rootAt a k) • (hcEmb q * e a ^ p) := by
          rw [e_diag_mul_e_pow, mul_add, mul_smul_comm, mul_assoc]
      _ = e a ^ p * (hcEmb (T q) * e (k, k) + ((p : ℂ) * rootAt a k) • hcEmb (T q)) := by
          rw [hq, mul_add, mul_smul_comm, mul_assoc]
      _ = e a ^ p * hcEmb (T (q * X k)) := by
          rw [map_mul T, map_mul hcEmb, hTX]
          simp only [mul_add, mul_smul_comm, mul_one]
end GroundTheory.Automorphic.HarishChandra
