-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.hcEmb_sub_eval_mem_vermaIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:08:18.646019+00:00
-- url     : https://prove2.me/submissions/9c3348da-9e14-4880-a124-f6ff33a020d9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_e_sub_mem_vermaIdeal
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
theorem _root_.solution (lam : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    hcEmb p - algebraMap ℂ (U n) (eval lam p) ∈ vermaIdeal lam := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, eval_add, map_add, add_sub_add_comm]
    exact Submodule.add_mem _ hp hq
  | mul_X p k hp =>
    have : hcEmb (p * X k) - algebraMap ℂ (U n) (eval lam (p * X k)) =
        hcEmb p * (e (k, k) - algebraMap ℂ (U n) (lam k)) +
          lam k • (hcEmb p - algebraMap ℂ (U n) (eval lam p)) := by
      rw [map_mul, hcEmb_X, eval_mul, eval_X]
      simp only [mul_sub, Algebra.smul_def]
      rw [Algebra.commutes (lam k) (hcEmb p), ← map_mul, mul_comm (lam k)]
      abel
    rw [this]
    exact Submodule.add_mem _ (mul_e_sub_mem_vermaIdeal lam _ k) (Submodule.smul_mem _ _ hp)
end GroundTheory.Automorphic.HarishChandra
