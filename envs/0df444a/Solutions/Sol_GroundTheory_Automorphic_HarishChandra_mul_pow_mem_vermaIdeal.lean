-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mul_pow_mem_vermaIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:48.94371+00:00
-- url     : https://prove2.me/submissions/bb424749-0cb8-440a-bc57-f969664caa54

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_nPlusU_le_vermaIdeal
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_mem_vermaIdeal
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_upper_mul_pow_mem
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_upper_simple_mul_pow_sub_mem
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pow_mul_h_sub_mem_vermaIdeal
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
variable {i j : Fin n}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (hij : (j : ℕ) = i + 1) (lam : Fin n → ℂ) (m : ℕ)
    (hm : lam i - lam j = m) {x : U n} (hx : x ∈ nPlusU n) :
    x * e (j, i) ^ (m + 1) ∈ vermaIdeal lam := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, b, hb, rfl⟩ := hx
    rw [mul_assoc]
    refine mul_mem_vermaIdeal lam u ?_
    by_cases hbij : b = (i, j)
    · subst hbij
      have h1 := e_upper_simple_mul_pow_sub_mem hij m
      have h2 := pow_mul_h_sub_mem_vermaIdeal lam m hm
      have : e (i, j) * e (j, i) ^ (m + 1) =
          (e (i, j) * e (j, i) ^ (m + 1) -
            (((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j))) -
              (((m : ℂ) + 1) * m) • e (j, i) ^ m)) +
          ((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j)) - (m : ℂ) • e (j, i) ^ m) := by
        rw [smul_sub, smul_smul]; abel
      rw [this]
      exact Submodule.add_mem _ (nPlusU_le_vermaIdeal lam h1) (Submodule.smul_mem _ _ h2)
    · exact nPlusU_le_vermaIdeal lam (e_upper_mul_pow_mem hij (m + 1) b hb hbij)
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx
end GroundTheory.Automorphic.HarishChandra
