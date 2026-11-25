-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.e_upper_mul_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:14.734148+00:00
-- url     : https://prove2.me/submissions/f8875c6b-3e77-45e0-ae1a-035208168d83

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
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
    ∀ b : Fin n × Fin n, IsUpper b → b ≠ (i, j) → e b * e (j, i) ^ m ∈ nPlusU n := by
  induction m with
  | zero =>
    intro b hb _
    rw [pow_zero, mul_one]
    exact Submodule.subset_span ⟨1, b, hb, one_mul _⟩
  | succ m ih =>
    intro b hb hne
    have hc := e_mul_sub_mul b (j, i)
    have : e b * e (j, i) ^ (m + 1) = e (j, i) * (e b * e (j, i) ^ m) +
        ((if b.2 = j then e (b.1, i) else 0) - (if i = b.1 then e (j, b.2) else 0)) *
          e (j, i) ^ m := by
      rw [← hc, pow_succ']; noncomm_ring
    rw [this]
    refine Submodule.add_mem _ (mul_mem_nPlusU _ (ih b hb hne)) ?_
    rw [sub_mul]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs with h2
      · refine ih (b.1, i) ?_ ?_
        · simp only [IsUpper] at hb ⊢
          have h1 : b.1 ≠ i := fun h1 => hne (Prod.ext h1 h2)
          rw [Fin.lt_def] at hb ⊢
          rw [h2, hij] at hb
          have : (b.1 : ℕ) ≠ i := fun h => h1 (Fin.ext h)
          omega
        · intro h; simp only [Prod.mk.injEq] at h
          rw [h.2] at hij; omega
      · rw [zero_mul]; exact Submodule.zero_mem _
    · split_ifs with h1
      · refine ih (j, b.2) ?_ ?_
        · simp only [IsUpper] at hb ⊢
          have h2 : b.2 ≠ j := fun h2 => hne (Prod.ext h1.symm h2)
          rw [Fin.lt_def] at hb ⊢
          rw [← h1] at hb
          have : (b.2 : ℕ) ≠ j := fun h => h2 (Fin.ext h)
          omega
        · intro h; simp only [Prod.mk.injEq] at h
          have := congrArg Fin.val h.1; omega
      · rw [zero_mul]; exact Submodule.zero_mem _
end GroundTheory.Automorphic.HarishChandra
