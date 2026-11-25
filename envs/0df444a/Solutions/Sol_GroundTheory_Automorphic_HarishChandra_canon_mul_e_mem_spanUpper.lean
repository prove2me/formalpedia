-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.canon_mul_e_mem_spanUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:27:39.165433+00:00
-- url     : https://prove2.me/submissions/c054c9b1-71ba-4d0f-a10e-0602900bc6e7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_upL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_of_mem_blockW
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_eq_blocks
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_notUpper_add
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hasUpper_notUpper_add
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_closed_upper
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_mem_canonSpan
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_singleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.pbw_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcEmb_X
attribute [local simp] GroundTheory.Automorphic.HarishChandra.diagExp_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
open scoped IsMulCommutative
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (m : Fin n × Fin n →₀ ℕ) {a : Fin n × Fin n} (ha : IsUpper a) :
    canon m * e a ∈ spanUpper n := by
  have hw : ∀ b ∈ blockW (upL n) m ++ [a], IsUpper b := by
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact mem_upL.1 (mem_of_mem_blockW hb).1
    · rw [List.mem_singleton.1 hb]; exact ha
  have hspan := word_mem_canonSpan closed_upper _ hw
  rw [List.length_append, List.length_singleton, show min 1 ((blockW (upL n) m).length + 1) = 1 by
    omega] at hspan
  have heq : canon m * e a = word (blockW (lowL n) m) * word (blockW (diagL n) m) *
      word (blockW (upL n) m ++ [a]) := by
    rw [canon_eq_blocks, word_append, word_singleton, mul_assoc]
  rw [heq]
  have : ∀ y ∈ canonSpan IsUpper 1 ((blockW (upL n) m).length + 1),
      word (blockW (lowL n) m) * word (blockW (diagL n) m) * y ∈ spanUpper n := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m', hm', h1, -, rfl⟩ := hx
      rw [canon_notUpper_add hm']
      exact Submodule.subset_span ⟨_, hasUpper_notUpper_add hm' h1, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx
  exact this _ hspan
end GroundTheory.Automorphic.HarishChandra
