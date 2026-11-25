-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.e_mul_canon_mem_spanLower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:10:13.091528+00:00
-- url     : https://prove2.me/submissions/421f9920-cf9c-4736-b903-16251a537ebf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_lowL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_of_mem_blockW
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_eq_blocks
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_add_notLower
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hasLower_add_notLower
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_closed_lower
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_mem_canonSpan
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
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
theorem _root_.solution (m : Fin n × Fin n →₀ ℕ) {a : Fin n × Fin n} (ha : IsLower a) :
    e a * canon m ∈ spanLower n := by
  have hw : ∀ b ∈ a :: blockW (lowL n) m, IsLower b := by
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ha
    · exact mem_lowL.1 (mem_of_mem_blockW hb).1
  have hspan := word_mem_canonSpan closed_lower _ hw
  rw [List.length_cons, show min 1 ((blockW (lowL n) m).length + 1) = 1 by omega] at hspan
  rw [canon_eq_blocks, ← mul_assoc, ← mul_assoc, ← word_cons]
  have : ∀ y ∈ canonSpan IsLower 1 ((blockW (lowL n) m).length + 1),
      y * word (blockW (diagL n) m) * word (blockW (upL n) m) ∈ spanLower n := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m', hm', h1, -, rfl⟩ := hx
      rw [canon_add_notLower hm']
      exact Submodule.subset_span ⟨_, hasLower_add_notLower hm' h1, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, add_mul]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ r hx
  exact this _ hspan
end GroundTheory.Automorphic.HarishChandra
