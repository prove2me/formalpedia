-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.eq_of_eval_eq_of_sub_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:08:00.847322+00:00
-- url     : https://prove2.me/submissions/4ce2f1ec-33de-4429-810d-bc03ee7769d7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
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
theorem _root_.solution (hij : i ≠ j) {P Q : MvPolynomial (Fin n) ℂ}
    (h : ∀ lam : Fin n → ℂ, ∀ m : ℕ, lam i - lam j = m → eval lam P = eval lam Q) : P = Q := by
  let f : Fin n → MvPolynomial (Fin n) ℂ := fun k => if k = i then X i + X j else X k
  let g : Fin n → MvPolynomial (Fin n) ℂ := fun k => if k = i then X i - X j else X k
  have hgf : (aeval g).comp (aeval f) = AlgHom.id ℂ _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    by_cases hk : k = i
    · subst hk; simp [f, g, Ne.symm hij]
    · simp [f, g, hk]
  have heval : ∀ (x : Fin n → ℂ) (R : MvPolynomial (Fin n) ℂ),
      eval x (aeval f R) = eval (fun k => if k = i then x i + x j else x k) R := by
    intro x R
    induction R using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, eval_add, eval_add, hp, hq]
    | mul_X p k hp =>
      rw [map_mul, eval_mul, eval_mul, hp, aeval_X, eval_X]
      by_cases hk : k = i
      · subst hk; simp [f]
      · simp [f, hk]
  have hfPQ : aeval f P = aeval f Q := by
    refine MvPolynomial.funext_set
      (fun k => if k = i then Set.range (Nat.cast : ℕ → ℂ) else Set.univ) (fun k => ?_) fun x hx => ?_
    · split_ifs
      · exact Set.infinite_range_of_injective Nat.cast_injective
      · exact Set.infinite_univ
    · have hxi : x i ∈ Set.range (Nat.cast : ℕ → ℂ) := by
        simpa using hx i (Set.mem_univ i)
      obtain ⟨m, hm⟩ := hxi
      rw [heval, heval]
      refine h _ m ?_
      simp [Ne.symm hij, hm]
  have := congrArg (aeval g) hfPQ
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hgf, AlgHom.id_apply, AlgHom.id_apply] at this
end GroundTheory.Automorphic.HarishChandra
