-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.monomial_diagExp_toFinsupp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:05:36.256866+00:00
-- url     : https://prove2.me/submissions/868fbad0-c2ff-4646-a4f9-d9cc16cecb30

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_add
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_single
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
theorem _root_.solution (w : List (Fin n × Fin n)) (hw : ∀ a ∈ w, a.1 = a.2) :
    monomial (diagExp (Multiset.toFinsupp (w : Multiset (Fin n × Fin n)))) (1 : ℂ) =
      (w.map fun a => X a.1).prod := by
  induction w with
  | nil =>
    have : diagExp (Multiset.toFinsupp (([] : List (Fin n × Fin n)) : Multiset (Fin n × Fin n))) = 0 := by
      ext; simp
    rw [this, monomial_zero', C_1]
    simp
  | cons a w ih =>
    rw [show ((a :: w : List _) : Multiset _) = {a} + (w : Multiset (Fin n × Fin n)) by simp,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, diagExp_add,
      show a = (a.1, a.1) from Prod.ext rfl (hw a (List.mem_cons_self ..)).symm, diagExp_single,
      ← one_mul (1 : ℂ), ← monomial_mul, ih fun b hb => hw b (List.mem_cons_of_mem _ hb),
      List.map_cons, List.prod_cons, ← pow_one (X a.1), X_pow_eq_monomial]
end GroundTheory.Automorphic.HarishChandra
