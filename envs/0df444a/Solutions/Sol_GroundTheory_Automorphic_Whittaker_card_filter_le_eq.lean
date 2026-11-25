-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.card_filter_le_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:39.221652+00:00
-- url     : https://prove2.me/submissions/69ebb41a-2e10-4f5b-bfb6-44a115a4da59

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (w : Equiv.Perm (Fin n)) (r j : Fin n) :
    (Finset.univ.filter fun x : Fin n => r ≤ x ∧ w⁻¹ x ≤ j).card =
      (if w⁻¹ r ≤ j then 1 else 0) + (Finset.univ.filter fun x : Fin n => r < x ∧ w⁻¹ x ≤ j).card := by
  classical
  have hsplit : (Finset.univ.filter fun x : Fin n => r ≤ x ∧ w⁻¹ x ≤ j) =
      (Finset.univ.filter fun x : Fin n => x = r ∧ w⁻¹ x ≤ j) ∪
        (Finset.univ.filter fun x : Fin n => r < x ∧ w⁻¹ x ≤ j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h | h
      · exact Or.inl ⟨h.symm, h2⟩
      · exact Or.inr ⟨h, h2⟩
    · rintro (⟨rfl, h⟩ | ⟨h1, h2⟩)
      · exact ⟨le_rfl, h⟩
      · exact ⟨h1.le, h2⟩
  have hdisj : Disjoint (Finset.univ.filter fun x : Fin n => x = r ∧ w⁻¹ x ≤ j)
      (Finset.univ.filter fun x : Fin n => r < x ∧ w⁻¹ x ≤ j) := by
    rw [Finset.disjoint_filter]
    rintro x - ⟨rfl, -⟩ ⟨h, -⟩
    exact lt_irrefl _ h
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  congr 1
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl, -⟩
      rfl
    · rintro rfl
      exact ⟨rfl, h⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨rfl, hx⟩
    exact h hx
end GroundTheory.Automorphic.Whittaker
