-- Prove2me | solution 1 for N4Code.twobitCount_C0form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:46.234852+00:00
-- url     : https://prove2.me/submissions/c723564d-a185-4553-b2aa-92094b493a1b

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_colWeight_eq_two_iff_C0form
import Theorems.Thm_N4Code_count_eq_card


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h : C0form C) :
    Even (twobitCount C) := by
  have hcard : twobitCount C = count C 5 + count C 6 := by
    unfold twobitCount
    rw [count_eq_card C 5, count_eq_card C 6]
    have hdisj : Disjoint (Finset.univ.filter fun t : Fin n => colVal (C t) = 5)
        (Finset.univ.filter fun t : Fin n => colVal (C t) = 6) := by
      rw [Finset.disjoint_filter]
      intro t _ h5 h6
      omega
    have hunion : (Finset.univ.filter fun t : Fin n => colVal (C t) = 5) ∪
        (Finset.univ.filter fun t : Fin n => colVal (C t) = 6) =
        Finset.univ.filter fun t : Fin n => colWeight (C t) = 2 := by
      ext t
      simp
      exact (colWeight_eq_two_iff_C0form C h t).symm
    rw [← hunion, ← Finset.card_union_of_disjoint hdisj]
  rcases h.2.1 with ⟨a, ha⟩
  rcases h.2.2 with ⟨b, hb⟩
  rw [hcard]
  refine ⟨a + b + 1, ?_⟩
  omega
end N4Code
