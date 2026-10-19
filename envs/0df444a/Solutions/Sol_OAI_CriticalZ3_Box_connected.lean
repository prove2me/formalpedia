-- Prove2me | solution 1 for OAI.CriticalZ3.Box.connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:34:08.743853+00:00
-- url     : https://prove2.me/submissions/f3219a9a-7981-47f6-a4e2-d1410d42a2e5

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Box
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical
theorem cz_box_conn_aux (B : Box) (y : Vertex) (hy : B.Contains y) :
    ∀ n : ℕ, ∀ x : Vertex, (∑ i, (x i - y i).natAbs) = n → B.Contains x →
      Relation.ReflTransGen B.Within x y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn hx
    by_cases hxy : x = y
    · subst hxy; exact Relation.ReflTransGen.refl
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra h; push_neg at h; exact hxy (funext h)
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · have hx' : B.Contains (step x i) := by
          intro j; have := hx j; have := hy j
          simp only [step]; split_ifs with h <;> [subst h; skip] <;> constructor <;> omega
        refine Relation.ReflTransGen.head ⟨⟨i, Or.inl rfl⟩, hx, hx'⟩ (ih _ ?_ _ rfl hx')
        rw [← hn]
        apply Finset.sum_lt_sum
        · intro j _; simp only [step]; split_ifs with h <;> [subst h; skip] <;> omega
        · exact ⟨i, Finset.mem_univ _, by simp only [step, if_true]; omega⟩
      · have hx' : B.Contains (backstep x i) := by
          intro j; have := hx j; have := hy j
          simp only [backstep]; split_ifs with h <;> [subst h; skip] <;> constructor <;> omega
        refine Relation.ReflTransGen.head ⟨⟨i, Or.inr (step_backstep x i).symm⟩, hx, hx'⟩
          (ih _ ?_ _ rfl hx')
        rw [← hn]
        apply Finset.sum_lt_sum
        · intro j _; simp only [backstep]; split_ifs with h <;> [subst h; skip] <;> omega
        · exact ⟨i, Finset.mem_univ _, by simp only [backstep, if_true]; omega⟩

theorem solution (B : Box) {x y : Vertex} (hx : B.Contains x) (hy : B.Contains y) :
    Relation.ReflTransGen B.Within x y := by
  exact cz_box_conn_aux B y hy _ x rfl hx

