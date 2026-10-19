-- Prove2me | solution 2 for OAI.Problem356.sqrt_sum_disjoint_squares
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:03:20.723935+00:00
-- url     : https://prove2.me/submissions/858f307e-6d7d-42b4-bcae-4d05fa9f0922

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/DisjointSquares.lean:L14-L48
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.sqrt_sum_disjoint_squares. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

-- ---- from OAI.Analysis.CoulombTransport.DisjointSquares ----
namespace OAI

universe uIndex uX

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem356

/-- Disjoint nonnegative summands allow the square root of a weighted sum of
squares to be written without any nonsmooth square-root composition. -/
theorem sqrt_sum_disjoint_squares {ι : Type uIndex} {X : Type uX} (s : Finset ι)
    (a : ι → ℝ) (g : ι → X → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (x : X) :
    Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, Real.sqrt (a i) * g i x := by
  classical
  by_cases h : ∃ i ∈ s, g i x ≠ 0
  · obtain ⟨i, hi, hix⟩ := h
    have hz : ∀ j ∈ s, j ≠ i → g j x = 0 := by
      intro j hj hji
      by_contra hjx
      exact Set.disjoint_left.mp (hd i hi j hj hji.symm) hix hjx
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · rw [Real.sqrt_mul (ha i hi), Real.sqrt_sq (hg i hi x)]
    · intro j hj hji
      simp [hz j hj hji]
    · exact fun hni => False.elim (hni hi)
    · intro j hj hji
      simp [hz j hj hji]
    · exact fun hni => False.elim (hni hi)
  · have hz : ∀ i ∈ s, g i x = 0 := by
      intro i hi
      by_contra hix
      exact h ⟨i, hi, hix⟩
    have hleft : (∑ i ∈ s, a i * (g i x) ^ 2) = 0 :=
      Finset.sum_eq_zero (fun i hi => by simp [hz i hi])
    have hright : (∑ i ∈ s, Real.sqrt (a i) * g i x) = 0 :=
      Finset.sum_eq_zero (fun i hi => by simp [hz i hi])
    rw [hleft, hright, Real.sqrt_zero]

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped BigOperators


theorem solution.{uIndex,uX} : type_of% @_root_.OAI.Problem356.sqrt_sum_disjoint_squares.{uIndex,uX} := @_root_.OAI.Problem356.sqrt_sum_disjoint_squares.{uIndex,uX}
