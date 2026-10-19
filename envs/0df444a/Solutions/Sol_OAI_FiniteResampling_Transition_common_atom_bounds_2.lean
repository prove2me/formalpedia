-- Prove2me | solution 2 for OAI.FiniteResampling.Transition.common_atom_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:33:39.11998+00:00
-- url     : https://prove2.me/submissions/f862b800-d333-44b6-b65c-1ce82e576e9a

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Resampling.lean:L65-L88
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteResampling.Transition.common_atom_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling

-- ---- from OAI.Probability.CriticalZ3.Resampling ----
namespace OAI

universe uI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

open scoped BigOperators Matrix
open Filter

namespace FiniteResampling
variable {I : Type uI} [Fintype I] [Nonempty I]

theorem lower_le (f : I → ℝ) (i : I) : lower f ≤ f i :=
  Finset.inf'_le f (Finset.mem_univ i)
theorem le_upper (f : I → ℝ) (i : I) : f i ≤ upper f :=
  Finset.le_sup' f (Finset.mem_univ i)
namespace Transition
variable (K : Transition I)
/-- Subtracting the same atom from each row exposes a nonnegative remainder. -/
theorem common_atom_bounds (z : I) (a : ℝ) (ha : ∀ i, a ≤ K.weight i z)
    (f : I → ℝ) (i : I) :
    a * f z + (1-a) * lower f ≤ K.act f i ∧
      K.act f i ≤ a * f z + (1-a) * upper f := by
  classical
  let r : I → ℝ := fun j => K.weight i j - if j = z then a else 0
  have hr : ∀ j, 0 ≤ r j := by
    intro j
    dsimp [r]
    split_ifs with h
    · subst j; exact sub_nonneg.mpr (ha i)
    · simpa using K.nonneg i j
  have hsum : ∑ j, r j = 1-a := by simp [r, Finset.sum_sub_distrib, K.total]
  have heq : K.act f i = a * f z + ∑ j, r j * f j := by
    simp [act, r, sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [heq]
  constructor
  · apply add_le_add le_rfl
    rw [← hsum, Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (lower_le f j) (hr j))
  · apply add_le_add le_rfl
    rw [← hsum, Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (le_upper f j) (hr j))

end Transition
end FiniteResampling

end OAI

-- ---- platform node ----
open OAI OAI.FiniteResampling OAI.FiniteResampling.Transition
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
open scoped BigOperators Matrix
open Filter


theorem solution.{uI} : type_of% @_root_.OAI.FiniteResampling.Transition.common_atom_bounds.{uI} := @_root_.OAI.FiniteResampling.Transition.common_atom_bounds.{uI}
