-- Prove2me | solution 2 for OAI.Problem356.isSmoothCompactProbabilityDensity_sum_disjoint_squares
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:04:45.548996+00:00
-- url     : https://prove2.me/submissions/72221d85-ff0e-4d74-9b6e-204e0108d612

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/DisjointSquares.lean:L50-L83
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.isSmoothCompactProbabilityDensity_sum_disjoint_squares. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Theorems.Thm_OAI_Problem356_sqrt_sum_disjoint_squares

-- ---- from OAI.Analysis.CoulombTransport.DisjointSquares ----
namespace OAI

universe uIndex uX

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem356

/-- A finite disjoint family of smooth compactly supported nonnegative square
roots yields a density satisfying both smoothness requirements of the target. -/
theorem isSmoothCompactProbabilityDensity_sum_disjoint_squares {ι : Type uIndex}
    (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hsm : ∀ i ∈ s, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hcs : ∀ i ∈ s, HasCompactSupport (g i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hmass : (∫ x : E3, (∑ i ∈ s, a i * (g i x) ^ 2)
      ∂(volume : Measure E3)) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) := by
  have hsqrt : (fun x => Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2)) =
      (fun x => ∑ i ∈ s, Real.sqrt (a i) * g i x) := by
    funext x
    exact sqrt_sum_disjoint_squares s a g ha hg hd x
  refine ⟨?_, ?_, ?_, ?_, ?_, hmass⟩
  · intro x
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))
  · exact ContDiff.sum (fun i hi => contDiff_const.mul ((hsm i hi).pow 2))
  · have hterm : ∀ i ∈ s, HasCompactSupport (fun x => a i * (g i x) ^ 2) := by
      intro i hi
      simpa only [Function.comp_def] using
        (hcs i hi).comp_left (g := fun y : ℝ => a i * y ^ 2) (by simp)
    simpa only [Finset.sum_fn] using HasCompactSupport.finset_sum hterm
  · rw [hsqrt]
    exact ContDiff.sum (fun i hi => contDiff_const.mul (hsm i hi))
  · rw [hsqrt]
    have hterm : ∀ i ∈ s, HasCompactSupport (fun x => Real.sqrt (a i) * g i x) := by
      intro i hi
      simpa only [Function.comp_def] using
        (hcs i hi).comp_left (g := fun y : ℝ => Real.sqrt (a i) * y) (by simp)
    simpa only [Finset.sum_fn] using HasCompactSupport.finset_sum hterm

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.Problem356.isSmoothCompactProbabilityDensity_sum_disjoint_squares.{uIndex} := @_root_.OAI.Problem356.isSmoothCompactProbabilityDensity_sum_disjoint_squares.{uIndex}
