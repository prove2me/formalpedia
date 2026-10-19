-- Prove2me | solution 2 for OAI.Problem356.isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:06:44.356981+00:00
-- url     : https://prove2.me/submissions/73f6e6dd-bc54-4887-9257-193cf095b370

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/DisjointSquares.lean:L85-L113
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Theorems.Thm_OAI_Problem356_isSmoothCompactProbabilityDensity_sum_disjoint_squares

-- ---- from OAI.Analysis.CoulombTransport.DisjointSquares ----
namespace OAI

universe uIndex uX

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem356

/-- Convenient normalization form for the five component densities: every
square has unit mass, and the component weights sum to one. -/
theorem isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
    {ι : Type uIndex} (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hsm : ∀ i ∈ s, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hcs : ∀ i ∈ s, HasCompactSupport (g i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hgint : ∀ i ∈ s, (∫ x : E3, (g i x) ^ 2 ∂(volume : Measure E3)) = 1)
    (haint : (∑ i ∈ s, a i) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) := by
  apply isSmoothCompactProbabilityDensity_sum_disjoint_squares s a g ha hg hsm hcs hd
  have hint : ∀ i ∈ s, Integrable (fun x => a i * (g i x) ^ 2)
      (volume : Measure E3) := by
    intro i hi
    have hcomp : HasCompactSupport (fun x => (g i x) ^ 2) := by
      simpa only [Function.comp_def] using
        (hcs i hi).comp_left (g := fun y : ℝ => y ^ 2) (by simp)
    exact ((hsm i hi).continuous.pow 2).integrable_of_hasCompactSupport hcomp |>.const_mul (a i)
  rw [integral_finsetSum s hint]
  calc
    (∑ i ∈ s, ∫ x : E3, a i * (g i x) ^ 2 ∂(volume : Measure E3)) =
        ∑ i ∈ s, a i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul, hgint i hi, mul_one]
    _ = 1 := haint

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.Problem356.isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares.{uIndex} := @_root_.OAI.Problem356.isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares.{uIndex}
