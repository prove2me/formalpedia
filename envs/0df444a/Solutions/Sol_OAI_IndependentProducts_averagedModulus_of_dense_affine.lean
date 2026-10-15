-- Prove2me | solution 1 for OAI.IndependentProducts.averagedModulus_of_dense_affine
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:20:43.299406+00:00
-- url     : https://prove2.me/submissions/3f1309ad-a510-4b78-b75b-1d9920ce5961

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/MidpointModulus.lean:L129-L153
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.averagedModulus_of_dense_affine. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Theorems.Thm_OAI_IndependentProducts_averagedModulus_lower_of_approx

-- ---- from OAI.Analysis.ProductSpaces.MidpointModulus ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uX

namespace IndependentProducts
section MidpointGeometry
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma midpointGain_center_bound (t : ℝ) (x u y : X) :
    midpointGain t u y - 2 * ‖x - u‖ ≤ midpointGain t x y := by
  have hp := norm_add_le (x + t • y) (u - x)
  have hm := norm_add_le (x - t • y) (u - x)
  have hc := norm_add_le u (x - u)
  have ep : (x + t • y) + (u - x) = u + t • y := by abel
  have em : (x - t • y) + (u - x) = u - t • y := by abel
  rw [ep, norm_sub_rev u x] at hp
  rw [em, norm_sub_rev u x] at hm
  rw [add_sub_cancel] at hc
  unfold midpointGain
  linarith

lemma averagedModulus_of_dense_affine (hdim : ¬ FiniteDimensional ℝ X)
    {D : Set X} (hD : Dense D) (A B t : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ u ∈ D, ∃ F ∈ CofiniteSubspaces X,
      ∀ y ∈ F, A * ‖y‖ - B * ‖u‖ ≤ midpointGain t u y) :
    A - B ≤ averagedMidpointModulus X (normSeminorm ℝ X) t := by
  apply averagedModulus_lower_of_approx hdim t (A - B)
  intro x hx ε hε
  have hd : 0 < ε / (B + 2) := div_pos hε (by linarith)
  obtain ⟨u, huD, hxu⟩ := Metric.mem_closure_iff.mp (hD x) (ε / (B + 2)) hd
  rw [dist_eq_norm] at hxu
  obtain ⟨F, hF, hFy⟩ := h u huD
  refine ⟨F, hF, ?_⟩
  intro y hy hn
  have hc := midpointGain_center_bound t x u y
  have hag := hFy y hy
  have hAyn := mul_le_mul_of_nonneg_left hn hA
  have hnorm : ‖u‖ ≤ 1 + ‖x - u‖ := by
    have hr := norm_sub_le x (x - u)
    rw [sub_sub_cancel, hx] at hr
    exact hr
  have hBn := mul_le_mul_of_nonneg_left hnorm hB
  have hεn : (B + 2) * ‖x - u‖ < ε := by
    have hh := (lt_div_iff₀ (by linarith : 0 < B + 2)).mp hxu
    nlinarith
  nlinarith

end MidpointGeometry
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uX
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem solution (hdim : ¬ FiniteDimensional ℝ X)
    {D : Set X} (hD : Dense D) (A B t : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ u ∈ D, ∃ F ∈ CofiniteSubspaces X,
      ∀ y ∈ F, A * ‖y‖ - B * ‖u‖ ≤ midpointGain t u y) :
    A - B ≤ averagedMidpointModulus X (normSeminorm ℝ X) t := by
  first
    | exact OAI.IndependentProducts.averagedModulus_of_dense_affine hdim hD A B t hA hB h
    | exact OAI.IndependentProducts.averagedModulus_of_dense_affine
    | (apply OAI.IndependentProducts.averagedModulus_of_dense_affine <;> assumption)
    | (intros; apply OAI.IndependentProducts.averagedModulus_of_dense_affine <;> assumption)
