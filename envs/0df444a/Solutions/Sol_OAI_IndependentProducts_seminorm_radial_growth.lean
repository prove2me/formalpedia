-- Prove2me | solution 1 for OAI.IndependentProducts.seminorm_radial_growth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:56:42.707805+00:00
-- url     : https://prove2.me/submissions/521aea63-19e7-4461-8ebe-48beacd306a3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/TreeObstruction.lean:L103-L118
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.seminorm_radial_growth. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction

-- ---- from OAI.Analysis.ProductSpaces.TreeObstruction ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uX

namespace IndependentProducts

section AbstractObstruction

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

end AbstractObstruction
end IndependentProducts

namespace IndependentProducts
section RadialGrowth
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Convexity extends a positive one-sided gain from one radius to every larger radius. -/
lemma seminorm_radial_growth (N : Seminorm ℝ X) {x w : X} (hx : N x = 1)
    {t r γ : ℝ} (ht : 0 < t) (htr : t ≤ r) (hγ : 0 ≤ γ)
    (hg : 1 + γ ≤ N (x + t • w)) : 1 + γ ≤ N (x + r • w) := by
  have hr : 0 < r := ht.trans_le htr
  have hq : 0 < t / r := div_pos ht hr
  have hq1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  have hcomb : (t / r) • (x + r • w) + (1 - t / r) • x = x + t • w := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ hr.ne']
    module
  have hh := map_add_le_add N ((t / r) • (x + r • w)) ((1 - t / r) • x)
  rw [hcomb, map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hq, abs_of_nonneg (sub_nonneg.mpr hq1), hx] at hh
  have hm := mul_nonneg (sub_nonneg.mpr hq1) hγ
  have : (t / r) * (1 + γ) ≤ (t / r) * N (x + r • w) := by nlinarith
  exact (mul_le_mul_iff_right₀ hq).mp this

end RadialGrowth
end IndependentProducts

namespace IndependentProducts
section TreeObstruction
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

end TreeObstruction
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uX
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem solution (N : Seminorm ℝ X) {x w : X} (hx : N x = 1)
    {t r γ : ℝ} (ht : 0 < t) (htr : t ≤ r) (hγ : 0 ≤ γ)
    (hg : 1 + γ ≤ N (x + t • w)) : 1 + γ ≤ N (x + r • w) := by
  first
    | exact OAI.IndependentProducts.seminorm_radial_growth N hx ht htr hγ hg
    | exact OAI.IndependentProducts.seminorm_radial_growth
    | (apply OAI.IndependentProducts.seminorm_radial_growth <;> assumption)
    | (intros; apply OAI.IndependentProducts.seminorm_radial_growth <;> assumption)
