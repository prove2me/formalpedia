-- Prove2me | solution 1 for OAI.IndependentProducts.weaklyNull_approx_cofinite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:54:15.24397+00:00
-- url     : https://prove2.me/submissions/e986b304-77bf-451a-8ef5-3bb0ceca4ded

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/TreeObstruction.lean:L35-L56
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.weaklyNull_approx_cofinite. The node keeps its source
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

lemma weaklyNull_tendsto_finiteDimensional [FiniteDimensional ℝ X]
    {u : ℕ → X} (hu : WeaklyNull u) : Tendsto u atTop (𝓝 0) := by
  let e := (Module.finBasis ℝ X).equivFunL
  have he : Tendsto (fun n => e (u n)) atTop (𝓝 (e 0)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa using hu ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap)
  have h := (e.symm.continuous.tendsto (e 0)).comp he
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, map_zero] using h

/-- A weakly null sequence approaches every closed finite-codimensional subspace in norm. -/
lemma weaklyNull_approx_cofinite {u : ℕ → X} (hu : WeaklyNull u)
    (F : Submodule ℝ X) (hF : F ∈ CofiniteSubspaces X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ z ∈ F, ‖u n - z‖ < ε := by
  let : IsClosed (F : Set X) := hF.1
  let : FiniteDimensional ℝ (X ⧸ F) := hF.2
  have hquot : Tendsto (fun n => F.mkQL (u n)) atTop (𝓝 0) :=
    weaklyNull_tendsto_finiteDimensional (fun f => by simpa using hu (f.comp F.mkQL))
  have he : ∀ᶠ n in atTop, ‖F.mkQL (u n)‖ < ε / 2 := by
    have hn := hquot.norm
    simp only [norm_zero] at hn
    exact hn.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  filter_upwards [he] with n hn
  obtain ⟨w, hw, hnw⟩ := Submodule.Quotient.norm_mk_lt (F.mkQL (u n))
    (by linarith : (0 : ℝ) < ε / 2)
  refine ⟨u n - w, ?_, ?_⟩
  · apply (Submodule.Quotient.mk_eq_zero F).mp
    change F.mkQ (u n - w) = 0
    rw [map_sub]
    change F.mkQL (u n) - Submodule.Quotient.mk w = 0
    rw [hw, sub_self]
  · simpa only [sub_sub_cancel] using hnw.trans_le (by linarith)

end AbstractObstruction
end IndependentProducts

namespace IndependentProducts
section RadialGrowth
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

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

theorem solution {u : ℕ → X} (hu : WeaklyNull u)
    (F : Submodule ℝ X) (hF : F ∈ CofiniteSubspaces X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ z ∈ F, ‖u n - z‖ < ε := by
  first
    | exact OAI.IndependentProducts.weaklyNull_approx_cofinite hu F hF hε
    | exact OAI.IndependentProducts.weaklyNull_approx_cofinite
    | (apply OAI.IndependentProducts.weaklyNull_approx_cofinite <;> assumption)
    | (intros; apply OAI.IndependentProducts.weaklyNull_approx_cofinite <;> assumption)
