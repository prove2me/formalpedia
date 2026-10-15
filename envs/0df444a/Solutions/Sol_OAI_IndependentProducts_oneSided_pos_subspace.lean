-- Prove2me | solution 1 for OAI.IndependentProducts.oneSided_pos_subspace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:55:21.035689+00:00
-- url     : https://prove2.me/submissions/094f94a9-cf35-4917-b4c9-7d467c5d1742

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/TreeObstruction.lean:L58-L89
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.oneSided_pos_subspace. The node keeps its source
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

/-- The elementary consequence of positivity of the *actual* inf-sup-inf modulus. -/
lemma oneSided_pos_subspace (N : Seminorm ℝ X) {t : ℝ}
    (hδ : 0 < oneSidedModulus X N t) {x : X} (hx : N x = 1) :
    ∃ F ∈ CofiniteSubspaces X, ∀ y ∈ F, N y = 1 →
      1 + oneSidedModulus X N t / 2 ≤ N (x + t • y) := by
  let directions (F : Submodule ℝ X) :=
    {b : ℝ | ∃ y : X, y ∈ F ∧ N y = 1 ∧ b = N (x + t • y) - 1}
  let centers := {r : ℝ | ∃ x : X, N x = 1 ∧ r =
    sSup {a | ∃ F ∈ CofiniteSubspaces X, a =
      sInf {b | ∃ y : X, y ∈ F ∧ N y = 1 ∧ b = N (x + t • y) - 1}}}
  have hbelow : BddBelow centers := by
    by_contra h
    have hz := Real.sInf_of_not_bddBelow h
    change oneSidedModulus X N t = 0 at hz
    linarith
  have hcenter : oneSidedModulus X N t ≤
      sSup {a | ∃ F ∈ CofiniteSubspaces X, a = sInf (directions F)} :=
    csInf_le hbelow ⟨x, hx, rfl⟩
  have hnonempty : {a | ∃ F ∈ CofiniteSubspaces X, a = sInf (directions F)}.Nonempty := by
    refine ⟨_, ⊤, ?_, rfl⟩
    exact ⟨isClosed_univ, inferInstance⟩
  obtain ⟨a, ⟨F, hF, rfl⟩, ha⟩ := exists_lt_of_lt_csSup hnonempty
    (lt_of_lt_of_le (by linarith : oneSidedModulus X N t / 2 < oneSidedModulus X N t)
      hcenter)
  refine ⟨F, hF, ?_⟩
  intro y hy hNy
  have hd : BddBelow (directions F) := by
    refine ⟨-1, ?_⟩
    rintro b ⟨z, hz, hNz, rfl⟩
    linarith [apply_nonneg N (x + t • z)]
  have hle := csInf_le hd (show N (x + t • y) - 1 ∈ directions F from ⟨y, hy, hNy, rfl⟩)
  linarith

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

theorem solution (N : Seminorm ℝ X) {t : ℝ}
    (hδ : 0 < oneSidedModulus X N t) {x : X} (hx : N x = 1) :
    ∃ F ∈ CofiniteSubspaces X, ∀ y ∈ F, N y = 1 →
      1 + oneSidedModulus X N t / 2 ≤ N (x + t • y) := by
  first
    | exact OAI.IndependentProducts.oneSided_pos_subspace N hδ hx
    | exact OAI.IndependentProducts.oneSided_pos_subspace
    | (apply OAI.IndependentProducts.oneSided_pos_subspace <;> assumption)
    | (intros; apply OAI.IndependentProducts.oneSided_pos_subspace <;> assumption)
