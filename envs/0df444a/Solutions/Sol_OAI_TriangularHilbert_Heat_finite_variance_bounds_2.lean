-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.finite_variance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:46:30.28493+00:00
-- url     : https://prove2.me/submissions/7f6e0783-debb-4bdd-b306-ca481d5104fb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/PlaneIntegral.lean:L54-L66
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.finite_variance_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral

-- ---- from OAI.Analysis.TriangularHilbert.PlaneIntegral ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma finite_variance_bounds (σ : Three → ℝ) (hσ : ∀ w, 0 < σ w) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ (∀ w, a ≤ σ w) ∧ (∀ w, σ w ≤ b) := by
  let a := min (σ 0) (min (σ 1) (σ 2))
  let b := σ 0 + σ 1 + σ 2
  have ha : 0 < a := lt_min (hσ 0) (lt_min (hσ 1) (hσ 2))
  have hlo : ∀ w, a ≤ σ w := by
    intro w; fin_cases w
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hhi : ∀ w, σ w ≤ b := by
    intro w; fin_cases w <;> dsimp [b] <;> linarith [hσ 0,hσ 1,hσ 2]
  exact ⟨a,b,ha,(hlo 0).trans (hhi 0),hlo,hhi⟩

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.finite_variance_bounds := @_root_.OAI.TriangularHilbert.Heat.finite_variance_bounds
