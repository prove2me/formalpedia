-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.finite_cost_dissipation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:55:54.035879+00:00
-- url     : https://prove2.me/submissions/f638bf36-4fad-4544-bd93-4ff2ae0116b8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/DissipationAlgebra.lean:L10-L47
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.finite_cost_dissipation. The node keeps its source
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

-- ---- from OAI.Analysis.TriangularHilbert.DissipationAlgebra ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators

lemma finite_cost_dissipation (α : Three → ℝ) (hα : ∀ w, 0 ≤ α w)
    (K : Three → Three → ℝ) (Z : Three → ℝ) (hK : ∀ v w, 0 ≤ K v w)
    (hrow : ∀ v, 2*Z v ≤ ∑ w, if w = v then 0 else K v w)
    (hcol : ∀ w, (∑ v, if v = w then 0 else K v w) ≤ Real.sqrt 2 * K w w) :
    (∑ v, ((∑ w, α w)*Z v - (∑ w, α w*K v w))) ≤
      ∑ w, (-α w + Real.sqrt 2 * max 0 ((∑ v, α v)/2-α w))*K w w := by
  let S := ∑ w, α w
  have hS : 0 ≤ S := Finset.sum_nonneg (fun w _ => hα w)
  have hr v : S*Z v ≤ S/2 * ∑ w, if w = v then 0 else K v w := by
    have hh := mul_le_mul_of_nonneg_left (hrow v) (show 0 ≤ S/2 by positivity)
    nlinarith
  have hc w : (S/2-α w)*(∑ v, if v = w then 0 else K v w) ≤
      Real.sqrt 2 * max 0 (S/2-α w)*K w w := by
    have ho : 0 ≤ ∑ v, if v = w then 0 else K v w :=
      Finset.sum_nonneg (fun v _ => by split_ifs; exact le_refl 0; exact hK v w)
    calc
      _ ≤ max 0 (S/2-α w)*(∑ v, if v = w then 0 else K v w) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) ho
      _ ≤ max 0 (S/2-α w)*(Real.sqrt 2*K w w) :=
        mul_le_mul_of_nonneg_left (hcol w) (le_max_left _ _)
      _ = _ := by ring
  calc
    _ ≤ ∑ v, (S/2*(∑ w, if w = v then 0 else K v w) - (∑ w, α w*K v w)) := by
      apply Finset.sum_le_sum
      intro v _
      exact sub_le_sub_right (hr v) _
    _ = ∑ w, (-α w*K w w + (S/2-α w)*(∑ v, if v = w then 0 else K v w)) := by
      simp [Fin.sum_univ_three]
      ring
    _ ≤ ∑ w, (-α w*K w w + Real.sqrt 2 * max 0 (S/2-α w)*K w w) := by
      apply Finset.sum_le_sum
      intro w _
      exact add_le_add (le_refl _) (hc w)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      dsimp [S]
      ring

end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.finite_cost_dissipation := @_root_.OAI.TriangularHilbert.Heat.finite_cost_dissipation
