-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.planeIntegral_weight_slice
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:20:08.281984+00:00
-- url     : https://prove2.me/submissions/3895a0a1-9060-48f7-9625-c216f6284cce

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/WeightSlice.lean:L28-L43
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.planeIntegral_weight_slice. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Theorems.Thm_OAI_TriangularHilbert_Heat_weight_three_integrable

-- ---- from OAI.Analysis.TriangularHilbert.WeightSlice ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

lemma planeIntegral_weight_slice {h : ℝ} (hh : 0 < h) (a b d : ℝ)
    (c f : ι → ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p v) (σ v)) d =
      ∑ m, f m*planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h (c m) (p v) (σ v)) d := by
  unfold planeIntegral
  have he (z : ℝ×ℝ) : weight h a (chart 2 d z 0) (σ 0)*weight h b (chart 2 d z 1) (σ 1)*
      (∑ m, f m*weight h (c m) (chart 2 d z v) (σ v)) =
      ∑ m, f m*(weight h a (chart 2 d z 0) (σ 0)*weight h b (chart 2 d z 1) (σ 1)*weight h (c m) (chart 2 d z v) (σ v)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun m _ => (weight_three_integrable hh a b (c m) d σ hσ v).const_mul (f m))]
  simp only [integral_const_mul]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.planeIntegral_weight_slice.{uι} := @_root_.OAI.TriangularHilbert.Heat.planeIntegral_weight_slice.{uι}
