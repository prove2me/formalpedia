-- Prove2me | solution 2 for OAI.TriangularHilbert.integral_gridLift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:02:21.692197+00:00
-- url     : https://prove2.me/submissions/bd260705-fc27-4602-8b4b-cee706c60be2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/GridCell.lean:L101-L116
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.integral_gridLift. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridCell

-- ---- from OAI.Analysis.TriangularHilbert.GridCell ----
namespace OAI

universe uE uF

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma volume_gridCell (h : ℝ) (i : ℤ) : volume (gridCell h i) = ENNReal.ofReal h := by
  rw [gridCell,Real.volume_Ico]
  congr 1
  ring

lemma measurableSet_gridRect (h : ℝ) (i j : ℤ) : MeasurableSet (gridRect h i j) :=
  measurableSet_Ico.prod measurableSet_Ico

lemma volume_gridRect (h : ℝ) (i j : ℤ) : volume (gridRect h i j) = (ENNReal.ofReal h)^2 := by
  change (volume.prod volume) (gridCell h i ×ˢ gridCell h j) = _
  rw [Measure.prod_prod,volume_gridCell,volume_gridCell,pow_two]

lemma integral_gridLift (D : Finset ℤ) (h : ℝ) {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : D → D → E) (hh : 0 ≤ h) :
    (∫ z : ℝ×ℝ, gridLift D h f z) = ∑ i, ∑ j, h^2 • f i j := by
  have hi (i j : D) : Integrable ((gridRect h i j).indicator (fun _ : ℝ×ℝ => f i j)) :=
    IntegrableOn.integrable_indicator
      (integrableOn_const (μ := volume) (s := gridRect h i j) (C := f i j)
        (by rw [volume_gridRect]; finiteness)) (measurableSet_gridRect h i j)
  unfold gridLift
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator (measurableSet_gridRect h i j),setIntegral_const,measureReal_def,volume_gridRect,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hh]
end
end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open MeasureTheory
open scoped BigOperators


theorem solution.{uE} : type_of% @_root_.OAI.TriangularHilbert.integral_gridLift.{uE} := @_root_.OAI.TriangularHilbert.integral_gridLift.{uE}
