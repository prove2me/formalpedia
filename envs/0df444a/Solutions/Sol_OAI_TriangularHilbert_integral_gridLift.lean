-- Prove2me | solution 1 for OAI.TriangularHilbert.integral_gridLift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:08:45.477975+00:00
-- url     : https://prove2.me/submissions/b7556e79-5347-49a9-9162-8be7e597baa4

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

open OAI OAI.TriangularHilbert
universe uE uF
open MeasureTheory
open scoped BigOperators


theorem solution (D : Finset ℤ) (h : ℝ) {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : D → D → E) (hh : 0 ≤ h) :
    (∫ z : ℝ×ℝ, gridLift D h f z) = ∑ i, ∑ j, h^2 • f i j := by
  have hms : ∀ i j : ℤ, MeasurableSet (gridRect h i j) := fun i j =>
    (measurableSet_Ico).prod measurableSet_Ico
  have hvol : ∀ i j : ℤ, volume (gridRect h i j) = ENNReal.ofReal (h^2) := by
    intro i j
    rw [gridRect, Measure.volume_eq_prod, Measure.prod_prod, gridCell, gridCell, Real.volume_Ico,
      Real.volume_Ico, ← ENNReal.ofReal_mul (by nlinarith)]
    congr 1; ring
  have hfin : ∀ i j : ℤ, volume (gridRect h i j) ≠ ⊤ := fun i j => by rw [hvol]; exact ENNReal.ofReal_ne_top
  unfold gridLift
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [integral_indicator_const _ (hms _ _), Measure.real, hvol, ENNReal.toReal_ofReal (by positivity)]
    · intro j _
      exact (integrableOn_const (C := f i j) (hfin _ _) enorm_ne_top).integrable_indicator (hms _ _)
  · intro i _
    refine integrable_finset_sum _ (fun j _ => ?_)
    exact (integrableOn_const (C := f i j) (hfin _ _) enorm_ne_top).integrable_indicator (hms _ _)

