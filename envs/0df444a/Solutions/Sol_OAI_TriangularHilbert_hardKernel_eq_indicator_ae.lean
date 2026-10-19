-- Prove2me | solution 1 for OAI.TriangularHilbert.hardKernel_eq_indicator_ae
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:00:45.60308+00:00
-- url     : https://prove2.me/submissions/4add737d-e41e-4317-a9eb-b226cee5345a

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_Quantization
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridLine
import Definitions.Def_OAI_Analysis_TriangularHilbert_BoundedBox
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledOutput
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicSlice
import Definitions.Def_OAI_Analysis_TriangularHilbert_RationalSup
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteDual
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscreteMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicMaxMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicHomogeneity
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicNorm
import Definitions.Def_OAI_Analysis_TriangularHilbert_Coordinates

open OAI OAI.TriangularHilbert
open MeasureTheory MeasureTheory.Measure Heat
open scoped ENNReal


theorem solution {r R : ℝ} (hR : r ≤ R) :
    (fun t => hardKernel r R t) =ᵐ[volume]
      (annulus r R).indicator (fun t : ℝ => 1/t) := by
  have hc : ({R, -R} : Set ℝ).Countable := (Set.toFinite _).countable
  filter_upwards [hc.ae_notMem volume] with t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
  have hne : |t| ≠ R := by
    intro h
    rcases abs_choice t with h' | h'
    · exact ht.1 (by linarith)
    · exact ht.2 (by linarith)
  unfold hardKernel annulus
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : ¬ R < |t| := not_lt.mpr hlt.le
    by_cases h1 : r < |t|
    · simp [Set.indicator, h1, hlt, this]
    · simp [Set.indicator, h1, this]
  · have h1 : r < |t| := lt_of_le_of_lt hR hgt
    have : ¬ |t| < R := not_lt.mpr hgt.le
    simp [Set.indicator, h1, hgt, this]

