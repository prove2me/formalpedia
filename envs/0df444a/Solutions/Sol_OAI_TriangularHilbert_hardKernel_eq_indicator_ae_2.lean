-- Prove2me | solution 2 for OAI.TriangularHilbert.hardKernel_eq_indicator_ae
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:34:32.582877+00:00
-- url     : https://prove2.me/submissions/8e80d509-4d36-4115-9beb-3977f04fce82

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Coordinates.lean:L45-L65
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.hardKernel_eq_indicator_ae. The node keeps its source
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

-- ---- from OAI.Analysis.TriangularHilbert.Coordinates ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory MeasureTheory.Measure Heat
open scoped ENNReal
noncomputable section

lemma hardKernel_eq_indicator_ae {r R : ℝ} (hR : r ≤ R) :
    (fun t => hardKernel r R t) =ᵐ[volume]
      (annulus r R).indicator (fun t : ℝ => 1/t) := by
  have hne (x : ℝ) : ∀ᵐ t : ℝ, t ≠ x := by simp [ae_iff]
  filter_upwards [hne R,hne (-R)] with t ht1 ht2
  have ht : |t| ≠ R := by
    intro he
    rcases eq_or_eq_neg_of_abs_eq he with he|he
    · exact ht1 he
    · exact ht2 he
  classical
  by_cases h1 : r < |t|
  · by_cases h2 : |t| < R
    · simp only [hardKernel,h1,ite_true,not_lt.mpr h2.le,ite_false,sub_zero,
        Set.indicator_of_mem (show t ∈ annulus r R from ⟨h1,h2⟩)]
    · have h3 : R < |t| := lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm ht)
      simp only [hardKernel,h1,h3,ite_true,sub_self,zero_div,
        Set.indicator_of_notMem (show t ∉ annulus r R from fun h => h2 h.2)]
  · have h2 : ¬ R < |t| := not_lt.mpr ((le_of_not_gt h1).trans hR)
    simp only [hardKernel,h1,h2,ite_false,sub_self,zero_div,
      Set.indicator_of_notMem (show t ∉ annulus r R from fun h => h1 h.1)]

end
end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open MeasureTheory MeasureTheory.Measure Heat
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.TriangularHilbert.hardKernel_eq_indicator_ae := @_root_.OAI.TriangularHilbert.hardKernel_eq_indicator_ae
