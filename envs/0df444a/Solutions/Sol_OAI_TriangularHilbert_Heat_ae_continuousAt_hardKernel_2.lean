-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.ae_continuousAt_hardKernel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:14:40.319406+00:00
-- url     : https://prove2.me/submissions/8b3d7f12-e181-4a7a-b230-1e06ba6d163f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SampledConvergence.lean:L58-L70
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.ae_continuousAt_hardKernel. The node keeps its source
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

-- ---- from OAI.Analysis.TriangularHilbert.HardScalar ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma continuousAt_absStep (r t : ℝ) (ht : |t| ≠ r) :
    ContinuousAt (fun x : ℝ => if r < |x| then (1:ℝ) else 0) t := by
  rcases lt_or_gt_of_ne ht with h|h
  · have he : ∀ᶠ x in 𝓝 t, |x| < r := continuous_abs.continuousAt.eventually (eventually_lt_nhds h)
    apply (show ContinuousAt (fun _ : ℝ => (0:ℝ)) t from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with x hx
    simp only [not_lt.mpr hx.le,ite_false]
  · have he : ∀ᶠ x in 𝓝 t, r < |x| := continuous_abs.continuousAt.eventually (eventually_gt_nhds h)
    apply (show ContinuousAt (fun _ : ℝ => (1:ℝ)) t from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with x hx
    simp only [hx,ite_true]

lemma continuousAt_hardKernel (r R t : ℝ) (ht0 : t ≠ 0) (htr : |t| ≠ r) (htR : |t| ≠ R) :
    ContinuousAt (hardKernel r R) t :=
  ((continuousAt_absStep r t htr).sub (continuousAt_absStep R t htR)).div continuousAt_id ht0
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SampledConvergence ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma ae_continuousAt_hardKernel (r R a : ℝ) : ∀ᵐ c : ℝ, ContinuousAt (hardKernel r R) (a+c) := by
  have hne (x : ℝ) : ∀ᵐ c : ℝ, c ≠ x := by simp [ae_iff]
  filter_upwards [hne (-a),hne (r-a),hne (-r-a),hne (R-a),hne (-R-a)] with c h0 h1 h2 h3 h4
  apply continuousAt_hardKernel
  · intro he; apply h0; linarith
  · intro he
    rcases eq_or_eq_neg_of_abs_eq he with he|he
    · apply h1; linarith
    · apply h2; linarith
  · intro he
    rcases eq_or_eq_neg_of_abs_eq he with he|he
    · apply h3; linarith
    · apply h4; linarith
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.ae_continuousAt_hardKernel := @_root_.OAI.TriangularHilbert.Heat.ae_continuousAt_hardKernel
