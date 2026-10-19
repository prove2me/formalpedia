-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.hasDerivAt_integral_compact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:05:47.051544+00:00
-- url     : https://prove2.me/submissions/ca2859c9-538e-4f1c-8c7b-017098a325ad

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/CompactIntegrals.lean:L46-L71
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.hasDerivAt_integral_compact. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals

-- ---- from OAI.Analysis.DirectCrouzeix.CompactIntegrals ----
namespace OAI

universe u_87 u_88 u_89 u_90 u_91 u_92 u_93

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem integrable_of_continuous_compact {α : Type u_87} {E : Type u_88} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem hasDerivAt_integral_compact {α : Type u_92} {E : Type u_93}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [CompactSpace α] [SecondCountableTopology α]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) [IsFiniteMeasure μ] {s : Set ℂ} (hs : IsOpen s)
    {f f' : ℂ → α → E}
    (hf : ContinuousOn f.uncurry (s ×ˢ univ))
    (hf' : ContinuousOn f'.uncurry (s ×ˢ univ))
    (hd : ∀ z ∈ s, ∀ t, HasDerivAt (fun w => f w t) (f' z t) z)
    {z : ℂ} (hz : z ∈ s) :
    HasDerivAt (fun w => ∫ t, f w t ∂μ) (∫ t, f' z t ∂μ) z := by
  obtain ⟨ε,hε,hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hz)
  have hcf (w : ℂ) (hw : w ∈ s) : Continuous (f w) := by
    exact hf.comp_continuous (continuous_const.prodMk continuous_id) (fun t => ⟨hw,mem_univ _⟩)
  have hcf' (w : ℂ) (hw : w ∈ s) : Continuous (f' w) := by
    exact hf'.comp_continuous (continuous_const.prodMk continuous_id) (fun t => ⟨hw,mem_univ _⟩)
  obtain ⟨B,hB⟩ := ((isCompact_closedBall z ε).prod isCompact_univ).exists_bound_of_continuousOn
    (hf'.mono (prod_mono hsub Subset.rfl))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := closedBall z ε) (bound := fun _ => B) (closedBall_mem_nhds z hε)
    ?_ (integrable_of_continuous_compact μ (hcf z hz))
    (hcf' z hz).aestronglyMeasurable ?_ (integrable_const B) ?_).2
  · filter_upwards [hs.mem_nhds hz] with w hw
    exact (hcf w hw).aestronglyMeasurable
  · exact ae_of_all μ (fun t w hw => hB (w,t) ⟨hw,mem_univ _⟩)
  · exact ae_of_all μ (fun t w hw => hd w (hsub hw) t)

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.hasDerivAt_integral_compact := @_root_.OAI.DirectCrouzeix.Faber.hasDerivAt_integral_compact
