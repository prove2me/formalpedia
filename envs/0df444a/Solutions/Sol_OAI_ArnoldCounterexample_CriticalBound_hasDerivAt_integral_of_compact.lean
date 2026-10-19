-- Prove2me | solution 1 for OAI.ArnoldCounterexample.CriticalBound.hasDerivAt_integral_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:48:40.399119+00:00
-- url     : https://prove2.me/submissions/23ee4e04-a5d1-4d00-ad57-3af6a2499e3d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Haar.lean:L16-L37
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.CriticalBound.hasDerivAt_integral_of_compact. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar

-- ---- from OAI.Geometry.Arnold.Haar ----
namespace OAI

universe uG

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter

open scoped BigOperators
open MeasureTheory Set Filter

namespace ArnoldCounterexample.CriticalBound

/-- Compactness supplies the uniform domination needed to differentiate a
parameter integral. This gives differentiation under the Haar integral. -/
theorem hasDerivAt_integral_of_compact
    {G : Type uG} [TopologicalSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasure μ]
    {F F' : ℝ → G → ℝ}
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ t g, HasDerivAt (fun s ↦ F s g) (F' t g) t) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ g, F s g ∂μ) (∫ g, F' t g ∂μ) t := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set G))).exists_bound_of_continuousOn
    (hF'.continuousOn : ContinuousOn (Function.uncurry F') (Icc (t - 1) (t + 1) ×ˢ univ))
  have hcont (s : ℝ) : Continuous (F s) := hF.comp (continuous_const.prodMk continuous_id)
  have hcont' (s : ℝ) : Continuous (F' s) := hF'.comp (continuous_const.prodMk continuous_id)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Icc (t - 1) (t + 1)) (bound := fun _ : G ↦ C) ?_ ?_ ?_
    (hcont' t).aestronglyMeasurable ?_ (integrable_const C) ?_).2
  · exact Icc_mem_nhds (by linarith) (by linarith)
  · exact Filter.Eventually.of_forall (fun s ↦ (hcont s).aestronglyMeasurable)
  · exact (hcont t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact Filter.Eventually.of_forall (fun g s hs ↦ hC (s, g) ⟨hs, mem_univ g⟩)
  · exact Filter.Eventually.of_forall (fun g s _ ↦ hd s g)

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound

end ArnoldCounterexample.CriticalBound

open scoped Matrix.Norms.Operator ContDiff

namespace ArnoldCounterexample.CriticalBound

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instContinuousStarRM
end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped BigOperators
open MeasureTheory Set Filter


theorem solution.{uG} : type_of% @_root_.OAI.ArnoldCounterexample.CriticalBound.hasDerivAt_integral_of_compact.{uG} := @_root_.OAI.ArnoldCounterexample.CriticalBound.hasDerivAt_integral_of_compact.{uG}
