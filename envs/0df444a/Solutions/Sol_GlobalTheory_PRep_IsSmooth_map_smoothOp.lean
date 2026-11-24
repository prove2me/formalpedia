-- Prove2me | solution 1 for GlobalTheory.PRep.IsSmooth.map_smoothOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:36:56.046578+00:00
-- url     : https://prove2.me/submissions/d0fccbd3-615a-4651-9ec4-76ba4e793d00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_map_lcIntegral
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_integrand
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
open GlobalTheory.PRep
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace G]
variable [IsTopologicalGroup G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  {ρ : Representation ℂ G V} {f f' : G → ℂ}
namespace GlobalTheory.OpTrace
namespace _root_.GlobalTheory.PRep.IsSmooth
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (hρ : IsSmooth ρ) (hf : IsLocallyConstant f) (hc : HasCompactSupport f)
    (l : V →ₗ[ℂ] E) (v : V) : l (smoothOp ρ μ f v) = ∫ g, f g • l (ρ g v) ∂μ := by
  rw [hρ.smoothOp_apply hf hc, map_lcIntegral (hρ.smoothOp_integrand hf hc v).1 (hρ.smoothOp_integrand hf hc v).2]
  simp only [map_smul]
end _root_.GlobalTheory.PRep.IsSmooth
end GlobalTheory.OpTrace
