-- Prove2me | solution 1 for GlobalTheory.PRep.IsSmooth.smoothOp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:51:50.9811+00:00
-- url     : https://prove2.me/submissions/5c1b4fcd-e297-4c97-aaf2-ad7926c8bdf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_add
import Theorems.Thm_GlobalTheory_OpTrace_eq_of_forall_dual
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_integrand
import Theorems.Thm_GlobalTheory_OpTrace_integrable_map
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_map_smoothOp

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
theorem _root_.solution (hρ : IsSmooth ρ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (hf' : IsLocallyConstant f') (hc' : HasCompactSupport f') :
    smoothOp ρ μ (f + f') = smoothOp ρ μ f + smoothOp ρ μ f' := by
  ext v
  refine eq_of_forall_dual fun l => ?_
  have h1 := integrable_map (μ := μ) (hρ.smoothOp_integrand hf hc v).1 (hρ.smoothOp_integrand hf hc v).2 l l.map_zero
  have h2 := integrable_map (μ := μ) (hρ.smoothOp_integrand hf' hc' v).1 (hρ.smoothOp_integrand hf' hc' v).2 l
    l.map_zero
  simp only [map_smul] at h1 h2
  rw [LinearMap.add_apply, map_add l, hρ.map_smoothOp (hf.add hf') (hc.add hc'),
    hρ.map_smoothOp hf hc, hρ.map_smoothOp hf' hc', ← integral_add h1 h2]
  simp only [Pi.add_apply, add_smul]
end _root_.GlobalTheory.PRep.IsSmooth
end GlobalTheory.OpTrace
