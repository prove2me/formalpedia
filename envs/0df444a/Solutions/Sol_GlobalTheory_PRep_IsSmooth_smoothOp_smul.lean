-- Prove2me | solution 1 for GlobalTheory.PRep.IsSmooth.smoothOp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:51:52.744819+00:00
-- url     : https://prove2.me/submissions/87a102c0-6009-4009-8b52-4db02c3535fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_comp_left
import Theorems.Thm_GlobalTheory_OpTrace_eq_of_forall_dual
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
    (hc : HasCompactSupport f) (c : ℂ) : smoothOp ρ μ (c • f) = c • smoothOp ρ μ f := by
  ext v
  refine eq_of_forall_dual fun l => ?_
  rw [LinearMap.smul_apply, map_smul l,
    hρ.map_smoothOp (f := c • f) (hf.comp (c • ·)) (hc.comp_left (g := (c • ·)) (smul_zero c)),
    hρ.map_smoothOp hf hc, ← integral_smul]
  simp only [Pi.smul_apply, smul_assoc]
end _root_.GlobalTheory.PRep.IsSmooth
end GlobalTheory.OpTrace
