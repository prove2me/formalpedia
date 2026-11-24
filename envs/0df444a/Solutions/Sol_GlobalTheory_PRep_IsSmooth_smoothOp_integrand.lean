-- Prove2me | solution 1 for GlobalTheory.PRep.IsSmooth.smoothOp_integrand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:13.333949+00:00
-- url     : https://prove2.me/submissions/0ea54d59-13bd-4fcf-adc0-2b8d4c759706

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_isLocallyConstant_orbit

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
omit [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.OpTrace
namespace _root_.GlobalTheory.PRep.IsSmooth
theorem _root_.solution (hρ : IsSmooth ρ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (v : V) :
    IsLocallyConstant (fun g => f g • ρ g v) ∧ HasCompactSupport fun g => f g • ρ g v :=
  ⟨hf.comp₂ (hρ.isLocallyConstant_orbit v) (· • ·), hc.smul_right⟩
end _root_.GlobalTheory.PRep.IsSmooth
end GlobalTheory.OpTrace
