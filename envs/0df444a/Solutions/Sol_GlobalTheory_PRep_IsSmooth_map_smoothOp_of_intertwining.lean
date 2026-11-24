-- Prove2me | solution 1 for GlobalTheory.PRep.IsSmooth.map_smoothOp_of_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:51:56.135719+00:00
-- url     : https://prove2.me/submissions/2f5c3c60-d263-41e8-b1e4-f68d8a639319

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
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
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℂ W]
    {ρ' : Representation ℂ G W} (hρ : IsSmooth ρ) (hρ' : IsSmooth ρ')
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (j : V →ₗ[ℂ] W)
    (hj : ∀ g v, j (ρ g v) = ρ' g (j v)) (v : V) :
    j (smoothOp ρ μ f v) = smoothOp ρ' μ f (j v) := by
  refine eq_of_forall_dual fun l => ?_
  rw [hρ'.map_smoothOp hf hc]
  simpa [hj] using hρ.map_smoothOp (μ := μ) hf hc (l ∘ₗ j) v
end _root_.GlobalTheory.PRep.IsSmooth
end GlobalTheory.OpTrace
