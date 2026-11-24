-- Prove2me | solution 1 for GlobalTheory.PRep.IsSmooth.smoothOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:21:58.462383+00:00
-- url     : https://prove2.me/submissions/20111d58-8948-47d0-8a24-561853dceb83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_map_lcIntegral
import Theorems.Thm_GlobalTheory_OpTrace_eq_of_forall_dual
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_integrand
import Theorems.Thm_GlobalTheory_OpTrace_integrable_map

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
    (hc : HasCompactSupport f) (v : V) :
    smoothOp ρ μ f v = lcIntegral μ fun g => f g • ρ g v := by
  have hi := hρ.smoothOp_integrand hf hc
  have h : ∃ T : V →ₗ[ℂ] V, ∀ v, T v = lcIntegral μ fun g => f g • ρ g v := by
    refine ⟨⟨⟨fun v => lcIntegral μ fun g => f g • ρ g v, fun v w => ?_⟩, fun c v => ?_⟩,
      fun _ => rfl⟩
    · refine eq_of_forall_dual fun l => ?_
      rw [map_add l, map_lcIntegral (hi _).1 (hi _).2, map_lcIntegral (hi _).1 (hi _).2,
        map_lcIntegral (hi _).1 (hi _).2, ← integral_add
          (integrable_map (hi _).1 (hi _).2 l l.map_zero)
          (integrable_map (hi _).1 (hi _).2 l l.map_zero)]
      simp only [map_add, smul_add]
    · refine eq_of_forall_dual fun l => ?_
      rw [RingHom.id_apply, map_smul l, map_lcIntegral (hi _).1 (hi _).2,
        map_lcIntegral (hi _).1 (hi _).2, ← integral_smul]
      simp only [map_smul, smul_comm c]
  rw [smoothOp, dif_pos h, h.choose_spec]
end _root_.GlobalTheory.PRep.IsSmooth
end GlobalTheory.OpTrace
