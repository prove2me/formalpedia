-- Prove2me | solution 1 for GlobalTheory.PRep.IsSmooth.smoothOp_mem_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:51:57.425407+00:00
-- url     : https://prove2.me/submissions/58e90fbb-27c6-4374-81b5-c203b97a1cd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_eq_of_forall_dual
import Theorems.Thm_GlobalTheory_OpTrace_mem_fixed
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
theorem _root_.solution [μ.IsMulLeftInvariant] (hρ : IsSmooth ρ)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) {K : Subgroup G}
    (hK : ∀ k ∈ K, ∀ g, f (k * g) = f g) (v : V) : smoothOp ρ μ f v ∈ fixed ρ K := by
  refine mem_fixed.2 fun k hk => eq_of_forall_dual fun l => ?_
  rw [hρ.map_smoothOp hf hc l, ← integral_mul_left_eq_self _ k]
  simpa [hK k hk] using hρ.map_smoothOp (μ := μ) hf hc (l ∘ₗ ρ k) v
end _root_.GlobalTheory.PRep.IsSmooth
end GlobalTheory.OpTrace
