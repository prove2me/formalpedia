-- Prove2me | solution 1 for GlobalTheory.PRep.IsAdmissible.smoothTrace_eq_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:18:22.844562+00:00
-- url     : https://prove2.me/submissions/dd3e65ba-7efa-4d81-a5e3-fb9eddea5388

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_finRankTrace_eq_of_equiv
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_map_smoothOp_of_intertwining
import Theorems.Thm_GlobalTheory_PRep_IsAdmissible_finiteDimensional_range_smoothOp

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
namespace _root_.GlobalTheory.PRep.IsAdmissible
theorem _root_.solution [μ.IsMulLeftInvariant] {W : Type} [AddCommGroup W]
    [Module ℂ W] {ρ' : Representation ℂ G W} (hρ : IsAdmissible ρ) (hρ' : IsSmooth ρ')
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (e : V ≃ₗ[ℂ] W)
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) : smoothTrace ρ' μ f = smoothTrace ρ μ f := by
  have := hρ.finiteDimensional_range_smoothOp (μ := μ) hf hc ho hK
  exact (finRankTrace_eq_of_equiv e
    (hρ.1.map_smoothOp_of_intertwining hρ' hf hc (e : V →ₗ[ℂ] W) he)).2
end _root_.GlobalTheory.PRep.IsAdmissible
end GlobalTheory.OpTrace
