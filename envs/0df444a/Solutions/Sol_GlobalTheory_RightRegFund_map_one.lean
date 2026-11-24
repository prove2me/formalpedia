-- Prove2me | solution 1 for GlobalTheory.RightRegFund.map_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:56:33.570505+00:00
-- url     : https://prove2.me/submissions/5003f1d5-d6c9-4764-91d7-a89da8e8bd68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep
import Theorems.Thm_GlobalTheory_RightRegFund_ae_rep_eq_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise
open GlobalTheory GlobalTheory.RightRegFund
variable {G : Type} [Group G]
variable {Γ : Subgroup G} {D : Set G} {r : G → G}
variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ]
variable [μ.IsMulRightInvariant]
variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}
namespace GlobalTheory.RightRegFund
theorem _root_.solution (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g))) : R 1 = 1 := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [hR 1 F, ae_rep_eq_self hD hDm hr] with x h1 h2
  rw [h1, mul_one, h2]; rfl
end GlobalTheory.RightRegFund
