-- Prove2me | solution 1 for GlobalTheory.RightRegFund.ae_rep_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:55.959898+00:00
-- url     : https://prove2.me/submissions/040c1059-76f5-4605-8fe3-498a8ebdedbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep
import Theorems.Thm_GlobalTheory_RightRegFund_rep_eq
import Theorems.Thm_GlobalTheory_RightRegFund_ae_good

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
namespace GlobalTheory.RightRegFund
theorem _root_.solution (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) : ∀ᵐ x ∂(μ.restrict D), r x = x := by
  refine (ae_restrict_iff' hDm).2 ((ae_good hD).mono fun y hy h => ?_)
  simpa using rep_eq hr hy (γ := 1) (by simpa using h)
end GlobalTheory.RightRegFund
