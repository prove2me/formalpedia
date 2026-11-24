-- Prove2me | solution 1 for GlobalTheory.RightRegFund.Good.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:15.236113+00:00
-- url     : https://prove2.me/submissions/a781928e-6264-4485-aae1-235954c65242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep

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
namespace GlobalTheory.RightRegFund
namespace Good
theorem _root_.solution {Γ : Subgroup G} {D : Set G} {y : G} (h : Good Γ D y) (δ : Γ) :
    Good Γ D ((δ : G) * y) := by
  intro γ γ' h1 h2
  have := h (γ * δ) (γ' * δ) (by simpa [mul_assoc] using h1) (by simpa [mul_assoc] using h2)
  exact mul_right_cancel this
end Good
end GlobalTheory.RightRegFund
