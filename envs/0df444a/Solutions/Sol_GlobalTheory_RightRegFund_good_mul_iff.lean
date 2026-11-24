-- Prove2me | solution 1 for GlobalTheory.RightRegFund.good_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:56:33.20536+00:00
-- url     : https://prove2.me/submissions/80f63936-ed88-41f6-9457-5eea54f627cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep
import Theorems.Thm_GlobalTheory_RightRegFund_Good_mul

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
theorem _root_.solution {Γ : Subgroup G} {D : Set G} {y : G} (δ : Γ) :
    Good Γ D ((δ : G) * y) ↔ Good Γ D y :=
  ⟨fun h => by simpa using h.mul δ⁻¹, fun h => h.mul δ⟩
end GlobalTheory.RightRegFund
