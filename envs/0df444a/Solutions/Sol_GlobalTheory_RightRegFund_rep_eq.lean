-- Prove2me | solution 1 for GlobalTheory.RightRegFund.rep_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:44.365303+00:00
-- url     : https://prove2.me/submissions/c3b93db9-0963-4e38-94a8-d6527fb4a602

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
variable {Γ : Subgroup G} {D : Set G} {r : G → G}
namespace GlobalTheory.RightRegFund
theorem _root_.solution (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {y : G} (h : Good Γ D y)
    {γ : Γ} (hγ : (γ : G) * y ∈ D) : r y = γ * y := by
  obtain ⟨δ, h1, h2⟩ := hr y
  rw [h1, h δ γ (h1 ▸ h2) hγ]
end GlobalTheory.RightRegFund
