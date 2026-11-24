-- Prove2me | solution 1 for GlobalTheory.RightRegFund.rep_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:55.904551+00:00
-- url     : https://prove2.me/submissions/5c6a1c9b-ff29-4615-8bb1-41afca8f0251

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep
import Theorems.Thm_GlobalTheory_RightRegFund_rep_eq

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
    (δ : Γ) : r ((δ : G) * y) = r y := by
  obtain ⟨γ, h1, h2⟩ := hr ((δ : G) * y)
  have : r y = ((γ * δ : Γ) : G) * y :=
    rep_eq hr h (by simpa [mul_assoc, ← h1] using h2)
  rw [this, h1]; simp [mul_assoc]
end GlobalTheory.RightRegFund
