-- Prove2me | solution 1 for GroundTheory.LocalField.sum_conj_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:06:11.525799+00:00
-- url     : https://prove2.me/submissions/e9522131-dcc4-4932-9405-bbe0f836cd50

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G]
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}
omit [Fintype G] hp
namespace GroundTheory.LocalField
theorem _root_.solution [Fintype G] {g : G} (hc : ¬ IsConj x g) :
    (∑ t : G, if t⁻¹ * g * t = x then (1 : ℂ) else 0) = 0 := by
  refine Finset.sum_eq_zero fun t _ ↦ if_neg fun h ↦ hc ?_
  rw [isConj_iff]
  exact ⟨t, by rw [← h]; group⟩
end GroundTheory.LocalField
