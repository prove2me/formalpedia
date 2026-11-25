-- Prove2me | solution 1 for GroundTheory.LocalField.card_smul_eq_sum_classCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:07:56.330015+00:00
-- url     : https://prove2.me/submissions/8a94b7ab-206a-42bc-8f7d-25908231e152

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal

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
variable {G : Type u} [Group G] [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution {F : G → ℂ} (hF : IsClassFun F) :
    (Nat.card G : ℂ) • F = ∑ s : G, F s • classCount s := by
  funext g
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, classCount, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ t : G, ∑ s : G, F s * (if t⁻¹ * g * t = s then 1 else 0) = F g := by
    intro t
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    simpa using hF g t⁻¹
  rw [Finset.sum_congr rfl fun t _ ↦ h t, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]
end GroundTheory.LocalField
