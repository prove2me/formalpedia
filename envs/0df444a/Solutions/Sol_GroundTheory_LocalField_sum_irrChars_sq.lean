-- Prove2me | solution 1 for GroundTheory.LocalField.sum_irrChars_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:47:34.310752+00:00
-- url     : https://prove2.me/submissions/3001ad91-ea97-4a47-b0ec-346eb4a098bd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_sum_irrChars_mul_apply

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
variable {G : Type*} [Group G] [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution : ∑ ψ ∈ irrChars G, ψ 1 ^ 2 = (Nat.card G : ℂ) := by
  classical
  have h := sum_irrChars_mul_apply (G := G) 1
  rw [if_pos rfl] at h
  rw [← h]
  exact Finset.sum_congr rfl fun ψ _ ↦ sq _
end GroundTheory.LocalField
