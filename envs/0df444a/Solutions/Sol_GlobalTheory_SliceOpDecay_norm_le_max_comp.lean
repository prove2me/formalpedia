-- Prove2me | solution 1 for GlobalTheory.SliceOpDecay.norm_le_max_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:49:07.787746+00:00
-- url     : https://prove2.me/submissions/38cd04a7-8d50-4623-b7e5-874ece9adb6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowNormMulSeminormSliceRLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorSchwartzSeminormBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOpDecay
namespace GlobalTheory.SliceOpDecay
theorem _root_.solution {V : Type} [NormedAddCommGroup V] {κ κ₁' : Type} [Fintype κ] [Fintype κ₁']
    (z : κ ⊕ κ₁' → V) : ‖z‖ ≤ max ‖z ∘ Sum.inl‖ ‖z ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun i => ?_
  cases i with
  | inl i => exact (norm_le_pi_norm (z ∘ Sum.inl) i).trans (le_max_left _ _)
  | inr j => exact (norm_le_pi_norm (z ∘ Sum.inr) j).trans (le_max_right _ _)
end GlobalTheory.SliceOpDecay
