-- Prove2me | solution 1 for GlobalTheory.SliceOpDecay.pow_norm_le_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:51.715646+00:00
-- url     : https://prove2.me/submissions/4a1ae4cf-8773-444d-89fe-3582cc2f974e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowNormMulSeminormSliceRLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorSchwartzSeminormBound
import Theorems.Thm_GlobalTheory_SliceOpDecay_norm_le_max_comp

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
    (z : κ ⊕ κ₁' → V) (k : ℕ) : ‖z‖ ^ k ≤ ‖z ∘ Sum.inl‖ ^ k + ‖z ∘ Sum.inr‖ ^ k := by
  have h := pow_le_pow_left₀ (norm_nonneg z) (norm_le_max_comp z) k
  rcases le_total ‖z ∘ Sum.inl‖ ‖z ∘ Sum.inr‖ with hle | hle
  · rw [max_eq_right hle] at h; linarith [pow_nonneg (norm_nonneg (z ∘ Sum.inl)) k]
  · rw [max_eq_left hle] at h; linarith [pow_nonneg (norm_nonneg (z ∘ Sum.inr)) k]
end GlobalTheory.SliceOpDecay
