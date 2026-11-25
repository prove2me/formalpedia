-- Prove2me | solution 1 for GlobalTheory.ConnPointwise.entry_le_of_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:31.284536+00:00
-- url     : https://prove2.me/submissions/4f79a533-6f81-4024-a6a0-f8d6c40d851d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLe
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.ConnPointwise
variable {g : ℕ}
namespace GlobalTheory.ConnPointwise
theorem _root_.solution (P : Matrix (Fin g) (Fin g) ℝ) {W : ℝ} (hW : 0 ≤ W)
    (h : ∀ x, ‖P *ᵥ x‖ ≤ W * ‖x‖) (j k : Fin g) : |P j k| ≤ W := by
  have h1 := h (Pi.single k 1)
  have hs : ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      by_cases hi : i = k
      · subst hi; simp
      · simp [Pi.single_apply, hi]
  rw [mulVec_single_one] at h1
  calc |P j k| = ‖Pᵀ k j‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖Pᵀ k‖ := norm_le_pi_norm _ j
    _ ≤ W * ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ := h1
    _ ≤ W := mul_le_of_le_one_right hW hs
end GlobalTheory.ConnPointwise
