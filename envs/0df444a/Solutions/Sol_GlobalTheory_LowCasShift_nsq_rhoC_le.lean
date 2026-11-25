-- Prove2me | solution 1 for GlobalTheory.LowCasShift.nsq_rhoC_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:36.863694+00:00
-- url     : https://prove2.me/submissions/bfff5d7d-0cac-499f-88a1-f44d09dea735

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LowKSubSingleSqrtCkvLe
import Theorems.Thm_GlobalTheory_LowCasShift_rhoC_bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.LowCasShift
namespace GlobalTheory.LowCasShift
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) : nsq (rhoC ε) ≤ (n : ℝ) ^ 3 := by
  unfold nsq dot
  have h : ∀ a ∈ (univ : Finset (Fin n)), rhoC ε a * rhoC ε a ≤ (n : ℝ) ^ 2 := by
    intro a _
    have := rhoC_bd ε a
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [this.1, this.2]
  have := sum_le_card_nsmul _ _ _ h
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  calc _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := this
    _ = _ := by ring
end GlobalTheory.LowCasShift
