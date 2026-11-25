-- Prove2me | solution 1 for GlobalTheory.LowCasShift.rhoN_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:06:46.590509+00:00
-- url     : https://prove2.me/submissions/aaa34555-8746-4aa8-a46e-d2328613e9e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LowKSubSingleSqrtCkvLe
import Theorems.Thm_GlobalTheory_LowCasShift_card_le

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    -((n : ℝ) / 2) ≤ rhoN ε a ∧ rhoN ε a ≤ (n : ℝ) / 2 := by
  have h1 := card_le (fun b : Fin n => a < b ∧ ε b ≠ ε a)
  have h2 := card_le (fun b : Fin n => b < a ∧ ε b ≠ ε a)
  unfold rhoN
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
end GlobalTheory.LowCasShift
