-- Prove2me | solution 1 for GlobalTheory.LowCasShift.sqrt_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:18.296472+00:00
-- url     : https://prove2.me/submissions/90a0e342-5da9-4f56-a64f-970c30eeea55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LowKSubSingleSqrtCkvLe

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
theorem _root_.solution {X Y b : ℝ} (hb : 4 ≤ b) (hX : (b / 2) ^ 2 ≤ X) (hY : X - b ≤ Y) :
    Real.sqrt X ≤ Real.sqrt Y + 2 := by
  have h1 : b / 2 ≤ Real.sqrt X := Real.le_sqrt_of_sq_le hX
  have h0 : 0 ≤ X := le_trans (sq_nonneg _) hX
  have h2 : Real.sqrt X ^ 2 = X := Real.sq_sqrt h0
  have h3 : Real.sqrt X - 2 ≤ Real.sqrt Y := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  linarith
end GlobalTheory.LowCasShift
