-- Prove2me | solution 1 for GlobalTheory.T.qminor_commute_of_commute_columns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:25.805485+00:00
-- url     : https://prove2.me/submissions/447f336a-d6e1-48ab-b804-028036bd8a45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorCommOfCommColumns
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorCommOfCommColumnsStatement
import Theorems.Thm_GlobalTheory_qminor_comm_of_comm_columns


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (x : A) (a b : Fin t → Fin n) (u : ℂ), (∀ (c : Fin n) (i : Fin t), E c (b i) * x = x * E c (b i)) → qminor E a b u * x = x * qminor E a b u := by
  first | exact @GlobalTheory.qminor_comm_of_comm_columns | exact GlobalTheory.qminor_comm_of_comm_columns | (intros; apply GlobalTheory.qminor_comm_of_comm_columns <;> assumption)
end _root_.GlobalTheory.T
