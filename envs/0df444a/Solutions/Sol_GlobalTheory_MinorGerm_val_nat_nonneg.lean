-- Prove2me | solution 1 for GlobalTheory.MinorGerm.val_nat_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:51:16.737827+00:00
-- url     : https://prove2.me/submissions/798fa609-9de8-4f26-a914-358bc1f17721

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
namespace GlobalTheory.MinorGerm
theorem _root_.solution (n : ℕ) : 0 ≤ v (n : C) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact le_trans (le_min ih (AddValuation.map_one v).ge) (AddValuation.map_add v _ _)
end GlobalTheory.MinorGerm
