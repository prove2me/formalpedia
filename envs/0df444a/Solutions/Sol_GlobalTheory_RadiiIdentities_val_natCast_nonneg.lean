-- Prove2me | solution 1 for GlobalTheory.RadiiIdentities.val_natCast_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:25:15.438731+00:00
-- url     : https://prove2.me/submissions/a804d0dc-2e61-4ce9-aeb8-8d740324611a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory
open GlobalTheory.RadiiIdentities
namespace GlobalTheory.RadiiIdentities
theorem _root_.solution {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    calc (0 : WithTop ℝ) ≤ min (v (k : C)) (v 1) := by
          rw [AddValuation.map_one]
          exact le_min ih le_rfl
      _ ≤ v ((k : C) + 1) := AddValuation.map_add v _ _
end GlobalTheory.RadiiIdentities
