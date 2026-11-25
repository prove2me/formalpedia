-- Prove2me | solution 1 for GlobalTheory.BlockValue.OnlyIn.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:45.83452+00:00
-- url     : https://prove2.me/submissions/47f26f10-9dd8-479e-a47a-553e4c9acec0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_one
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators
open GlobalTheory GlobalTheory.BlockValue
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.BlockValue
namespace OnlyIn
theorem _root_.solution {S : σ → Prop} {f : MvPowerSeries σ C} (hf : OnlyIn S f) (k : ℕ) :
    OnlyIn S (f ^ k) := by
  induction k with
  | zero => simpa using OnlyIn.one S
  | succ k ih => rw [pow_succ]; exact ih.mul hf
end OnlyIn
end GlobalTheory.BlockValue
