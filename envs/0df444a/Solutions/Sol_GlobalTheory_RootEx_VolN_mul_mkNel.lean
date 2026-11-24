-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.mul_mkNel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:03:20.335997+00:00
-- url     : https://prove2.me/submissions/58bb89bb-2bd9-4364-bc6d-d8513fb20b4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_VolN_mul_matrixExtendSelectedEntriesByZero_apply
import Theorems.Thm_GlobalTheory_RootEx_VolN_val_mkNel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution (p : ℕ) (g : N k n c p) (e : Ix n c p → k) :
    g * mkNel p e = mkNel p ((lm (Up n c p) (g : GL (n ⊕ Fin c) k).val).mulVec e + co p g) := by
  rw [← mkNel_co p (g * mkNel p e)]
  congr 1
  funext rs
  rw [Pi.add_apply, ← mul_matrixExtendSelectedEntriesByZero_apply]
  simp only [co, Subgroup.coe_mul, Units.val_mul, val_mkNel, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  rw [add_comm]
end GlobalTheory.RootEx.VolN
