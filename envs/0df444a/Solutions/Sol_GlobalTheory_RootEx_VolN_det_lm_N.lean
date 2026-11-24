-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.det_lm_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:03:12.146827+00:00
-- url     : https://prove2.me/submissions/ba39e4dc-c12a-47e0-8482-ca54a6881881

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_VolN_det_lm
import Theorems.Thm_GlobalTheory_RootEx_VolN_det_block_unitri

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
theorem _root_.solution (p : ℕ) (g : N k n c p) : (lm (Up n c p) (g : GL (n ⊕ Fin c) k).val).det = 1 := by
  rw [det_lm]
  exact Finset.prod_eq_one fun s _ => det_block_unitri (lev p) _ (mem_N_iff.1 g.2) _
end GlobalTheory.RootEx.VolN
