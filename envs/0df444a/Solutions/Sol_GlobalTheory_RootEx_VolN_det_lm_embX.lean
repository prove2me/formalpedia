-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.det_lm_embX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:03:13.012623+00:00
-- url     : https://prove2.me/submissions/b3643be2-3a10-4981-90c3-72933623fa0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_VolN_det_lm
import Theorems.Thm_GlobalTheory_RootEx_VolN_det_block_fromBlocks
import Theorems.Thm_GlobalTheory_RootEx_VolN_val_embX

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
theorem _root_.solution {p : ℕ} (x : GL n k) :
    (lm (Up n c p) (embX c x).val).det = x.val.det ^ (c - p) := by
  rw [det_lm, val_embX]
  rw [Finset.prod_congr rfl fun s _ => det_block_fromBlocks x.val _ (p < lev p s) fun a => Iff.rfl]
  rw [Fintype.prod_sum_type]
  change (∏ _a : n, if p < p then x.val.det else 1) * (∏ i : Fin c, if p < i.val + 1 then x.val.det else 1) = _
  simp only [lt_irrefl, if_false, Finset.prod_const_one, one_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => if p < i + 1 then x.val.det else 1), ← Finset.prod_filter,
    Finset.prod_const]
  congr 1
  have : (Finset.range c).filter (fun i => p < i + 1) = Finset.Ico p c := by
    ext i; simp; omega
  rw [this, Nat.card_Ico]
end GlobalTheory.RootEx.VolN
