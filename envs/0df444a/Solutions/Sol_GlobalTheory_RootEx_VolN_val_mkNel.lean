-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.val_mkNel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:58.259429+00:00
-- url     : https://prove2.me/submissions/bb387e77-ac8f-4e8d-8734-2dba863752ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus

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
theorem _root_.solution (p : ℕ) (e : Ix n c p → k) :
    ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k).val = 1 + ext0 (Up n c p) e := by
  ext r s
  change mkN p e r s = _
  by_cases h : lev p r < lev p s
  · have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [mkN, ext0, h, this]
  · simp [mkN, ext0, h]
end GlobalTheory.RootEx.VolN
