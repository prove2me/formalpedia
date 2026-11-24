-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.det_block_unitri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:20.259448+00:00
-- url     : https://prove2.me/submissions/64560d4a-61e9-41d2-8758-7df99c229211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_VolN_det_unitri

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
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution (b : ι → ℕ) (M : Matrix ι ι k)
    (hM : ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s) (Q : ι → Prop) [DecidablePred Q] :
    (M.toSquareBlockProp Q).det = 1 := by
  refine det_unitri (fun r => b r.1) _ fun r s h => ?_
  simp [toSquareBlockProp_def, hM _ _ h, Matrix.one_apply, Subtype.ext_iff]
end GlobalTheory.RootEx.VolN
