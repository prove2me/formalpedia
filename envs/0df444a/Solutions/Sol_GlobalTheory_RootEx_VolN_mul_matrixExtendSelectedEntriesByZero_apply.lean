-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.mul_matrixExtendSelectedEntriesByZero_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:37.869091+00:00
-- url     : https://prove2.me/submissions/7d511a06-78f5-4176-a4b9-777f9f66e6f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_VolN_sum_extendByZero_fin_eq_sum_of_eq

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
theorem _root_.solution (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}] (h : Matrix ι ι k)
    (e : {rs : ι × ι // P rs.1 rs.2} → k) (a : {rs : ι × ι // P rs.1 rs.2}) :
    (h * ext0 P e) a.1.1 a.1.2 = (lm P h).mulVec e a := by
  have := sum_extendByZero_fin_eq_sum_of_eq P e (fun b => if a.1.2 = b.2 then h a.1.1 b.1 else 0)
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, lm, Matrix.of_apply]
  rw [this]
  simp
end GlobalTheory.RootEx.VolN
