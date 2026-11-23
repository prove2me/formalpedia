-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.chart_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:02.120664+00:00
-- url     : https://prove2.me/submissions/780005be-e663-4fdf-a97a-c1a97ccaca5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_ext_pos
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chart_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotStep
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {b : ι → ℕ} {S : ι × ι → Prop}
variable (hS : ∀ rs, S rs → b rs.1 < b rs.2)
namespace GlobalTheory.RootEx.QuotStep
theorem _root_.solution (e : {rs // S rs} → k) (i : {rs // S rs}) : (chart hS e).val i.1.1 i.1.2 = e i := by
  have : i.1.1 ≠ i.1.2 := fun h => absurd (hS _ i.2) (by rw [h]; exact lt_irrefl _)
  rw [chart_val, Matrix.add_apply, Matrix.one_apply_ne this, zero_add, ext_pos e i.2]
end GlobalTheory.RootEx.QuotStep
