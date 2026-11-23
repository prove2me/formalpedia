-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.chart_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:43.277107+00:00
-- url     : https://prove2.me/submissions/d338722b-0360-4395-88e1-45fbe83bcb1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chart_pos
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chart_neg

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
theorem _root_.solution (g : GL ι k) (hg : ∀ r s, ¬ S (r, s) → g.val r s = (1 : Matrix ι ι k) r s) :
    chart hS (fun i => g.val i.1.1 i.1.2) = g := by
  ext r s
  by_cases h : S (r, s)
  · exact chart_pos hS _ ⟨(r, s), h⟩
  · rw [chart_neg hS _ h, hg r s h]
end GlobalTheory.RootEx.QuotStep
