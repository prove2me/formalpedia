-- Prove2me | solution 1 for GlobalTheory.T.weil_formula_rootExchange_parabolic_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:01.092487+00:00
-- url     : https://prove2.me/submissions/32c86b8a-47ca-418a-afb8-643204cc306d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicQuotient
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicQuotientStatement
import Theorems.Thm_GlobalTheory_QuotIntFJ_weil_formula_FJ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) f z → (∀ h, Integrable (fun β : n → k => f (colE c (ρ + 1) β * h)) (Measure.pi fun _ => ν)) ∧ IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k, f (colE c (ρ + 1) β * h) ∂(Measure.pi fun _ => ν)) z := by
  first | exact @GlobalTheory.QuotIntFJ.weil_formula_FJ | exact GlobalTheory.QuotIntFJ.weil_formula_FJ | (intros; apply GlobalTheory.QuotIntFJ.weil_formula_FJ <;> assumption)
end _root_.GlobalTheory.T
