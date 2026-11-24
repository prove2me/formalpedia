-- Prove2me | solution 1 for GlobalTheory.T.rootExchangeOperator_weil_rowUnipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:45:35.317612+00:00
-- url     : https://prove2.me/submissions/b7dd319d-dbe0-480f-b0f2-36d1ee77b0a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeOperatorWeilRowUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeOperatorWeilRowUnipotentStatement
import Theorems.Thm_GlobalTheory_RootEx_RowSign_opE_om_rowE


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (u : n' → k) (x₀ : Matrix n n' k), opE ψ ν p (om μ (rowE (c + 1) p u) 1 Φ.1) x₀ = opE ψ ν p (fun x => Φ.1 (x + rowM n c p u)) x₀ := by
  first | exact @GlobalTheory.RootEx.RowSign.opE_om_rowE | exact GlobalTheory.RootEx.RowSign.opE_om_rowE | (intros; apply GlobalTheory.RootEx.RowSign.opE_om_rowE <;> assumption)
end _root_.GlobalTheory.T
