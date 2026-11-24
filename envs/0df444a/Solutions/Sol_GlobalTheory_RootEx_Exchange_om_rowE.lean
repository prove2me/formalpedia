-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.om_rowE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:16:43.357518+00:00
-- url     : https://prove2.me/submissions/5d9ff139-7505-45ac-b84f-27612139e372

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Theorems.Thm_GlobalTheory_RootEx_Exchange_det_lowU
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one


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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution (μ : kˣ →* ℂˣ) (p : ℕ) (u : n' → k) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    om μ (rowE (c + 1) p u) 1 Φ x = Φ (x * (rowE (c + 1) p u).val) := by
  have : Matrix.GeneralLinearGroup.det (rowE (c + 1) p u) = 1 := det_lowU _
  simp only [om, this, map_one, nabs_one]
  simp
end GlobalTheory.RootEx.Exchange
