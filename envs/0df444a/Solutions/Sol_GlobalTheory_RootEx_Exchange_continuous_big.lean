-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.continuous_big
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:29.788013+00:00
-- url     : https://prove2.me/submissions/7c2ec66c-d1f8-4bc4-be57-a3589e7aedd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero

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
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution {ψ : AddChar k Circle} (hψ : Continuous ψ) (q : Fin c) {χ : (n' → k) → ℂ}
    (hχ : Continuous χ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Continuous Φ) :
    Continuous (big ψ q χ Φ) := by
  unfold big ch
  refine ((hχ.comp (continuous_pi fun s => continuous_id.matrix_elem _ _)).mul hΦ).mul
    (continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_)))
  exact continuous_finset_sum _ fun i _ => continuous_id.matrix_elem _ _
end GlobalTheory.RootEx.Exchange
