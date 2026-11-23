-- Prove2me | solution 1 for GlobalTheory.RootEx.ExchangeSupport.rowM_mul_colM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:44.596426+00:00
-- url     : https://prove2.me/submissions/aa52d12c-4c9e-4dbb-bb7e-1e268d67930b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ExchangeSupport
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
omit [DecidableEq n]
namespace GlobalTheory.RootEx.ExchangeSupport
theorem _root_.solution (u β : n → k) (i j : Fin c) :
    (rowM c p u * colM c (p + 1) β) i j = if i.val + 1 = p ∧ j.val = p then u ⬝ᵥ β else 0 := by
  simp only [colM, rowM, Matrix.mul_apply, Matrix.of_apply, dotProduct]
  by_cases h1 : i.val + 1 = p <;> by_cases h2 : j.val = p <;> simp [h1, h2]
end GlobalTheory.RootEx.ExchangeSupport
