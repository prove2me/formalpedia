-- Prove2me | solution 1 for GlobalTheory.RootEx.ExchangeSupport.colM_mul_rowM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:42.765229+00:00
-- url     : https://prove2.me/submissions/ab9bd133-c2dc-4ce0-8d37-d853c7a49534

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
omit [DecidableEq n] [Fintype n]
namespace GlobalTheory.RootEx.ExchangeSupport
theorem _root_.solution (u β : n → k) : colM c (p + 1) β * rowM c p u = 0 := by
  ext r s
  simp only [colM, rowM, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with h1 h2
  · omega
  all_goals simp
end GlobalTheory.RootEx.ExchangeSupport
