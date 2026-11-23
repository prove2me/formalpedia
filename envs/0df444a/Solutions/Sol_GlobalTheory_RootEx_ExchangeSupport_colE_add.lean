-- Prove2me | solution 1 for GlobalTheory.RootEx.ExchangeSupport.colE_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:30.361806+00:00
-- url     : https://prove2.me/submissions/6f81baf5-2118-4a8c-b7c7-f9eb0443209b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_val

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
namespace GlobalTheory.RootEx.ExchangeSupport
theorem _root_.solution (u w : n → k) : colE c p (u + w) = colE c p u * colE c p w := by
  apply Units.ext
  rw [Units.val_mul, colE_val, colE_val, colE_val]
  have : colM c p (u + w) = colM c p w + colM c p u := by
    ext i j; simp only [colM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp [add_comm]
  simp [fromBlocks_multiply, this]
end GlobalTheory.RootEx.ExchangeSupport
