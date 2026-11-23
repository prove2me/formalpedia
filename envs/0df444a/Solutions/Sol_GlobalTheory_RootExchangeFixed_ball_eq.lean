-- Prove2me | solution 1 for GlobalTheory.RootExchangeFixed.ball_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:39.060953+00:00
-- url     : https://prove2.me/submissions/113541e8-5bf9-4fcc-a8d7-2616244c4782

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space

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
open GlobalTheory GlobalTheory.RootExchangeFixed
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.RootExchangeFixed
theorem _root_.solution (s : kˣ) : {x : k | valuation k x ≤ valuation k (s : k)} = s • (𝒪[k] : Set k) := by
  have hs : 0 < valuation k (s : k) := by simp [pos_iff_ne_zero]
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  show _ ↔ valuation k (((s⁻¹ : kˣ) : k) * x) ≤ 1
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ hs, mul_one]
  rfl
end GlobalTheory.RootExchangeFixed
