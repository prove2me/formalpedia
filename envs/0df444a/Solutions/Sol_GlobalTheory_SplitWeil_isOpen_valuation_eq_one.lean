-- Prove2me | solution 1 for GlobalTheory.SplitWeil.isOpen_valuation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:56:05.1178+00:00
-- url     : https://prove2.me/submissions/3177af08-665e-4bae-9cdb-68de9773c605

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.SplitWeil
theorem _root_.solution : IsOpen {x : kˣ | valuation k (x : k) = 1} := by
  have : {x : kˣ | valuation k (x : k) = 1} =
      (fun x : kˣ => (x : k)) ⁻¹' (𝒪[k] : Set k) ∩ (fun x : kˣ => ((x⁻¹ : kˣ) : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
      Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_le_one₀ (by simp [zero_lt_iff])]
    exact le_antisymm_iff
  rw [this]
  exact ((isOpen_int k).preimage Units.continuous_val).inter
    ((isOpen_int k).preimage Units.continuous_coe_inv)
end GlobalTheory.SplitWeil
