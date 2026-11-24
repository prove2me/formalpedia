-- Prove2me | solution 1 for GlobalTheory.CMVal.OrderUnits.geom_first_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:21:41.971326+00:00
-- url     : https://prove2.me/submissions/48d8f547-da65-43f0-a88a-f9d63fe8154a

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnits
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_pow_first_order
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits
namespace GlobalTheory.CMVal.OrderUnits
theorem _root_.solution {R : Type} [CommRing R] (t : R) (n : ℕ) :
    ∃ r, ∑ i ∈ Finset.range n, (1 + t) ^ i = n + (n.choose 2 : ℕ) * t + t ^ 2 * r := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨s, hs⟩ := pow_first_order t n
    refine ⟨r + s, ?_⟩
    rw [Finset.sum_range_succ, hr, hs, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    push_cast; ring
end GlobalTheory.CMVal.OrderUnits
