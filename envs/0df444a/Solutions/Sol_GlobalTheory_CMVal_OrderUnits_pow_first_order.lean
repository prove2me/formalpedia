-- Prove2me | solution 1 for GlobalTheory.CMVal.OrderUnits.pow_first_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:05:27.627861+00:00
-- url     : https://prove2.me/submissions/f18f7767-708c-4576-98a0-eb82ee7b0b78

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnits
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
theorem _root_.solution {R : Type} [CommRing R] (t : R) (i : ℕ) : ∃ r, (1 + t) ^ i = 1 + i * t + t ^ 2 * r := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨r + i + t * r, by rw [pow_succ, hr]; push_cast; ring⟩
end GlobalTheory.CMVal.OrderUnits
