-- Prove2me | solution 1 for GlobalTheory.DetInv.iotaScalar_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:44:51.379945+00:00
-- url     : https://prove2.me/submissions/de52a071-efd6-4a5f-9625-7a1ce244673d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SandwichMaps
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix GlobalTheory.Sandwich TensorProduct
open GlobalTheory GlobalTheory.DetInv
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
variable (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]
variable {p O Λ}
namespace GlobalTheory.DetInv
theorem _root_.solution {C : Type} [Field C] (N : ℕ) :
    IotaScalar (1 : Matrix (Fin N) (Fin N) C) 0 0 1 := by
  intro x y _ h2
  have : y = x := funext fun i => by simpa using h2 i (Nat.zero_le _)
  simp [this]
end GlobalTheory.DetInv
