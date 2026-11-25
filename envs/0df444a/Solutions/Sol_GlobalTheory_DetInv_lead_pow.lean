-- Prove2me | solution 1 for GlobalTheory.DetInv.lead_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:40:48.635672+00:00
-- url     : https://prove2.me/submissions/0b087358-4dfc-43fe-973a-3e92f8f40da2

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
theorem _root_.solution {R C : Type} [CommRing R] [Field C] (f : R →+* C) (ξ : R) (n : ℕ) :
    Lead f ξ (ξ ^ n) n 1 := ⟨1, 1, by simp, by simp, by simp⟩
end GlobalTheory.DetInv
