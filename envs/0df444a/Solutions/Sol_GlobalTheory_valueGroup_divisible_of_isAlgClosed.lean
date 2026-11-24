-- Prove2me | solution 1 for GlobalTheory.valueGroup_divisible_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:42:20.587241+00:00
-- url     : https://prove2.me/submissions/1d2f6ee5-a676-4d81-908f-b10d463f0161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {C : Type*} [Field C] [IsAlgClosed C]
    (O : ValuationSubring C) (γ : O.ValueGroup) {n : ℕ} (hn : 0 < n) :
    ∃ δ : O.ValueGroup, δ ^ n = γ := by
  obtain ⟨x, rfl⟩ := O.valuation_surjective γ
  obtain ⟨y, rfl⟩ := IsAlgClosed.exists_pow_nat_eq x hn
  exact ⟨O.valuation y, (map_pow _ y n).symm⟩
end GlobalTheory
