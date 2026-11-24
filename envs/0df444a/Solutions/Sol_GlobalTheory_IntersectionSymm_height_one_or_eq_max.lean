-- Prove2me | solution 1 for GlobalTheory.IntersectionSymm.height_one_or_eq_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:52:10.627802+00:00
-- url     : https://prove2.me/submissions/5026f036-5547-4d20-8d6b-f4e4e12dd5ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors
import Theorems.Thm_GlobalTheory_IntersectionSymm_height_add_dim_quotient_le
import Theorems.Thm_GlobalTheory_IntersectionSymm_arith
import Theorems.Thm_GlobalTheory_IntersectionSymm_not_dim_quotient_le_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.IntersectionSymm
namespace GlobalTheory.IntersectionSymm
theorem _root_.solution {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (p : Ideal A) [hp : p.IsPrime] (h0 : p ≠ ⊥) :
    p.height = 1 ∨ p = maximalIdeal A := by
  by_cases hm : p = maximalIdeal A
  · exact Or.inr hm
  left
  have hne : ¬ p.IsMaximal := fun h => hm (IsLocalRing.eq_maximalIdeal h)
  have h1 := height_add_dim_quotient_le p
  rw [hA] at h1
  have hle := (arith _ _ h1 (not_dim_quotient_le_zero p hne)).1
  have hz : p.height ≠ 0 := by
    intro hz
    rw [Ideal.height_eq_zero_iff] at hz
    exact h0 (le_bot_iff.1 (hz.2 ⟨Ideal.bot_prime, bot_le⟩ bot_le))
  exact le_antisymm hle (ENat.one_le_iff_ne_zero.2 hz)
end GlobalTheory.IntersectionSymm
