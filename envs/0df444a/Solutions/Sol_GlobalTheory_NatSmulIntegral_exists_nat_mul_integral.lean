-- Prove2me | solution 1 for GlobalTheory.NatSmulIntegral.exists_nat_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:39.14186+00:00
-- url     : https://prove2.me/submissions/934de5e6-db36-4390-bdd3-873e18e9fa68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ImportsTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatSmulIntegral
open NumberField
namespace GlobalTheory.NatSmulIntegral
theorem _root_.solution {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ N : ℕ, 0 < N ∧ ∃ a : 𝓞 E, (a : E) = (N : E) * c := by
  have h : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨z, hz, hi⟩ := h.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.2 hz, ?_⟩
  rw [zsmul_eq_mul] at hi
  rcases Int.natAbs_eq z with h1 | h1
  · refine ⟨⟨(z : E) * c, hi⟩, ?_⟩
    have : (z : E) = (z.natAbs : E) := by
      conv_lhs => rw [h1]
      exact Int.cast_natCast _
    rw [← this]; rfl
  · refine ⟨⟨-((z : E) * c), hi.neg⟩, ?_⟩
    have : (z : E) = -(z.natAbs : E) := by
      conv_lhs => rw [h1]
      rw [Int.cast_neg, Int.cast_natCast]
    have h2 : (z.natAbs : E) * c = -((z : E) * c) := by rw [this]; ring
    rw [h2]; rfl
end GlobalTheory.NatSmulIntegral
