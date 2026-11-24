-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.ncard_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:46:34.033381+00:00
-- url     : https://prove2.me/submissions/5ac1ae01-ee84-48ee-a9a0-17f3e3f3c0b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) (k : ℕ) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I = k ∧ J ∣ I}.ncard
      = if Ideal.absNorm J ∣ k then idealCount K (k / Ideal.absNorm J) else 0 := by
  have hN : 0 < Ideal.absNorm J := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ hN, idealCount, ← Set.ncard_image_of_injective
      {I | Ideal.absNorm I = m} (mul_right_injective₀ (show J ≠ 0 from hJ))]
    congr 1
    ext I
    constructor
    · rintro ⟨h1, I', rfl⟩
      rw [map_mul] at h1
      exact ⟨I', Nat.eq_of_mul_eq_mul_left hN h1, rfl⟩
    · rintro ⟨I', h1, rfl⟩
      exact ⟨by rw [map_mul, h1], dvd_mul_right _ _⟩
  · convert Set.ncard_empty (Ideal (𝓞 K))
    ext I
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl h'
    exact h (map_dvd _ h')
end GlobalTheory.QuadraticZeta
