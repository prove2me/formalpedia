-- Prove2me | solution 1 for GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:12.54185+00:00
-- url     : https://prove2.me/submissions/516a5be4-8465-47f3-a4f7-d74fa94277f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinMatrixReducedOfCharpolySeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K), N.charpoly.Separable →
      ∀ g ∈ Algebra.adjoin K {N}, ∀ m : ℕ, g ^ m = 0 → g = 0 := by
  intro K _ n N hsep g hg m hm
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · rw [pow_zero] at hm
    calc g = g * 1 := (mul_one g).symm
      _ = 0 := by rw [hm, mul_zero]
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hg
  obtain ⟨P, rfl⟩ := hg
  have h1 : minpoly K N ∣ P ^ m := minpoly.dvd K N (by rw [map_pow]; exact hm)
  have hs : (minpoly K N).Separable := hsep.of_dvd (Matrix.minpoly_dvd_charpoly N)
  have h2 : minpoly K N ∣ P := (hs.squarefree.dvd_pow_iff_dvd hmpos.ne').mp h1
  obtain ⟨q, hq⟩ := h2
  show aeval N P = 0
  rw [hq, map_mul, minpoly.aeval, zero_mul]
end GlobalTheory
