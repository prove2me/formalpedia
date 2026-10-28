-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_eq_card_sub_trdeg_toNat
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:32:42.943473+00:00
-- url     : https://prove2.me/submissions/e6e625f3-8708-4ac1-9551-945dc13fb154

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_prime_height_add_trdeg_eq_card

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height = ↑((m + 1) -
      (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat) := by
  let t := (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat
  let n := m + 1
  have h := OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_add_trdeg_eq_card P
  have h' : P.height + (t : ℕ∞) = (n : ℕ∞) := by
    simpa [t, n] using h
  have hfinite : P.height ≠ ⊤ := by
    intro hp
    rw [hp] at h'
    simp at h'
  obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp hfinite
  have h'' := h'
  rw [← hp] at h''
  have hnat : p + t = n := by
    exact_mod_cast h''
  have hsub : p = n - t := Nat.eq_sub_of_add_eq hnat
  change P.height = ↑(n - t)
  rw [← hp, hsub]