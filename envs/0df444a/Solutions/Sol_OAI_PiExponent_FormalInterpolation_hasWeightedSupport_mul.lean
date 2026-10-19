-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:52:41.427367+00:00
-- url     : https://prove2.me/submissions/5cda6206-274d-4e8a-b6f5-04cebdf673c9

import Mathlib
import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
theorem solution
    {m : ℕ} (v : Fin (m + 1) → ℝ) (B C : ℝ)
    (F G : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : FormalInterpolation.hasWeightedSupport v B F)
    (hG : FormalInterpolation.hasWeightedSupport v C G) :
    FormalInterpolation.hasWeightedSupport v (B + C) (F * G) := by
  have hev : ∀ p : Fin (m + 1) →₀ ℕ, InterpolationMatrix.exponentVector (⇑p) = p := by
    intro p; unfold InterpolationMatrix.exponentVector; exact Finsupp.equivFunOnFinite_symm_coe p
  intro b hb
  rw [MvPowerSeries.coeff_mul] at hb
  obtain ⟨⟨p, q⟩, hpq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
  have hp : MvPowerSeries.coeff p F ≠ 0 := left_ne_zero_of_mul hne
  have hq : MvPowerSeries.coeff q G ≠ 0 := right_ne_zero_of_mul hne
  have h1 := hF (⇑p) (by rw [hev]; exact hp)
  have h2 := hG (⇑q) (by rw [hev]; exact hq)
  have hb' : ∀ i, (b i : ℝ) = p i + q i := by
    intro i
    have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f i) hpq
    simp [InterpolationMatrix.exponentVector] at this
    exact_mod_cast this.symm
  calc B + C ≤ (∑ i, (p i : ℝ) * v i) + ∑ i, (q i : ℝ) * v i := add_le_add h1 h2
    _ = ∑ i, (b i : ℝ) * v i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [hb']; ring
