-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_local_logarithmic_interpolation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T06:30:52.37022+00:00
-- url     : https://prove2.me/submissions/dec08b77-0131-4705-9b69-c88cfb794f51
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_polynomial_coefficient_interpolation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_formalJet_polynomial_approximation
open OAI.PiExponent
theorem solution
    {m : ℕ} (c : Fin m → ℂ) (S : Finset (Fin (m + 1) → ℕ)) :
    ∀ y : ↥ S → ℂ, ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ a : ↥ S,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet c P) = y a := by
  classical
  intro y
  obtain ⟨Q, hQ⟩ := FormalInterpolation.finite_polynomial_coefficient_interpolation S y
  obtain ⟨P, hP⟩ := FormalInterpolation.finite_formalJet_polynomial_approximation c S Q
  refine ⟨P, ?_⟩
  intro a
  rw [hP a, hQ a]