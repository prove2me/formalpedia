-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_logarithmic_jet_gluing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T18:32:00.358643+00:00
-- url     : https://prove2.me/submissions/e5e4c41e-1a8b-49e8-8a40-7b3e901b5c7d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_logarithmic_jet_gluing_varying_sets

open OAI.PiExponent

theorem solution
    {m : ℕ} {J : Type*} [Fintype J]
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (S : Finset (Fin (m + 1) → ℕ))
    (Q : J → MvPolynomial (Fin (m + 1)) ℂ) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ j : J, ∀ a : {a // a ∈ S},
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet (c j) P) =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet (c j) (Q j)) := by
  exact FormalInterpolation.finite_logarithmic_jet_gluing_varying_sets
    c hc (fun _ => S) Q
