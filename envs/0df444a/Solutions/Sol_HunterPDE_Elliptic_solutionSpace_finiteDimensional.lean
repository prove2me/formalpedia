-- Prove2me | solution 1 for HunterPDE.Elliptic.solutionSpace_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T21:52:07.175019+00:00
-- url     : https://prove2.me/submissions/87cfdc30-d884-44d1-9195-4bb274f51e4f

import Theorems.Thm_HunterPDE_Elliptic_fredholm_alternative

open MeasureTheory HunterPDE.Elliptic

theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (P : Coeffs n) (hP : P.Admissible Ω)
    (hell : P.UniformlyElliptic Ω) (lam : ℝ) :
    FiniteDimensional ℝ (solutionSpace (Ω := Ω) (form P) (-lam)) := by
  rcases fredholm_alternative Ω hΩ hΩb P hP hell lam with h | h
  · have hz : solutionSpace (Ω := Ω) (form P) (-lam) = ⊥ := by
      apply le_antisymm _ bot_le
      apply Submodule.span_le.mpr
      intro u hu
      exact (Submodule.mem_bot ℝ).mpr (h.2.2 u hu)
    rw [hz]
    infer_instance
  · exact h.2.1
