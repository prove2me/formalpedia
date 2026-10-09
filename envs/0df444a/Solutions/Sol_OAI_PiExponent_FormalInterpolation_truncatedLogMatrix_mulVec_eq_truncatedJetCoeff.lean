-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedLogMatrix_mulVec_eq_truncatedJetCoeff
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-08T18:15:03.719894+00:00
-- url     : https://prove2.me/submissions/54a8fd09-540c-4c82-acfd-7f6fae179471

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators
set_option maxHeartbeats 1000000
noncomputable section

private def badPolynomial : FormalInterpolation.WeightedPolynomial 0
    (Fin.elim0 : Fin 0 → ℝ) 1 :=
  ⟨MvPolynomial.X 0, by
    intro a ha
    simp [InterpolationMatrix.columnWeights]⟩

private def badRow : InterpolationMatrix.Row 1 1 1 (Fin.elim0 : Fin 0 → ℝ) 1 :=
  (0, ⟨fun _ => 0, by
    simp [strictWeightedSimplex, realWeightedSimplex, InterpolationMatrix.rowWeights]⟩)

private theorem badColumn (c : InterpolationMatrix.Column 0
    (Fin.elim0 : Fin 0 → ℝ) 1) : c.val 0 = 0 := by
  have hc := c.property
  simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range] at hc
  have h := hc.1 0
  simp [InterpolationMatrix.columnWeights] at h
  omega

theorem counterexample :
    (InterpolationMatrix.truncatedLogMatrix 1 0 1 1 (Fin.elim0 : Fin 0 → ℝ) 1
      Fin.elim0 Fin.elim0).mulVecLin
        (fun c : InterpolationMatrix.Column 0 (Fin.elim0 : Fin 0 → ℝ) 1 =>
          badPolynomial.val.coeff (InterpolationMatrix.exponentVector c.1)) badRow ≠
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector badRow.2.val)
        (MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
          (fun i : Fin 0 => MvPowerSeries.C ((badRow.1.val : ℂ) * Fin.elim0 i) +
            MvPowerSeries.X i.succ + FormalInterpolation.liftSeries 0
              ((PowerSeries.trunc (Fin.elim0 i) (PowerSeries.log ℂ) : Polynomial ℂ) :
                PowerSeries ℂ))) badPolynomial.val) := by
  classical
  have hc : (fun c : InterpolationMatrix.Column 0 (Fin.elim0 : Fin 0 → ℝ) 1 =>
      badPolynomial.val.coeff (InterpolationMatrix.exponentVector c.1)) = 0 := by
    funext c
    have he : InterpolationMatrix.exponentVector c.val = 0 := by
      ext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact badColumn c
    simp [he, badPolynomial]
  rw [hc, map_zero]
  have hrow : badRow.2.val = fun _ : Fin 1 => 0 := rfl
  have hidx : InterpolationMatrix.exponentVector badRow.2.val = 0 := by
    ext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [hidx]
  simp [badPolynomial, badRow, InterpolationMatrix.exponentVector,
    MvPowerSeries.coeff_zero_X, hrow]

theorem solution :
    ¬ (∀ {m : Nat} (K : Nat) (w0 v0 theta H : Real) (w : Fin m → Real)
        (T : Fin m → Nat) (r : Fin m → Complex)
        (P : FormalInterpolation.WeightedPolynomial w0 w H),
      ∀ rho : InterpolationMatrix.Row K v0 theta w H,
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
            (fun c : InterpolationMatrix.Column w0 w H =>
              P.val.coeff (InterpolationMatrix.exponentVector c.1)) rho =
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
            (MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
              (fun i => MvPowerSeries.C ((rho.1.val : Complex) * r i) +
                MvPowerSeries.X i.succ +
                FormalInterpolation.liftSeries m
                  ((PowerSeries.trunc (T i) (PowerSeries.log Complex) : Polynomial Complex) :
                    PowerSeries Complex))) P.val)) := by
  intro h
  have hbad := h (m := 0) 1 0 1 1 1 (Fin.elim0 : Fin 0 → Real)
    (Fin.elim0 : Fin 0 → Nat) (Fin.elim0 : Fin 0 → Complex) badPolynomial
  exact counterexample (hbad badRow)
