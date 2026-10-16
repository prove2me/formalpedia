-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.mvPowerSeries_span_weighted_coeff_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:38:33.655163+00:00
-- url     : https://prove2.me/submissions/cf80e91a-2cde-44d2-bcb6-d036cc61f599

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (ω : Fin (m + 1) → ℝ) (R : ℝ)
    (hω : ∀ j : Fin (m + 1), 0 < ω j)
    (S : Set (MvPowerSeries (Fin (m + 1)) ℂ))
    (hS : ∀ F ∈ S, ∀ b : Fin (m + 1) → ℕ,
      (∑ j, ω j * (b j : ℝ)) < R →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) F = 0)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ j, ω j * (a j : ℝ)) < R)
    (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : F ∈ Ideal.span S) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) F = 0 := by
  classical
  -- Vanishing throughout the strict weighted region defines an ideal.
  let J : Ideal (MvPowerSeries (Fin (m + 1)) ℂ) :=
    { carrier := {G | ∀ b : Fin (m + 1) → ℕ,
        (∑ j, ω j * (b j : ℝ)) < R →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) G = 0}
      zero_mem' := by
        intro b hb
        simp
      add_mem' := by
        intro G H hG hH b hb
        simp only [map_add, hG b hb, hH b hb, add_zero]
      smul_mem' := by
        intro H G hG b hb
        change MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) (H * G) = 0
        rw [MvPowerSeries.coeff_mul]
        apply Finset.sum_eq_zero
        intro p hp
        have hpadd : p.1 + p.2 = InterpolationMatrix.exponentVector b :=
          Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        have hle : ∀ j : Fin (m + 1), p.2 j ≤ b j := by
          intro j
          calc
            p.2 j ≤ p.1 j + p.2 j := Nat.le_add_left _ _
            _ = (InterpolationMatrix.exponentVector b) j :=
              congrArg (fun d : Fin (m + 1) →₀ ℕ => d j) hpadd
            _ = b j := rfl
        have hweight : (∑ j, ω j * (p.2 j : ℝ)) < R := by
          refine lt_of_le_of_lt (Finset.sum_le_sum ?_) hb
          intro j hj
          exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hle j)) (hω j).le
        have hexp : InterpolationMatrix.exponentVector (fun j => p.2 j) = p.2 :=
          Finsupp.equivFunOnFinite_symm_coe p.2
        have hcoeff : MvPowerSeries.coeff p.2 G = 0 := by
          simpa only [hexp] using hG (fun j => p.2 j) hweight
        rw [hcoeff, mul_zero] }
  have hspan : Ideal.span S ≤ J := Ideal.span_le.mpr (by
    intro G hG
    exact hS G hG)
  exact hspan hF a ha
