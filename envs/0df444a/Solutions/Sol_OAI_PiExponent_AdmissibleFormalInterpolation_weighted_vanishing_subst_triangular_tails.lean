-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weighted_vanishing_subst_triangular_tails
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:47:20.008407+00:00
-- url     : https://prove2.me/submissions/a9fa519c-beec-41fa-b21b-1a6ba6b5b0ff

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weighted_vanishing_subst_of_weight_support
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_triangular_tail_substitution_support
import Mathlib.RingTheory.MvPowerSeries.Substitution

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (T : Fin m → ℕ)
    (R : Fin m → PowerSeries ℂ)
    (hq : ∀ i, 0 < q i)
    (hT : ∀ i : Fin m, q i.succ ≤ (T i : ℝ) * q 0)
    (hR : ∀ (i : Fin m) (k : ℕ), k < T i → PowerSeries.coeff k (R i) = 0)
    (H : ℝ) (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, q i * (a i : ℝ)) < H →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) F = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ i, q i * (a i : ℝ)) < H →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X 0)
            (fun i : Fin m => MvPowerSeries.X i.succ + liftLogSeries m (R i))) F) = 0 := by
  have hs := OAI.PiExponent.AdmissibleFormalInterpolation.triangular_tail_substitution_support
    q T R hq hT hR
  exact OAI.PiExponent.AdmissibleFormalInterpolation.weighted_vanishing_subst_of_weight_support
    q _ hq hs H F hF