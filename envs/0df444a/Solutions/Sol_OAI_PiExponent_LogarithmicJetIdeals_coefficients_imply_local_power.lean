-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coefficients_imply_local_power
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T12:18:16.36937+00:00
-- url     : https://prove2.me/submissions/b4fb26e0-fcb3-4852-8848-6a6f1fcdabc1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weightedStrictSimplex_mem_of_sum_lt
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_low_weight_formal_coefficients_imply_local_power

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (R : ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hR : 0 < R)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ j : Fin K, ∀ a : Fin (m + 1) → ℕ,
      a ∈ strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w)
        (((n + m : ℕ) : ℝ) * R) →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet
          (fun i => (j.val : ℂ) * r i) P) = 0) :
    ∀ j : Fin K,
      P ∈ (localJetIdeal (fun i => (j.val : ℂ) * r i) T e) ^ n := by
  intro j
  apply OAI.PiExponent.LogarithmicJetIdeals.low_weight_formal_coefficients_imply_local_power
    (v0 := v0) (theta := theta) (w := w) (R := R)
    (c := fun i => (j.val : ℂ) * r i) (T := T) (e := e)
    hR hv he hscale hT n P
  intro a ha
  exact hcoeff j a
    (OAI.PiExponent.LogarithmicJetIdeals.weightedStrictSimplex_mem_of_sum_lt
      (InterpolationMatrix.rowWeights v0 theta w)
      (((n + m : ℕ) : ℝ) * R) hv a ha)