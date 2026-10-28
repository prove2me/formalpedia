-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_vanish_on_ideal_power_of_profile
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T18:31:06.745294+00:00
-- url     : https://prove2.me/submissions/a060c2fa-f61e-485d-b2f8-cbe2cc089d0c

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_coeff_vanish_on_ideal_power_of_ringHom

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (r : Fin m → ℂ)
    (R : ℝ) (n : ℕ) (hn : 0 < n)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (hcoeff : ∀ (Q : MvPolynomial (Fin (m + 1)) ℂ), Q ∈ I →
      ∀ (j : Fin K) (a : Fin (m + 1) → ℕ),
        (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < R →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (AdmissibleFormalInterpolation.formalJet
            (fun i => (j.val : ℂ) * r i) Q) = 0)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ I ^ n)
    (j : Fin K) (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) <
      (n : ℝ) * R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet
        (fun i => (j.val : ℂ) * r i) P) = 0 := by
  exact OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_on_ideal_power_of_ringHom
    (v := InterpolationMatrix.rowWeights v0 theta w) R n hn hv I
    (AdmissibleFormalInterpolation.formalJet (fun i => (j.val : ℂ) * r i)).toRingHom
    (by
      intro Q hQ b hb
      exact hcoeff Q hQ j b hb)
    P hP a ha
