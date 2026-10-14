-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.ideal_power_raw_packet_of_coefficient_profile
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T18:22:06.766532+00:00
-- url     : https://prove2.me/submissions/cbc220a0-36a4-41de-a8cb-dcb8cf0abba7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coeff_vanish_on_ideal_power_of_profile

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (r : Fin m → ℂ)
    (R : ℝ) (n : ℕ)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (hcoeff : ∀ (Q : MvPolynomial (Fin (m + 1)) ℂ), Q ∈ I →
      ∀ (j : Fin K) (a : Fin (m + 1) → ℕ),
        (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < R →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (AdmissibleFormalInterpolation.formalJet
            (fun i => (j.val : ℂ) * r i) Q) = 0)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ I ^ n) :
    rawPacketMap K v0 theta w ((n : ℝ) * R) r P = 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    funext ρ
    have hmem := ρ.2.property
    have hlt :
        (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (ρ.2.val i : ℝ)) < 0 := by
      simpa using (Finset.mem_filter.mp hmem).2
    have hnonneg :
        0 ≤ ∑ i, InterpolationMatrix.rowWeights v0 theta w i * (ρ.2.val i : ℝ) := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (le_of_lt (hv i)) (Nat.cast_nonneg _)
    exact (not_lt_of_ge hnonneg hlt).elim
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    funext ρ
    change MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)
      (AdmissibleFormalInterpolation.formalJet (fun i => (ρ.1.val : ℂ) * r i) P) = 0
    apply OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_vanish_on_ideal_power_of_profile
      K v0 theta w r R n hnpos hv I hcoeff P hP ρ.1 ρ.2.val
    exact (Finset.mem_filter.mp ρ.2.property).2
