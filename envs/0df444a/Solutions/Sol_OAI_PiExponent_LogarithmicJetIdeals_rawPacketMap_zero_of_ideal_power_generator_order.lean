-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.rawPacketMap_zero_of_ideal_power_generator_order
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T17:12:33.953613+00:00
-- url     : https://prove2.me/submissions/016b8732-e444-44af-ab17-f2d2a0cdcab2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coeff_zero_of_simultaneousJetIdeal_pow

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (S : ℝ)
    (hweights : ∀ k, 0 < InterpolationMatrix.rowWeights v0 theta w k)
    (hgen : ∀ (j : Fin K) (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ),
      (∑ k : Fin (m + 1), InterpolationMatrix.rowWeights v0 theta w k * (a k : ℝ)) < S →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet (fun k => (j.val : ℂ) * r k)
          ((jetCoordinate (fun k => (j.val : ℂ) * r k) T i) ^ e i)) = 0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ (simultaneousJetIdeal K r T e) ^ n) :
    rawPacketMap K v0 theta w ((n : ℝ) * S) r P = (fun _ => 0) := by
  funext rho
  change MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
      (AdmissibleFormalInterpolation.formalJet (fun k => (rho.1.val : ℂ) * r k) P) = 0
  apply OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_zero_of_simultaneousJetIdeal_pow
      K v0 theta w r T e S hweights hgen n P hP rho.1 rho.2.val
  have hrange : rho.2.val ∈ strictWeightedSimplex
      (InterpolationMatrix.rowWeights v0 theta w) ((n : ℝ) * S) := rho.2.property
  have hrange' := hrange
  simp only [strictWeightedSimplex, Finset.mem_filter] at hrange'
  exact hrange'.2