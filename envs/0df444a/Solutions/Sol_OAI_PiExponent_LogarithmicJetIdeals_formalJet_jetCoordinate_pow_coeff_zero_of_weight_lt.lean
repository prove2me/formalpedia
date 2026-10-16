-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_jetCoordinate_pow_coeff_zero_of_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T12:46:48.485789+00:00
-- url     : https://prove2.me/submissions/9e815197-9610-411f-a54b-24add3197347

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coeff_pow_zero_of_support_bound
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_jetCoordinate_coeff_zero_of_weight_lt

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (S : ℝ)
    (hweights : ∀ k, 0 < InterpolationMatrix.rowWeights v0 theta w k)
    (he : ∀ k, 0 < e k)
    (hcommon : ∀ k, S = (e k : ℝ) * InterpolationMatrix.rowWeights v0 theta w k)
    (hT : ∀ k, InterpolationMatrix.rowWeights v0 theta w k.succ ≤ (T k : ℝ) * v0)
    (j : Fin K) (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ)
    (ha : (∑ k : Fin (m + 1), InterpolationMatrix.rowWeights v0 theta w k * (a k : ℝ)) < S) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet (fun k => (j.val : ℂ) * r k)
        ((jetCoordinate (fun k => (j.val : ℂ) * r k) T i) ^ e i)) = 0 := by
  rw [map_pow]
  apply OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_pow_zero_of_support_bound
    (wt := InterpolationMatrix.rowWeights v0 theta w)
    (F := AdmissibleFormalInterpolation.formalJet
      (fun k => (j.val : ℂ) * r k)
      (jetCoordinate (fun k => (j.val : ℂ) * r k) T i))
    (B := InterpolationMatrix.rowWeights v0 theta w i)
    (n := e i)
  · intro b hb
    exact OAI.PiExponent.LogarithmicJetIdeals.formalJet_jetCoordinate_coeff_zero_of_weight_lt
      (v0 := v0) (theta := theta) (w := w)
      (c := fun k => (j.val : ℂ) * r k) (T := T) hweights hT i b hb
  · exact he i
  · rw [hcommon i] at ha
    exact ha