-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_support_succ
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T16:01:28.021343+00:00
-- url     : https://prove2.me/submissions/98714876-8d40-4134-9f0c-577981d46211

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_generator_formalJet_decomposition_succ
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_generator_logTail_coeff_support_succ

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation OAI.PiExponent.LogarithmicJetIdeals

theorem solution {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (b : Fin (m + 1) → ℕ) (i : Fin m) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (AdmissibleFormalInterpolation.formalJet c
        (OAI.PiExponent.LogarithmicJetIdeals.jetCoordinate c T i.succ)) ≠ 0 →
      (∀ j : Fin (m + 1), b j = if j = i.succ then 1 else 0) ∨
        (T i ≤ b 0 ∧ ∀ j : Fin m, b j.succ = 0) := by
  intro h
  have hdec := OAI.PiExponent.LogarithmicJetIdeals.local_jet_generator_formalJet_decomposition_succ c T b i
  rw [hdec] at h
  by_cases hX : MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (MvPowerSeries.X i.succ : MvPowerSeries (Fin (m + 1)) ℂ) = 0
  · right
    have hL : MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (AdmissibleFormalInterpolation.liftLogSeries m
          (PowerSeries.log ℂ -
            (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ))) ≠ 0 := by
      intro h0
      exact h (by rw [hX, h0, add_zero])
    have hc := OAI.PiExponent.LogarithmicJetIdeals.local_jet_generator_logTail_coeff_support_succ T b i hL
    exact ⟨hc.2, hc.1⟩
  · left
    rw [MvPowerSeries.coeff_X] at hX
    have hb : InterpolationMatrix.exponentVector b = Finsupp.single i.succ 1 := by
      by_contra hne
      rw [if_neg hne] at hX
      exact hX rfl
    intro j
    have hj := congrArg (fun f : Fin (m + 1) →₀ ℕ => f j) hb
    simpa [InterpolationMatrix.exponentVector, Finsupp.single_apply, eq_comm] using hj
