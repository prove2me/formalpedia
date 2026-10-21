-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:28:20.17471+00:00
-- url     : https://prove2.me/submissions/13eb3404-a3f4-450b-815c-01994948a3ed

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_seriesJet_monomial
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_seriesJet_linearExtension

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (D F : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (hH : 0 < H)
    (c : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ) :
    (weightedShear (m := m) v0 u H D).toFun
        (weightedSeriesJet (m := m) v0 u H c F P) =
      weightedSeriesJet (m := m) v0 u H c (fun i => F i + D i) P := by
  apply OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet_linearExtension
    v0 u H N D F hv0 hu hN hD hH c P
  intro e
  exact OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet_monomial
    v0 u H N D F hv0 hu hN hD hH c e
