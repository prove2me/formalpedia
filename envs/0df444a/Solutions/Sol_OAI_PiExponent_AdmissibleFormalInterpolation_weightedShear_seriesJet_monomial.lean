-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:32:56.300206+00:00
-- url     : https://prove2.me/submissions/ff98bc23-7259-49dc-8509-20285ae21e14

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_seriesJet

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (D F : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (hH : 0 < H)
    (c : Fin m → ℂ) (e : Fin (m + 1) →₀ ℕ) :
    (weightedShear (m := m) v0 u H D).toFun
        (weightedSeriesJet (m := m) v0 u H c F
          (MvPolynomial.monomial e 1)) =
      weightedSeriesJet (m := m) v0 u H c (fun i => F i + D i)
        (MvPolynomial.monomial e 1) := by
  exact OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet
    (m := m) v0 u H N D F hv0 hu hN hD hH c (MvPolynomial.monomial e 1)