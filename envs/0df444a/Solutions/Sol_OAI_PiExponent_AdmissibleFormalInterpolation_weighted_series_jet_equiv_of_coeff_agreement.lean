-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weighted_series_jet_equiv_of_coeff_agreement
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:44:41.589744+00:00
-- url     : https://prove2.me/submissions/8d8bcd38-a071-4f33-82d9-034512429790
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedSeriesJets
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weighted_series_jet_equiv_of_coeff_agreement_nonpos
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weighted_series_jet_equiv_of_coeff_agreement_pos

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (F G : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hFG : ∀ i n, n < N i → PowerSeries.coeff n (F i) = PowerSeries.coeff n (G i)) :
    ∃ E : ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ) ≃ₗ[ℂ]
        ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ),
      ∀ (c : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ),
        E (weightedSeriesJet v0 u H c G P) = weightedSeriesJet v0 u H c F P := by
  rcases le_or_gt H 0 with hH | hH
  · exact OAI.PiExponent.AdmissibleFormalInterpolation.weighted_series_jet_equiv_of_coeff_agreement_nonpos
      v0 u H N F G hv0 hu hN hFG hH
  · exact OAI.PiExponent.AdmissibleFormalInterpolation.weighted_series_jet_equiv_of_coeff_agreement_pos
      v0 u H N F G hv0 hu hN hFG hH