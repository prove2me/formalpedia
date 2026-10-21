-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weighted_series_jet_equiv_of_coeff_agreement_pos
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:01:52.528772+00:00
-- url     : https://prove2.me/submissions/ee05dfb5-ae89-412e-b8e1-e6486b895c9e

import Definitions.Def_OAI_PiExponent_WeightedSeriesJets
import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_neg_leftInverse
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_seriesJet

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

set_option maxHeartbeats 1000000

theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (F G : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hFG : ∀ i n, n < N i → PowerSeries.coeff n (F i) = PowerSeries.coeff n (G i))
    (hH : 0 < H) :
    ∃ E : ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ) ≃ₗ[ℂ]
        ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ),
      ∀ (c : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ),
        E (weightedSeriesJet v0 u H c G P) = weightedSeriesJet v0 u H c F P := by
  classical
  let D : Fin m → PowerSeries ℂ := fun i => F i - G i
  have hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0 := by
    intro i n hn
    change PowerSeries.coeff n (F i - G i) = 0
    rw [map_sub, hFG i n hn, sub_self]
  have hnegD : ∀ i n, n < N i → PowerSeries.coeff n (-D i) = 0 := by
    intro i n hn
    rw [map_neg, hD i n hn, neg_zero]
  let T := weightedShear (m := m) v0 u H D
  let S := weightedShear (m := m) v0 u H (fun i : Fin m => -D i)
  have hST : S ∘ₗ T = LinearMap.id := by
    exact weightedShear_neg_leftInverse v0 u H N D hv0 hu hN hD hH
  have hTS : T ∘ₗ S = LinearMap.id := by
    simpa only [T, S, neg_neg] using
      (weightedShear_neg_leftInverse v0 u H N (fun i : Fin m => -D i)
        hv0 hu hN hnegD hH)
  let E : ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ) ≃ₗ[ℂ]
      ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ) :=
    LinearEquiv.ofLinearMap T S hTS hST
  refine ⟨E, ?_⟩
  intro c P
  have hGD : (fun i => G i + D i) = F := by
    funext i
    change G i + (F i - G i) = F i
    rw [add_comm, sub_add_cancel]
  change (weightedShear (m := m) v0 u H D).toFun
      (weightedSeriesJet v0 u H c G P) = weightedSeriesJet v0 u H c F P
  simpa only [hGD] using
    (weightedShear_seriesJet v0 u H N D G hv0 hu hN hD hH c P)
