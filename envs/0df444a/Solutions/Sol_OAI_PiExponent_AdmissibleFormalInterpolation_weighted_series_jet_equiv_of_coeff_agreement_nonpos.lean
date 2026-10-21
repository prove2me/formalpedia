-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weighted_series_jet_equiv_of_coeff_agreement_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:18:15.258397+00:00
-- url     : https://prove2.me/submissions/85b436d9-e6fc-4fa8-9344-841434b5c3f6

import Definitions.Def_OAI_PiExponent_WeightedSeriesJets

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

set_option maxHeartbeats 1000000 in
/-- If the height is nonpositive, the strict weighted simplex is empty (the weights are
positive and the exponent vectors are nonnegative), so the two weighted series jets live on an
empty index type and are equal; the required linear equivalence is the identity. -/
theorem solution {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (F G : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hFG : ∀ i n, n < N i → PowerSeries.coeff n (F i) = PowerSeries.coeff n (G i))
    (hH : H ≤ 0) :
    ∃ E : ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ) ≃ₗ[ℂ]
        ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ),
      ∀ (c : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ),
        E (weightedSeriesJet v0 u H c G P) = weightedSeriesJet v0 u H c F P := by
  classical
  have hnonpos : ∀ a : Fin (m + 1) → ℕ,
      a ∈ strictWeightedSimplex (Fin.cases v0 u) H → False := by
    intro a ha
    simp only [strictWeightedSimplex, Finset.mem_filter] at ha
    have hnonneg : 0 ≤ ∑ i, Fin.cases v0 u i * (a i : ℝ) := by
      apply Finset.sum_nonneg
      intro i _
      cases i using Fin.cases with
      | zero =>
          simp only [Fin.cases_zero]
          exact mul_nonneg hv0.le (Nat.cast_nonneg _)
      | succ j =>
          simp only [Fin.cases_succ]
          exact mul_nonneg (hu j).le (Nat.cast_nonneg _)
    linarith [ha.2]
  have hempty : IsEmpty ↥(strictWeightedSimplex (Fin.cases v0 u) H) :=
    ⟨fun a => hnonpos a.1 a.2⟩
  refine ⟨LinearEquiv.refl ℂ _, ?_⟩
  intro c P
  simp only [LinearEquiv.refl_apply]
  funext b
  exact (hempty.false b).elim
