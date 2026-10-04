-- Prove2me | solution 1 for MDPFinance.MeanVariance.saddle_point_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:21:14.690688+00:00
-- url     : https://prove2.me/submissions/c6a51e50-103e-4fe1-a488-86b92a97c376

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory MDPFinance.MeanVariance

theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (πstar : ℕ → ℝ → (Fin d → ℝ)) (lamstar : ℝ) (hsaddle : M.IsSaddlePoint πstar lamstar) :
    (⨅ π ∈ {π | M.IsAdmissible 0 π}, ⨆ lam ∈ Set.Ici (0 : ℝ), (M.Lagrangian π lam : EReal)) =
        (⨆ lam ∈ Set.Ici (0 : ℝ), ⨅ π ∈ {π | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) ∧
      (⨆ lam ∈ Set.Ici (0 : ℝ), ⨅ π ∈ {π | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) =
        (M.Lagrangian πstar lamstar : EReal) ∧
      M.IsOptimalMV πstar := by
  obtain ⟨hadm, hlam0, hmaxlam, hminpi⟩ := hsaddle
  have hB_le : (⨆ lam ∈ Set.Ici (0 : ℝ), ⨅ π ∈ {π | M.IsAdmissible 0 π},
      (M.Lagrangian π lam : EReal)) ≤ (M.Lagrangian πstar lamstar : EReal) := by
    refine iSup₂_le fun lam hlam => ?_
    exact (iInf₂_le (f := fun π (_ : π ∈ {π | M.IsAdmissible 0 π}) =>
      (M.Lagrangian π lam : EReal)) πstar hadm).trans (EReal.coe_le_coe_iff.mpr (hmaxlam lam hlam))
  have hB_ge : (M.Lagrangian πstar lamstar : EReal) ≤ (⨆ lam ∈ Set.Ici (0 : ℝ),
      ⨅ π ∈ {π | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) := by
    refine le_trans ?_ (le_iSup₂ (f := fun lam (_ : lam ∈ Set.Ici (0 : ℝ)) =>
      ⨅ π ∈ {π | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) lamstar hlam0)
    exact le_iInf₂ fun π hπ => EReal.coe_le_coe_iff.mpr (hminpi π hπ)
  have hA_le : (⨅ π ∈ {π | M.IsAdmissible 0 π}, ⨆ lam ∈ Set.Ici (0 : ℝ),
      (M.Lagrangian π lam : EReal)) ≤ (M.Lagrangian πstar lamstar : EReal) := by
    refine (iInf₂_le (f := fun π (_ : π ∈ {π | M.IsAdmissible 0 π}) =>
      ⨆ lam ∈ Set.Ici (0 : ℝ), (M.Lagrangian π lam : EReal)) πstar hadm).trans ?_
    exact iSup₂_le fun lam hlam => EReal.coe_le_coe_iff.mpr (hmaxlam lam hlam)
  have hA_ge : (M.Lagrangian πstar lamstar : EReal) ≤ (⨅ π ∈ {π | M.IsAdmissible 0 π},
      ⨆ lam ∈ Set.Ici (0 : ℝ), (M.Lagrangian π lam : EReal)) := by
    refine le_iInf₂ fun π hπ => ?_
    exact (EReal.coe_le_coe_iff.mpr (hminpi π hπ)).trans (le_iSup₂ (f := fun lam
      (_ : lam ∈ Set.Ici (0 : ℝ)) => (M.Lagrangian π lam : EReal)) lamstar hlam0)
  refine ⟨(le_antisymm hA_le hA_ge).trans (le_antisymm hB_le hB_ge).symm,
    le_antisymm hB_le hB_ge, hadm, ?_, ?_⟩
  · -- `μ ≤ meanXN πstar`
    have h1 := hmaxlam (lamstar + 1) (by linarith)
    unfold MVMarket.Lagrangian at h1
    nlinarith
  · intro π hπ hμ
    have h1 := hmaxlam (lamstar + 1) (by linarith)
    have h0 := hmaxlam 0 le_rfl
    have h2 := hminpi π hπ
    unfold MVMarket.Lagrangian at h1 h0 h2
    have hm : M.μ ≤ M.meanXN πstar := by nlinarith
    nlinarith [mul_nonneg hlam0 (sub_nonneg.mpr hμ), mul_nonneg hlam0 (sub_nonneg.mpr hm)]

#print axioms solution
