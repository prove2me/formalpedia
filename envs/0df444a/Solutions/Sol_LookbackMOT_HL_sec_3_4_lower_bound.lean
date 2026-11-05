-- Prove2me | solution 1 for LookbackMOT.HL.sec_3_4_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:32:48.637617+00:00
-- url     : https://prove2.me/submissions/2a8a04e2-5219-4927-879a-73bc30c7ef79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting
import Theorems.Thm_LookbackMOT_HL_azema_yor

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

lemma LB_expect_of_integrable' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {φ : Ω → ℝ}
    (hφ : Integrable φ P) : expect P φ = ((∫ ω, φ ω ∂P : ℝ) : EReal) := by
  unfold expect
  have h1 : ∫⁻ ω, ENNReal.ofReal (-φ ω) ∂P < ⊤ := hφ.neg.lintegral_lt_top
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ, EReal.coe_sub,
    EReal.coe_ennreal_toReal hφ.lintegral_lt_top.ne,
    EReal.coe_ennreal_toReal h1.ne]

lemma LB_expect_mono {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {φ ψ : Ω → ℝ}
    (h : ∀ ω, φ ω ≤ ψ ω) : expect P φ ≤ expect P ψ := by
  unfold expect
  apply EReal.sub_le_sub
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (h ω))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (by linarith [h ω]))

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ) (hB : IsFBrownian P ℱ B)
    (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (hξ : (⨆ τ : Ω → WithTop ℝ≥0, ⨆ (_ : IsUIStop P ℱ (shift X₀ B) τ),
      ∫⁻ ω, ENNReal.ofReal (g (runMaxUpTo (shift X₀ B) τ ω)) ∂P) < ⊤)
    (ν : Measure ℝ) (hν : IsHLTransform μ ν) (hνg : Integrable g ν) :
    ((∫ x, g x ∂ν : ℝ) : EReal) ≤ U P ℱ B X₀ μ g := by
  obtain ⟨hUI, hXlaw, hMlaw⟩ := LookbackMOT.HL.azema_yor P ℱ B hB X₀ μ hμ1 hmean ν hν
  set τ := tauStar B X₀ μ
  set M := runMaxUpTo (shift X₀ B) τ
  set Xτ := stoppedValue (shift X₀ B) τ
  have hgM : Integrable (fun ω => g (M ω)) P := by
    have h := hνg
    rw [← hMlaw.map_eq] at h
    exact (integrable_map_measure h.aestronglyMeasurable hMlaw.aemeasurable).mp h
  have e1 : ∫ ω, g (M ω) ∂P = ∫ x, g x ∂ν :=
    hMlaw.integral_comp (f := g) hνg.aestronglyMeasurable
  unfold U
  refine le_iInf₂ (fun lam hlam => ?_)
  have hlint : Integrable lam μ := hlam.2.1
  have hLX : Integrable (fun ω => lam (Xτ ω)) P := by
    have h := hlint
    rw [← hXlaw.map_eq] at h
    exact (integrable_map_measure h.aestronglyMeasurable hXlaw.aemeasurable).mp h
  have e2 : ∫ ω, lam (Xτ ω) ∂P = ∫ x, lam x ∂μ :=
    hXlaw.integral_comp (f := lam) hlint.aestronglyMeasurable
  have hstop : (((∫ x, g x ∂ν) - ∫ x, lam x ∂μ : ℝ) : EReal) ≤ stopValue P ℱ B g lam X₀ X₀ := by
    have h1 : expect P (fun ω => g (M ω) - lam (Xτ ω)) =
        (((∫ x, g x ∂ν) - ∫ x, lam x ∂μ : ℝ) : EReal) := by
      rw [LB_expect_of_integrable' P (φ := fun ω => g (M ω) - lam (Xτ ω)) (hgM.sub hLX),
        integral_sub hgM hLX, e1, e2]
    rw [← h1]
    calc expect P (fun ω => g (M ω) - lam (Xτ ω))
        ≤ expect P (fun ω => g (max X₀ (M ω)) - lam (Xτ ω)) :=
          LB_expect_mono P (fun ω => by linarith [hgmono (le_max_right X₀ (M ω))])
      _ ≤ stopValue P ℱ B g lam X₀ X₀ := by
          unfold stopValue
          exact le_iSup₂ (f := fun τ' (_ : IsUIStop P ℱ (shift X₀ B) τ') =>
            expect P (fun ω => g (max X₀ (runMaxUpTo (shift X₀ B) τ' ω)) -
              lam (stoppedValue (shift X₀ B) τ' ω))) τ hUI
  calc ((∫ x, g x ∂ν : ℝ) : EReal)
      = ((∫ x, lam x ∂μ : ℝ) : EReal) + (((∫ x, g x ∂ν) - ∫ x, lam x ∂μ : ℝ) : EReal) := by
        rw [← EReal.coe_add]; congr 1; ring
    _ ≤ ((∫ x, lam x ∂μ : ℝ) : EReal) + stopValue P ℱ B g lam X₀ X₀ := by
        gcongr
