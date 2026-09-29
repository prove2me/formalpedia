-- Prove2me | solution 1 for MeasureTheory.setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b6c69f9b-699a-55cf-af25-e4e943afc393

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap

set_option autoImplicit false

open MeasureTheory Set

namespace OcLaplaceGap
theorem volume_abs_le (ρ : ℝ) (hρ : 0 ≤ ρ) : volume {v : ℝ | |v| ≤ ρ} = ENNReal.ofReal (2 * ρ) := by
  rw [show {v : ℝ | |v| ≤ ρ} = Icc (-ρ) ρ by ext v; simp [abs_le], Real.volume_Icc]
  congr 1; ring

theorem setIntegral_exp_mul_compl_le
    (φ : ℝ → ℝ) (hφm : Measurable φ) (hφmax : ∀ v, φ v ≤ φ 0)
    (γ δ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ)
    (hout : ∀ v, δ < |v| → φ v ≤ φ 0 - γ) (hin : ∀ v, |v| ≤ ρ → φ 0 - γ / 2 ≤ φ v)
    (H : ℝ → ℝ) (Λ₀ : ℝ) (hΛ₀ : 0 ≤ Λ₀)
    (hHint : Integrable (fun v => Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v))
    (hHloc : IntegrableOn H {v | |v| ≤ δ})
    (h : ℝ → ℝ) (hhm : Measurable h) (hh0 : ∀ v, 0 ≤ h v) (hhH : ∀ v, h v ≤ H v)
    (cm : ℝ) (hhin : ∀ v, |v| ≤ ρ → Real.exp cm ≤ h v)
    (Λ : ℝ) (hΛ : Λ₀ ≤ Λ) :
    IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | δ < |v|} ∧
    IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | |v| ≤ δ} ∧
    ∫ v in {v | δ < |v|}, Real.exp (Λ * φ v) * h v ≤
      ((∫ v, Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v) * Real.exp (-cm) / (2 * ρ)) * Real.exp (-(Λ * γ / 2)) *
        ∫ v in {v | |v| ≤ δ}, Real.exp (Λ * φ v) * h v := by
  have hSout : MeasurableSet {v : ℝ | δ < |v|} := measurableSet_lt measurable_const continuous_abs.measurable
  have hSin : MeasurableSet {v : ℝ | |v| ≤ δ} := measurableSet_le continuous_abs.measurable measurable_const
  have hSρ : MeasurableSet {v : ℝ | |v| ≤ ρ} := measurableSet_le continuous_abs.measurable measurable_const
  have hmeas : Measurable (fun v => Real.exp (Λ * φ v) * h v) :=
    (Real.measurable_exp.comp (measurable_const.mul hφm)).mul hhm
  have hnn : ∀ v, 0 ≤ Real.exp (Λ * φ v) * h v := fun v => mul_nonneg (Real.exp_nonneg _) (hh0 v)
  have hH0 : ∀ v, 0 ≤ H v := fun v => (hh0 v).trans (hhH v)
  set C : ℝ := ∫ v, Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v with hC

  have hpt : ∀ v, δ < |v| → Real.exp (Λ * φ v) * h v ≤
      Real.exp (Λ * (φ 0 - γ)) * (Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v) := by
    intro v hv
    have hneg : φ v - φ 0 + γ ≤ 0 := by linarith [hout v hv]
    have h1 : Λ * φ v ≤ Λ * (φ 0 - γ) + Λ₀ * (φ v - φ 0 + γ) := by nlinarith
    calc Real.exp (Λ * φ v) * h v ≤ Real.exp (Λ * (φ 0 - γ) + Λ₀ * (φ v - φ 0 + γ)) * H v :=
          mul_le_mul (Real.exp_le_exp.2 h1) (hhH v) (hh0 v) (Real.exp_nonneg _)
      _ = _ := by rw [Real.exp_add]; ring

  have hIout : IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | δ < |v|} := by
    refine Integrable.mono' ((hHint.const_mul (Real.exp (Λ * (φ 0 - γ)))).integrableOn) hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hSout).2 (ae_of_all _ (fun v hv => ?_))
    rw [Real.norm_of_nonneg (hnn v)]
    exact hpt v hv
  have hIin : IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | |v| ≤ δ} := by
    refine Integrable.mono' ((hHloc.const_mul (Real.exp (Λ * φ 0)))) hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hSin).2 (ae_of_all _ (fun v _ => ?_))
    rw [Real.norm_of_nonneg (hnn v)]
    refine mul_le_mul (Real.exp_le_exp.2 ?_) (hhH v) (hh0 v) (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_left (hφmax v) (hΛ₀.trans hΛ)
  refine ⟨hIout, hIin, ?_⟩

  have hout_le : ∫ v in {v | δ < |v|}, Real.exp (Λ * φ v) * h v ≤ Real.exp (Λ * (φ 0 - γ)) * C := by
    calc ∫ v in {v | δ < |v|}, Real.exp (Λ * φ v) * h v
        ≤ ∫ v in {v | δ < |v|}, Real.exp (Λ * (φ 0 - γ)) * (Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v) :=
          setIntegral_mono_on hIout (hHint.const_mul _).integrableOn hSout hpt
      _ = Real.exp (Λ * (φ 0 - γ)) * ∫ v in {v | δ < |v|}, Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v := integral_const_mul _ _
      _ ≤ Real.exp (Λ * (φ 0 - γ)) * C := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
          exact setIntegral_le_integral hHint (ae_of_all _ (fun v => mul_nonneg (Real.exp_nonneg _) (hH0 v)))

  have hin_ge : 2 * ρ * Real.exp cm * Real.exp (Λ * (φ 0 - γ / 2)) ≤ ∫ v in {v | |v| ≤ δ}, Real.exp (Λ * φ v) * h v := by
    have hsub : {v : ℝ | |v| ≤ ρ} ⊆ {v | |v| ≤ δ} := fun v hv => le_trans hv hρδ
    have hΛ0 : 0 ≤ Λ := hΛ₀.trans hΛ
    have hconst : ∫ v in {v : ℝ | |v| ≤ ρ}, Real.exp cm * Real.exp (Λ * (φ 0 - γ / 2))
        = 2 * ρ * Real.exp cm * Real.exp (Λ * (φ 0 - γ / 2)) := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, volume_abs_le ρ hρ.le, ENNReal.toReal_ofReal (by positivity)]
      ring
    have hstep1 : ∫ v in {v : ℝ | |v| ≤ ρ}, Real.exp cm * Real.exp (Λ * (φ 0 - γ / 2))
        ≤ ∫ v in {v : ℝ | |v| ≤ ρ}, Real.exp (Λ * φ v) * h v := by
      refine setIntegral_mono_on ?_ (hIin.mono_set hsub) hSρ (fun v hv => ?_)
      · refine integrableOn_const ?_
        rw [volume_abs_le ρ hρ.le]; exact ENNReal.ofReal_ne_top
      · rw [mul_comm (Real.exp cm)]
        exact mul_le_mul (Real.exp_le_exp.2 (by nlinarith [hin v hv, hΛ₀.trans hΛ])) (hhin v hv) (Real.exp_nonneg _) (Real.exp_nonneg _)
    have hstep2 : ∫ v in {v : ℝ | |v| ≤ ρ}, Real.exp (Λ * φ v) * h v ≤ ∫ v in {v | |v| ≤ δ}, Real.exp (Λ * φ v) * h v :=
      setIntegral_mono_set hIin (ae_of_all _ hnn) (ae_of_all _ hsub)
    linarith

  have hρ2 : 0 < 2 * ρ := by positivity
  have key : Real.exp (Λ * (φ 0 - γ)) * C
      = (C * Real.exp (-cm) / (2 * ρ)) * Real.exp (-(Λ * γ / 2)) * (2 * ρ * Real.exp cm * Real.exp (Λ * (φ 0 - γ / 2))) := by
    rw [Real.exp_neg, show Λ * (φ 0 - γ) = -(Λ * γ / 2) + Λ * (φ 0 - γ / 2) by ring, Real.exp_add]
    field_simp
  have hcoef : 0 ≤ (C * Real.exp (-cm) / (2 * ρ)) * Real.exp (-(Λ * γ / 2)) := by
    have hC0 : 0 ≤ C := integral_nonneg (fun v => mul_nonneg (Real.exp_nonneg _) (hH0 v))
    positivity
  calc ∫ v in {v | δ < |v|}, Real.exp (Λ * φ v) * h v ≤ Real.exp (Λ * (φ 0 - γ)) * C := hout_le
    _ = (C * Real.exp (-cm) / (2 * ρ)) * Real.exp (-(Λ * γ / 2)) * (2 * ρ * Real.exp cm * Real.exp (Λ * (φ 0 - γ / 2))) := key
    _ ≤ _ := mul_le_mul_of_nonneg_left hin_ge hcoef

end OcLaplaceGap

theorem solution
    (φ : ℝ → ℝ) (hφm : Measurable φ) (hφmax : ∀ v, φ v ≤ φ 0)
    (γ δ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ)
    (hout : ∀ v, δ < |v| → φ v ≤ φ 0 - γ) (hin : ∀ v, |v| ≤ ρ → φ 0 - γ / 2 ≤ φ v)
    (H : ℝ → ℝ) (Λ₀ : ℝ) (hΛ₀ : 0 ≤ Λ₀)
    (hHint : Integrable (fun v => Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v))
    (hHloc : IntegrableOn H {v | |v| ≤ δ})
    (h : ℝ → ℝ) (hhm : Measurable h) (hh0 : ∀ v, 0 ≤ h v) (hhH : ∀ v, h v ≤ H v)
    (cm : ℝ) (hhin : ∀ v, |v| ≤ ρ → Real.exp cm ≤ h v)
    (Λ : ℝ) (hΛ : Λ₀ ≤ Λ) :
    IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | δ < |v|} ∧
    IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | |v| ≤ δ} ∧
    ∫ v in {v | δ < |v|}, Real.exp (Λ * φ v) * h v ≤
      ((∫ v, Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v) * Real.exp (-cm) / (2 * ρ)) * Real.exp (-(Λ * γ / 2)) *
        ∫ v in {v | |v| ≤ δ}, Real.exp (Λ * φ v) * h v :=
  OcLaplaceGap.setIntegral_exp_mul_compl_le φ hφm hφmax γ δ ρ hγ hρ hρδ hout hin H Λ₀ hΛ₀ hHint hHloc h hhm hh0 hhH cm hhin Λ hΛ

end S_MeasureTheory_setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap
end P2MW
export P2MW.S_MeasureTheory_setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap (solution)
