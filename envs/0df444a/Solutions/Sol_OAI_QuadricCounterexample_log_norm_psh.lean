-- Prove2me | solution 1 for OAI.QuadricCounterexample.log_norm_psh
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T15:58:52.236794+00:00
-- url     : https://prove2.me/submissions/cb4af9d6-28dc-447c-987c-8768855ef4c2

import Mathlib
import Definitions.Def_OAIQWQC001

section
-- module Solutions.OAIQW_QuadricCounterexample.Removability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric

open scoped Pointwise
noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

open Real

theorem radialIntegral_of_circle_means {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hu : ContinuousOn u (closedBall c R))
    (hm : ∀ a ∈ closedBall (0 : ℂ) 1,
      circleAverage (fun z ↦ u (c+a*z)) 0 R = u c) :
    radialIntegral u c (R : ℂ) = (volume (closedBall (0 : ℂ) 1)).toReal * u c := by
  have hmap (a : ℂ) (ha : a ∈ closedBall (0 : ℂ) 1) (θ : ℝ) :
      c+a*circleMap 0 R θ ∈ closedBall c R := by
    have ha' : ‖a‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using ha
    simp only [mem_closedBall,dist_self_add_left,norm_mul,norm_circleMap_zero,abs_of_nonneg hR]
    exact mul_le_of_le_one_left hR ha'
  have hc : ContinuousOn (fun p : ℂ × ℝ ↦ u (c+p.1*circleMap 0 R p.2))
      (closedBall (0 : ℂ) 1 ×ˢ Icc 0 (2*Real.pi)) :=
    hu.comp (by fun_prop) (fun p hp ↦ hmap p.1 hp.1 p.2)
  have hi := hc.integrableOn_compact
    (μ := (volume : Measure ℂ).prod volume) ((isCompact_closedBall (0 : ℂ) 1).prod isCompact_Icc)
  have hij := hi.mono_set (prod_mono (Subset.refl (closedBall (0 : ℂ) 1)) Ioc_subset_Icc_self)
  unfold IntegrableOn at hij
  rw [← Measure.prod_restrict] at hij
  have hswap := integral_integral_swap (f := fun a : ℂ ↦ fun θ : ℝ ↦ u (c+a*circleMap 0 R θ)) hij
  have hr (θ : ℝ) : (∫ a in closedBall (0 : ℂ) 1, u (c+a*circleMap 0 R θ)) =
      radialIntegral u c (R : ℂ) := by
    apply radialIntegral_eq_of_norm_eq
    simp [norm_circleMap_zero]
  calc
    radialIntegral u c (R : ℂ) =
        (2*Real.pi)⁻¹ * ∫ θ in Ioc 0 (2*Real.pi), radialIntegral u c (R : ℂ) := by
      simp only [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc]
      rw [sub_zero, ENNReal.toReal_ofReal Real.two_pi_pos.le]
      field_simp [Real.pi_ne_zero]
    _ = (2*Real.pi)⁻¹ * ∫ θ in Ioc 0 (2*Real.pi),
        ∫ a in closedBall (0 : ℂ) 1, u (c+a*circleMap 0 R θ) := by simp only [hr]
    _ = (2*Real.pi)⁻¹ * ∫ a in closedBall (0 : ℂ) 1,
        ∫ θ in Ioc 0 (2*Real.pi), u (c+a*circleMap 0 R θ) := by rw [hswap]
    _ = ∫ a in closedBall (0 : ℂ) 1,
        circleAverage (fun z ↦ u (c+a*z)) 0 R := by
      simp only [circleAverage,intervalIntegral.integral_of_le Real.two_pi_pos.le,
        smul_eq_mul,integral_const_mul]
    _ = ∫ _a in closedBall (0 : ℂ) 1, u c := by
      apply setIntegral_congr_fun measurableSet_closedBall
      exact hm
    _ = (volume (closedBall (0 : ℂ) 1)).toReal * u c := by
      simp only [setIntegral_const,measureReal_def,smul_eq_mul]
lemma log_norm_subharmonic {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hn : ∀ z ∈ D, f z ≠ 0) :
    DiskSubharmonicOn D (fun z ↦ Real.log ‖f z‖) := by
  have hcont : ContinuousOn (fun z ↦ Real.log ‖f z‖) D :=
    hf.continuousOn.norm.log (fun z hz ↦ norm_ne_zero_iff.mpr (hn z hz))
  refine ⟨hcont.upperSemicontinuousOn,?_⟩
  intro c hc R hR hb
  refine ⟨((hcont.mono hb).integrableOn_compact (isCompact_closedBall c R)).mono_set
    ball_subset_closedBall,?_⟩
  have hm : ∀ a ∈ closedBall (0 : ℂ) 1,
      circleAverage (fun z ↦ Real.log ‖f (c+a*z)‖) 0 R = Real.log ‖f c‖ := by
    intro a ha
    have ha' : ‖a‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using ha
    have hg : ∀ z ∈ closedBall (0 : ℂ) |R|, c+a*z ∈ D := by
      intro z hz
      apply hb
      have hz' : ‖z‖ ≤ R := by simpa [abs_of_pos hR] using hz
      simp only [mem_closedBall,dist_self_add_left,norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg z) ha').trans hz'
    have hh : InnerProductSpace.HarmonicOnNhd (fun z ↦ Real.log ‖f (c+a*z)‖)
        (closedBall (0 : ℂ) |R|) := by
      intro z hz
      apply AnalyticAt.harmonicAt_log_norm
      · exact (hf.analyticAt (hD.mem_nhds (hg z hz))).comp (f := fun w : ℂ ↦ c+a*w)
          (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ c+a*w) z)
      · exact hn _ (hg z hz)
    simpa only [mul_zero,add_zero] using hh.circleAverage_eq
  have he := radialIntegral_of_circle_means hR.le (hcont.mono hb) hm
  rw [radialIntegral_pos_radius _ _ hR] at he
  have hv := radialIntegral_pos_radius (fun _ ↦ (1 : ℝ)) c hR
  simp only [radialIntegral,setIntegral_const,measureReal_def,smul_eq_mul,mul_one] at hv
  have hball := complex_closedBall_ae_ball c R
  rw [measure_congr hball] at hv
  rw [← setIntegral_congr_set hball]
  apply le_of_eq
  rw [hv] at he
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 2 hR.ne'))
  simpa only [mul_assoc] using he.symm

theorem log_norm_psh_oai {E : Type u5} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (_hU : IsOpen U) {f : E → ℂ} (hf : DifferentiableOn ℂ f U)
    (hn : ∀ x ∈ U, f x ≠ 0) : DiskPshOn U (fun x ↦ Real.log ‖f x‖) := by
  refine ⟨(hf.continuousOn.norm.log (fun x hx ↦ norm_ne_zero_iff.mpr (hn x hx))).upperSemicontinuousOn,?_⟩
  intro D hD γ hγ hm
  exact log_norm_subharmonic hD (hf.comp hγ hm) (fun z hz ↦ hn _ (hm hz))

end
end QuadricCounterexample

end OAI
end

theorem solution.{u5} : type_of% @OAI.QuadricCounterexample.log_norm_psh_oai.{u5} := @OAI.QuadricCounterexample.log_norm_psh_oai.{u5}
