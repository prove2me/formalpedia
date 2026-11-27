-- Prove2me | solution 1 for GlobalTheory.PointSup.pointSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:48.633227+00:00
-- url     : https://prove2.me/submissions/ca03aa20-f90c-490e-b0de-8e2d009baf0c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralLeDensity
import Theorems.Thm_GlobalTheory_PointSup_point_le
import Theorems.Thm_GlobalTheory_PointSup_mean_le
import Theorems.Thm_GlobalTheory_PointSup_lintegral_le_density
import Theorems.Thm_GlobalTheory_PointSup_root_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_cpt_entry_cd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_cpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_orth_mem_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoE_phiF_B
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoE_phiF_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoE_phiF_meas
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.PointSup
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PointSup
theorem _root_.solution : (MeasInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∃ ρ c C : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ c ≤ densF X x z ∧ densF X x z ≤ C ∧ c ≤ X.nfac la (cpt X x z) ∧ X.nfac la (cpt X x z) ≤ C) → (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x, IsOrth X x → ENNReal.ofReal ‖P x‖ ≤ ENNReal.ofReal (C * Real.sqrt (κ x)) * ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom), (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)) := by
  intro hMI hU _ r X x0 hx0 la W bb κ hκ hW hWL F P hIn hP hPF ρ hρ _
  obtain ⟨hκm, hκpos, hκB, hκka, -, ρ1, C1, hρ1, hκloc⟩ := hκ
  obtain ⟨ρ0, c0, C0, hρ0, hc0, hU0⟩ := hU r X la
  obtain ⟨cw, hcw, hWl⟩ := hWL

  obtain ⟨φ, hφ⟩ : ∃ φ : Frame X.Ψ r → ℝ≥0∞,
      φ = fun y => OntoE.phiF X P W y * ENNReal.ofReal (κ y)⁻¹ := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφ]
    exact (OntoE.phiF_meas X hP.1.continuousOn hW.1).mul (ENNReal.measurable_ofReal.comp hκm.inv)
  have hφB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y := by
    intro y hy b hb
    rw [hφ]
    simp only
    rw [OntoE.phiF_B X hP.2 hW y hy b hb, hκB y hy b hb]
  have hφdom : ∀ y ∈ X.dom, φ y = ENNReal.ofReal (‖P y‖ ^ 2) * W y * ENNReal.ofReal (κ y)⁻¹ := by
    intro y hy
    rw [hφ]
    simp only
    rw [OntoE.phiF_dom X P W hy]
  have hφout : ∀ y, y ∉ X.dom → φ y = 0 := by
    intro y hy
    rw [hφ]
    simp [OntoE.phiF, Set.piecewise, hy]

  have hI : ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hIn
    by_cases hz : cpt X x0 z ∈ X.dom
    · rw [hφdom _ hz, hPF z hz, hκka z hz, div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _)]
      exact le_of_eq (by ring)
    · rw [hφout _ hz]
      exact zero_le
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = min ρ (min ρ0 ρ1) := ⟨_, rfl⟩
  have hRpos : 0 < R := by rw [hR]; exact lt_min hρ (lt_min hρ0 hρ1)
  have hball : ∀ z ∈ Metric.ball (0 : V (nd X)) R, ‖z‖ < ρ ∧ ‖z‖ < ρ0 ∧ ‖z‖ < ρ1 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [hR] at hz
    exact ⟨hz.trans_le (min_le_left _ _), hz.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      hz.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℝ≥0∞, J = (ENNReal.ofReal c0)⁻¹ * ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 :=
    ⟨_, rfl⟩
  have hJfin : J < ⊤ := by
    rw [hJ]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hc0)) hI
  have hv : volume (Metric.ball (0 : V (nd X)) R) ≠ 0 := (Metric.measure_ball_pos volume _ hRpos).ne'
  have hvt : volume (Metric.ball (0 : V (nd X)) R) ≠ ⊤ := measure_ball_lt_top.ne
  have hK0 : 0 ≤ max C1 0 / c0 ^ 2 := div_nonneg (le_max_right _ _) (sq_nonneg _)
  refine ⟨Real.sqrt ((J / volume (Metric.ball (0 : V (nd X)) R)).toReal * (max C1 0 / c0 ^ 2)),
    fun x hx => ?_⟩
  have hxd : x ∈ X.dom := IW.orth_mem_dom X x hx
  have hκx : 0 < κ x := (hκpos x hxd).1
  have hcd : Differentiable ℂ (fun z : V (nd X) => cpt X x z) := by
    rw [differentiable_pi]; intro τ
    rw [differentiable_pi]; intro a
    rw [differentiable_pi]; intro b
    exact (IW.cpt_entry_cd X x τ a b).differentiable (by simp)
  have hmaps : ∀ z ∈ Metric.ball (0 : V (nd X)) R, cpt X x z ∈ X.dom :=
    fun z hz => (hU0 x hx z (hball z hz).2.1).1
  have hu : DifferentiableOn ℂ (fun z => P (cpt X x z)) (Metric.ball (0 : V (nd X)) R) :=
    hP.1.comp hcd.differentiableOn hmaps
  have hg : Measurable fun z => φ (cpt X x z) := hφm.comp hcd.continuous.measurable

  have hgJ : ∫⁻ z in Metric.ball (0 : V (nd X)) R, φ (cpt X x z) ≤ J := by
    calc ∫⁻ z in Metric.ball (0 : V (nd X)) R, φ (cpt X x z)
        ≤ (ENNReal.ofReal c0)⁻¹ * ∫⁻ z, φ (cpt X x z) ∂muF X x :=
          lintegral_le_density (O := OmF X x) (d := densF X x) measurableSet_ball hmaps hc0
            (fun z hz => (hU0 x hx z (hball z hz).2.1).2.1) _
      _ = J := by rw [hJ, hMI r X x0 x hx0 hx φ hφm hφB]
  have key : ∀ S : ℝ≥0∞, (∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom →
      (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ) ≤ S) →
      ENNReal.ofReal ‖P x‖ ≤
        ENNReal.ofReal (Real.sqrt ((J / volume (Metric.ball (0 : V (nd X)) R)).toReal *
          (max C1 0 / c0 ^ 2)) * Real.sqrt (κ x)) * S := by
    intro S hSle
    have hpt : ∀ z ∈ Metric.ball (0 : V (nd X)) R, φ (cpt X x z) < ⊤ →
        ENNReal.ofReal (‖P (cpt X x z)‖ ^ 2) ≤
          φ (cpt X x z) * (ENNReal.ofReal (max C1 0 / c0 ^ 2 * κ x) * S ^ 2) := by
      intro z hz hfin
      obtain ⟨hzρ, hzρ0, hzρ1⟩ := hball z hz
      obtain ⟨hyd, -, -, hn1, -⟩ := hU0 x hx z hzρ0
      have hky : 0 < κ (cpt X x z) := (hκpos _ hyd).1
      have hkK : κ (cpt X x z) ≤ max C1 0 * κ x :=
        (hκloc x hx z hzρ1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hκx.le)
      have hce : c0 ^ 2 ≤ Real.exp (-phla X la (cpt X x z)) := by
        have hn : 0 < X.nfac la (cpt X x z) := hc0.trans_le hn1
        have h2 : Real.exp (-phla X la (cpt X x z)) = X.nfac la (cpt X x z) ^ 2 := by
          show Real.exp (-(-2 * Real.log (X.nfac la (cpt X x z)))) = _
          rw [neg_mul, neg_neg, two_mul, Real.exp_add, Real.exp_log hn]; ring
        rw [h2]; nlinarith
      have hw : W (cpt X x z) ≠ 0 :=
        (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (mul_pos hcw (Real.exp_pos _))) (hWl _ hyd)).ne'
      rw [hφdom _ hyd] at hfin ⊢
      have h := point_le hky hkK (pow_pos hc0 2) hce hw (hSle z hzρ hyd) hfin
      rwa [show max C1 0 * κ x / c0 ^ 2 = max C1 0 / c0 ^ 2 * κ x by ring] at h
    have hmean := mean_le hu hg hJfin hgJ hpt
    simp only [IW.cpt_zero] at hmean
    exact root_le hJfin hv hvt hK0 hκx.le hmean
  exact key _ fun z hz hd => le_iSup_of_le z (le_iSup_of_le hz (le_iSup_of_le hd le_rfl))
end GlobalTheory.PointSup
