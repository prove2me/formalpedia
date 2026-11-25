-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaStrip.norm_digamma_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:30.140104+00:00
-- url     : https://prove2.me/submissions/c8261219-8e34-4aa7-8339-cb89e5f494b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaBoundVerticalStrip
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaStrip_exists_Gamma_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaStrip_norm_inv_Gamma_le
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaStrip_deriv_inv_Gamma_div
import Theorems.Thm_GlobalTheory_LWide_disc
import Theorems.Thm_PI_EF_norm_Gamma_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaStrip
namespace GlobalTheory.CompanionTheory.DigammaStrip
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ z.re → z.re ≤ 2 → 1 / 2 ≤ |z.im| →
      ‖digamma z‖ ≤ C * (1 + |z.im|) := by
  obtain ⟨C0, hC0, H⟩ := GlobalTheory.LWide.disc (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨K, hK0, hK⟩ := exists_Gamma_bound
  set L : ℝ := Real.log (16 * K ^ 2) with hL
  refine ⟨4 * C0 * (1 + |L| + 4 * Real.pi), by positivity, fun z hz1 hz2 hzi => ?_⟩
  set t : ℝ := |z.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  set F : ℂ → ℂ := fun w => (Complex.Gamma w)⁻¹ with hF
  have hFd : Differentiable ℂ F := by
    have h := Complex.differentiable_one_div_Gamma
    simpa [hF, one_div] using h
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hFz : F z ≠ 0 := inv_ne_zero hGz
  have hM : ∀ w, ‖w - z‖ ≤ 1 / 4 → ‖F w‖ ≤ 16 * K * Real.exp (Real.pi * (t + 1)) := by
    intro w hw
    have hre : |w.re - z.re| ≤ 1 / 4 := by
      have := (Complex.abs_re_le_norm (w - z)).trans hw
      simpa using this
    have him : |w.im - z.im| ≤ 1 / 4 := by
      have := (Complex.abs_im_le_norm (w - z)).trans hw
      simpa using this
    have hre' := abs_le.1 hre
    have h1 : t ≤ |w.im| + 1 / 4 := by
      have := abs_sub_abs_le_abs_sub z.im w.im
      rw [abs_sub_comm z.im w.im] at this
      linarith
    have h2 : |w.im| ≤ t + 1 / 4 := by
      have := abs_sub_abs_le_abs_sub w.im z.im
      linarith
    refine (norm_inv_Gamma_le hK0 hK (by linarith [hre'.1]) (by linarith [hre'.2])
      (by linarith)).trans ?_
    gcongr
    linarith
  obtain ⟨-, -, h3⟩ := H F z (1 / 4) (16 * K * Real.exp (Real.pi * (t + 1))) (by norm_num) hFd hFz hM
  have hempty : {w : ℂ | ‖w - z‖ ≤ 1 / 2 * (1 / 4) ∧ F w = 0} = ∅ := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hw
    have hre : |w.re - z.re| ≤ 1 / 2 * (1 / 4) := by
      have := (Complex.abs_re_le_norm (w - z)).trans hw
      simpa using this
    have hre' := abs_le.1 hre
    exact inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by linarith [hre'.1]))
  have h4 := h3 z (by simp) hFz
  rw [hempty, finsum_mem_empty, sub_zero, deriv_inv_Gamma_div (by linarith), norm_neg] at h4
  have hnz : ‖Complex.Gamma z‖ ≤ K :=
    (PI.EF.norm_Gamma_le (by linarith)).trans (hK _ (by linarith) (by linarith))
  have hnz0 : 0 < ‖Complex.Gamma z‖ := norm_pos_iff.2 hGz
  have hlog : Real.log (16 * K * Real.exp (Real.pi * (t + 1)) / ‖F z‖) ≤ L + Real.pi * (t + 1) := by
    have he : 16 * K * Real.exp (Real.pi * (t + 1)) / ‖F z‖ =
        (16 * K * ‖Complex.Gamma z‖) * Real.exp (Real.pi * (t + 1)) := by
      simp only [hF, norm_inv]
      field_simp
    rw [he, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    have : Real.log (16 * K * ‖Complex.Gamma z‖) ≤ L := by
      apply Real.log_le_log (by positivity)
      nlinarith
    linarith
  have hL' : L ≤ |L| := le_abs_self L
  have hpi := Real.pi_pos
  have hfin : (1 / 4) * ‖digamma z‖ ≤ C0 * (1 + |L| + 4 * Real.pi) * (1 + t) := by
    refine h4.trans ?_
    have h5 : 1 + Real.log (16 * K * Real.exp (Real.pi * (t + 1)) / ‖F z‖) ≤
        (1 + |L| + 4 * Real.pi) * (1 + t) := by
      have h6 : 0 ≤ t * (1 + |L|) := by positivity
      nlinarith
    calc _ ≤ C0 * ((1 + |L| + 4 * Real.pi) * (1 + t)) := by gcongr
      _ = _ := by ring
  linarith
end GlobalTheory.CompanionTheory.DigammaStrip
