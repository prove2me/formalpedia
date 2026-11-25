-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:10.635632+00:00
-- url     : https://prove2.me/submissions/9fe888de-7a08-4cf2-86b8-e614b09fffdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_norm_itg
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_dI_apply
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_norm_dh_le
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped ContDiff Real
noncomputable section
open GlobalTheory GlobalTheory.RealWeil
open GlobalTheory.RealWeil.Superpos
variable {V Y B : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B} {ι : Y →L[ℝ] V} {ν : Measure Y}
namespace GlobalTheory.RealWeil.Superpos
theorem _root_.solution (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Mom ν h) {g : V → B}
    (hg : ContDiff ℝ ∞ g) (v₀ : V) : ∃ bd : Y → ℝ, Integrable bd ν ∧
      ∀ y, ∀ v ∈ Metric.closedBall v₀ 1, ‖dI om ρ ι h g v y‖ ≤ bd y := by
  obtain ⟨Cg, hCg⟩ := (isCompact_closedBall v₀ 1).exists_bound_of_continuousOn hg.continuous.continuousOn
  obtain ⟨Cd, hCd⟩ :=
    (isCompact_closedBall v₀ 1).exists_bound_of_continuousOn (hg.continuous_fderiv (by simp)).continuousOn
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg v₀ (Metric.mem_closedBall_self zero_le_one))
  have hCd0 : 0 ≤ Cd := (norm_nonneg _).trans (hCd v₀ (Metric.mem_closedBall_self zero_le_one))
  have hK : 0 ≤ 2 * π * ‖om‖ * ‖ι‖ * Cg := by have := Real.pi_pos; positivity
  refine ⟨fun y => ‖h y‖ * (Cd + 2 * π * ‖om‖ * ‖ι‖ * Cg * ‖y‖), ?_, fun y v hv => ?_⟩
  · refine (((hh.2 0).const_mul Cd).add ((hh.2 1).const_mul (2 * π * ‖om‖ * ‖ι‖ * Cg))).congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, pow_zero, pow_one]
    ring
  · refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (norm_nonneg _) (add_nonneg hCd0 (mul_nonneg hK (norm_nonneg _)))) fun z => ?_
    rw [dI_apply]
    refine (norm_add_le _ _).trans ?_
    rw [norm_itg hρ, norm_itg hρ]
    have hDz : ‖fderiv ℝ g v z‖ ≤ Cd * ‖z‖ :=
      ((fderiv ℝ g v).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hCd v hv) (norm_nonneg _))
    calc ‖dh om ι h z y‖ * ‖g v‖ + ‖h y‖ * ‖fderiv ℝ g v z‖
        ≤ (2 * π * ‖om‖ * ‖ι‖ * ‖y‖ * ‖z‖ * ‖h y‖) * Cg + ‖h y‖ * (Cd * ‖z‖) :=
          add_le_add (mul_le_mul (norm_dh_le h z y) (hCg v hv) (norm_nonneg _) (by have := Real.pi_pos; positivity))
            (mul_le_mul_of_nonneg_left hDz (norm_nonneg _))
      _ = ‖h y‖ * (Cd + 2 * π * ‖om‖ * ‖ι‖ * Cg * ‖y‖) * ‖z‖ := by ring
end GlobalTheory.RealWeil.Superpos
