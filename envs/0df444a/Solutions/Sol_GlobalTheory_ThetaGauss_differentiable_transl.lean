-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.differentiable_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:50:59.872025+00:00
-- url     : https://prove2.me/submissions/2ebd1b9f-8262-4e4f-a512-197ddcf10042

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_analytic_of_diff
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.ThetaGauss.transl_apply

set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution {K : Type} [TopologicalSpace K] [CompactSpace K]
    {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (γ : C(K, Fin g → ℂ)) :
    Differentiable ℂ (transl hf γ) := by
  intro z
  have hc : Continuous (fderiv ℂ f) :=
    continuousOn_univ.1 (analytic_of_diff hf).fderiv.continuousOn
  let L : (Fin g → ℂ) →ₗ[ℂ] C(K, ℂ) :=
    { toFun := fun h => ⟨fun k => fderiv ℂ f (z + γ k) h, by fun_prop⟩
      map_add' := fun a b => by ext k; simp
      map_smul' := fun a b => by ext k; simp }
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall z (‖γ‖ + 1)).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  obtain ⟨M₂, hM₂⟩ := (isCompact_closedBall z (‖γ‖ + 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have hmem : ∀ k, ∀ h ∈ ball (0 : Fin g → ℂ) 1, z + γ k + h ∈ closedBall z (‖γ‖ + 1) := by
    intro k h hh
    rw [mem_ball_zero_iff] at hh
    rw [mem_closedBall, dist_eq_norm, show z + γ k + h - z = γ k + h by abel]
    linarith [norm_add_le (γ k) h, γ.norm_coe_le_norm k]
  have hM : 0 ≤ M₁ + M₁ + M₂ := by
    have := (norm_nonneg _).trans (hM₁ z (mem_closedBall_self (by positivity)))
    have := (norm_nonneg _).trans (hM₂ z (mem_closedBall_self (by positivity)))
    positivity
  refine HasFDerivAt.differentiableAt (f' := LinearMap.toContinuousLinearMap L) ?_
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h => ‖h‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id (by norm_num))
  refine Asymptotics.IsBigO.of_bound (M₁ + M₁ + M₂) ?_
  filter_upwards [ball_mem_nhds 0 one_pos] with h hh
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun k => ?_
  have key := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
    (f := fun h => f (z + γ k + h) - fderiv ℂ f (z + γ k) h) (c := 0) (z := h) (R₁ := 1)
    (R₂ := M₁ + M₁ + M₂) (n := 1) (by fun_prop) (fun y hy => ?_) ?_ hh
  · simp only [dist_eq_norm, add_zero, map_zero, sub_zero, div_one] at key
    simp only [norm_pow, norm_norm]
    refine le_trans (le_of_eq ?_) key
    congr 1
    change f (z + h + γ k) - f (z + γ k) - fderiv ℂ f (z + γ k) h = _
    rw [add_right_comm]; ring
  · simp only [mem_closedBall, dist_eq_norm, add_zero, map_zero, sub_zero]
    have h1 := hM₁ _ (hmem k y hy)
    have h2 := hM₁ _ (hmem k 0 (by simp))
    have h3 := hM₂ _ (hmem k 0 (by simp))
    rw [add_zero] at h2 h3
    have h4 : ‖fderiv ℂ f (z + γ k) y‖ ≤ M₂ := by
      refine ((fderiv ℂ f (z + γ k)).le_opNorm y).trans ?_
      rw [mem_ball_zero_iff] at hy
      nlinarith [norm_nonneg y, norm_nonneg (fderiv ℂ f (z + γ k))]
    linarith [norm_sub_le (f (z + γ k + y) - fderiv ℂ f (z + γ k) y) (f (z + γ k)),
      norm_sub_le (f (z + γ k + y)) (fderiv ℂ f (z + γ k) y)]
  · have := hasFDerivAt_iff_isLittleO_nhds_zero.1 (hf (z + γ k)).hasFDerivAt
    simp only [add_zero, map_zero, sub_zero, pow_one]
    refine (this.congr_left fun y => by ring).norm_right
end GlobalTheory.ThetaGauss
