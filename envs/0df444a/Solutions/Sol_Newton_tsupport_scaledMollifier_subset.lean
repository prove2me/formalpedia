-- Prove2me | solution 1 for Newton.tsupport_scaledMollifier_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:03:23.671626+00:00
-- url     : https://prove2.me/submissions/3f02be5d-1457-41fb-a5b4-b19866fa667f

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity

set_option autoImplicit false
open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise
open Newton
variable {n : ℕ}
variable {ψ : (Fin n → ℝ) → ℝ}
namespace Newton
theorem _root_.solution
    (hψ : IsApproximateIdentity ψ) {η : ℝ} (hη_pos : 0 < η) :
    tsupport (scaledMollifier ψ η)
      ⊆ Metric.closedBall (0 : Fin n → ℝ) η := by
  -- Scaling map s(x) = x / η
  set s : (Fin n → ℝ) → (Fin n → ℝ) := fun x => fun i => x i / η with hs_def
  have hs_eq_smul : s = fun x : (Fin n → ℝ) => (η⁻¹ : ℝ) • x := by
    funext x i; simp [s, div_eq_mul_inv, mul_comm]
  have hs_cont : Continuous s := by
    simpa [hs_eq_smul] using (continuous_const_smul (η⁻¹ : ℝ))
  -- support(scaled) ⊆ preimage of tsupport ψ under s, hence tsupport(scaled) ⊆ that preimage
  have h_support_subset :
      Function.support (scaledMollifier ψ η) ⊆ s ⁻¹' tsupport ψ := by
    intro x hx
    have hx_ne : scaledMollifier ψ η x ≠ 0 := hx
    have hψ_ne : ψ (s x) ≠ 0 := by
      intro hzero
      have : scaledMollifier ψ η x = 0 := by
        simp [scaledMollifier, hzero, s]
      exact hx_ne this
    have : s x ∈ Function.support ψ := by simpa [Function.support] using hψ_ne
    have : s x ∈ tsupport ψ := subset_tsupport _ this
    simpa [Set.mem_preimage] using this
  have h_tsupport_subset :
      tsupport (scaledMollifier ψ η) ⊆ s ⁻¹' tsupport ψ := by
    have h_closed : IsClosed (s ⁻¹' tsupport ψ) := (isClosed_tsupport _).preimage hs_cont
    simpa [tsupport, Function.support] using closure_minimal h_support_subset h_closed
  -- Push forward the inclusion along tsupport ψ ⊆ closedBall(0,1)
  have h_preimage_subset :
      s ⁻¹' tsupport ψ ⊆ s ⁻¹' Metric.closedBall (0 : Fin n → ℝ) 1 := by
    exact Set.preimage_mono hψ.support_subset
  -- Preimage of the unit ball under s equals the ball of radius η.
  have h_preimage_ball :
      s ⁻¹' Metric.closedBall (0 : Fin n → ℝ) 1
        ⊆ Metric.closedBall (0 : Fin n → ℝ) η := by
    intro x hx
    have hx' : ‖s x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hnorm_smul : ‖(η⁻¹ : ℝ)‖ = η⁻¹ := by
      have : 0 < (η : ℝ) := hη_pos
      simp [Real.norm_eq_abs, abs_of_pos this]
    have hx'' : (η⁻¹ : ℝ) * ‖x‖ ≤ 1 := by
      simpa [hs_eq_smul, norm_smul, hnorm_smul] using hx'
    have hx_le : ‖x‖ ≤ η := by
      have h_nonneg : 0 ≤ (η : ℝ) := le_of_lt hη_pos
      have h := mul_le_mul_of_nonneg_left hx'' h_nonneg
      -- Rewrite the left-hand side exactly to ‖x‖ using η ≠ 0.
      have hη_ne : (η : ℝ) ≠ 0 := ne_of_gt hη_pos
      have h_left_eq : η * (η⁻¹ * ‖x‖) = ‖x‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ hη_ne, one_mul]
      -- Conclude ‖x‖ ≤ η.
      simpa [h_left_eq, mul_one] using h
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx_le
  exact (h_tsupport_subset.trans h_preimage_subset).trans h_preimage_ball
end Newton
