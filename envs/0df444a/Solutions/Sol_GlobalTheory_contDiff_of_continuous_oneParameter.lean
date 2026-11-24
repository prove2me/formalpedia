-- Prove2me | solution 1 for GlobalTheory.contDiff_of_continuous_oneParameter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:22.854486+00:00
-- url     : https://prove2.me/submissions/971984a4-4a38-4414-bbcd-b2d81931072d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContDiffOfContinuousOneParameter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory
open MeasureTheory Filter Topology
open scoped ContDiff
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (T : ℝ → A) (hT : Continuous T) (h0 : T 0 = 1)
    (hadd : ∀ s t, T (s + t) = T s * T t) : ContDiff ℝ ∞ T := by
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → A, G = fun x => ∫ s in (0:ℝ)..x, T s := ⟨_, rfl⟩
  have hG : ∀ x, HasDerivAt G (T x) x := fun x => by
    rw [hGdef]; exact (hT.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hG0 : G 0 = 0 := by rw [hGdef]; exact intervalIntegral.integral_same
  have hlim : Tendsto (fun δ : ℝ => δ⁻¹ • G δ) (𝓝[≠] 0) (𝓝 1) := by
    have h := hasDerivAt_iff_tendsto_slope.mp (hG 0)
    rw [h0] at h
    refine h.congr' (Eventually.of_forall fun δ => ?_)
    simp [slope_def_module, hG0]
  obtain ⟨δ, hδu, hδ0⟩ :=
    ((hlim.eventually (Units.isOpen.mem_nhds isUnit_one)).and self_mem_nhdsWithin).exists
  have hδ : δ ≠ 0 := hδ0
  have hu : IsUnit (G δ) := by
    have e : G δ = algebraMap ℝ A δ * (δ⁻¹ • G δ) := by
      rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hδ, one_smul]
    rw [e]
    exact ((Ne.isUnit hδ).map (algebraMap ℝ A)).mul hδu
  have key : ∀ t, T t * G δ = G (t + δ) - G t := by
    intro t
    have h1 := (ContinuousLinearMap.mul ℝ A (T t)).intervalIntegral_comp_comm
      (hT.intervalIntegrable (μ := volume) 0 δ)
    simp only [ContinuousLinearMap.mul_apply'] at h1
    rw [hGdef]
    dsimp only
    rw [← h1, intervalIntegral.integral_interval_sub_left (hT.intervalIntegrable (μ := volume) _ _)
      (hT.intervalIntegrable (μ := volume) _ _)]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun x => T x) t, add_zero]
  have hform : T = fun t => (G (t + δ) - G t) * ↑hu.unit⁻¹ := by
    funext t
    rw [← key, mul_assoc, IsUnit.mul_val_inv, mul_one]
  rw [contDiff_infty]
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hT
  | succ n ih =>
    have hGn : ContDiff ℝ (n + 1 : ℕ) G := by
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun x => (hG x).differentiableAt, by simp, ?_⟩
      rwa [show deriv G = T from funext fun x => (hG x).deriv]
    rw [hform]
    exact ((hGn.comp (contDiff_id.add contDiff_const)).sub hGn).mul contDiff_const
end _root_.GlobalTheory
end GlobalTheory
