-- Prove2me | solution 1 for GlobalTheory.norm_fderiv_le_of_small_of_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:10.399265+00:00
-- url     : https://prove2.me/submissions/2c2626f6-0ff7-4cbb-b79b-664877e34337

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : V → E} (hg : Differentiable ℝ g) {C δ t : ℝ}
    (hC : 0 ≤ C) (ht : 0 < t)
    (hL : ∀ a b, ‖fderiv ℝ g a - fderiv ℝ g b‖ ≤ C * ‖a - b‖) (hδ : ∀ w, ‖g w‖ ≤ δ) (v : V) :
    ‖fderiv ℝ g v‖ ≤ 2 * δ / t + C * t := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
  have key : ∀ h : V, ‖h‖ = t → ‖fderiv ℝ g v h‖ ≤ 2 * δ + C * t * t := by
    intro h hh
    have hψd : ∀ x, DifferentiableAt ℝ (fun y => g y - fderiv ℝ g v y) x :=
      fun x => (hg x).sub (fderiv ℝ g v).differentiableAt
    have hψf : ∀ x, fderiv ℝ (fun y => g y - fderiv ℝ g v y) x = fderiv ℝ g x - fderiv ℝ g v := by
      intro x
      exact ((hg x).hasFDerivAt.sub (fderiv ℝ g v).hasFDerivAt).fderiv
    have hb : ∀ x ∈ Metric.closedBall v t,
        ‖fderiv ℝ (fun y => g y - fderiv ℝ g v y) x‖ ≤ C * t := by
      intro x hx
      rw [hψf]
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      exact (hL x v).trans (mul_le_mul_of_nonneg_left hx hC)
    have hvh : v + h ∈ Metric.closedBall v t := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hh]
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hψd x) hb
      (convex_closedBall v t) (Metric.mem_closedBall_self ht.le) hvh
    rw [add_sub_cancel_left, hh, map_add] at hmv
    have e1 : g (v + h) - (fderiv ℝ g v v + fderiv ℝ g v h) - (g v - fderiv ℝ g v v) =
        (g (v + h) - g v) - fderiv ℝ g v h := by abel
    rw [e1] at hmv
    have e2 : fderiv ℝ g v h = (g (v + h) - g v) - ((g (v + h) - g v) - fderiv ℝ g v h) := by abel
    rw [e2]
    calc _ ≤ ‖g (v + h) - g v‖ + ‖(g (v + h) - g v) - fderiv ℝ g v h‖ := norm_sub_le _ _
      _ ≤ (δ + δ) + C * t * t :=
          add_le_add ((norm_sub_le _ _).trans (add_le_add (hδ _) (hδ _))) hmv
      _ = 2 * δ + C * t * t := by ring
  have hnn : 0 ≤ 2 * δ / t + C * t := add_nonneg (div_nonneg (by linarith) ht.le) (mul_nonneg hC ht.le)
  refine ContinuousLinearMap.opNorm_le_bound _ hnn (fun u => ?_)
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hs : 0 ≤ t / ‖u‖ := div_nonneg ht.le hu'.le
  have hk := key ((t / ‖u‖) • u) (by rw [norm_smul, Real.norm_of_nonneg hs, div_mul_cancel₀ t hu'.ne'])
  rw [ContinuousLinearMap.map_smul, norm_smul, Real.norm_of_nonneg hs] at hk
  have h3 : ‖fderiv ℝ g v u‖ * t ≤ (2 * δ + C * t * t) * ‖u‖ := by
    have e : ‖fderiv ℝ g v u‖ * t = (t / ‖u‖ * ‖fderiv ℝ g v u‖) * ‖u‖ := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hk hu'.le
  have e3 : (2 * δ / t + C * t) * ‖u‖ = (2 * δ + C * t * t) * ‖u‖ / t := by
    field_simp
  rw [e3, le_div_iff₀ ht]
  exact h3
end GlobalTheory
