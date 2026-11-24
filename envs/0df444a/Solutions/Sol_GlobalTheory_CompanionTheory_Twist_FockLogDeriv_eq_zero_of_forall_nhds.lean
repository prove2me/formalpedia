-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Twist.FockLogDeriv.eq_zero_of_forall_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:42:50.155892+00:00
-- url     : https://prove2.me/submissions/8a420b91-55c5-4029-ba8b-8a9ca4262acb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_EqZeroOfForallNhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Twist GlobalTheory.CompanionTheory.Twist.FockLogDeriv
namespace GlobalTheory.CompanionTheory.Twist.FockLogDeriv
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hT : ∀ b, (∀ y, T y b = 0) → b = 0)
    (y₀ : V) (U : Set V) (hU : U ∈ 𝓝 y₀) (b : V) (hb : ∀ y ∈ U, T y b = 0) : b = 0 := by
  apply hT
  intro z
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have h0 : T y₀ b = 0 := hb y₀ (hball (Metric.mem_ball_self hε))
  have hz1 : 0 < ‖z‖ + 1 := by positivity
  set t : ℝ := ε / (2 * (‖z‖ + 1)) with ht
  have htpos : 0 < t := by positivity
  have htz : t * (‖z‖ + 1) = ε / 2 := by
    rw [ht]; field_simp
  have hmem : y₀ + t • z ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le]
    nlinarith [norm_nonneg z]
  have h1 := hb _ hmem
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, h0, zero_add, smul_eq_mul] at h1
  exact (mul_eq_zero.mp h1).resolve_left htpos.ne'
end GlobalTheory.CompanionTheory.Twist.FockLogDeriv
