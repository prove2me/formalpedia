-- Prove2me | solution 1 for HuberSNSDP.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:27:31.841499+00:00
-- url     : https://prove2.me/submissions/3d3aad63-a58f-4820-929b-cb88028e2620

import Mathlib
import Definitions.Def_HuberSNSDP_Algorithm

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

open HuberSNSDP in
theorem solution {n m : ℕ} (D : SDPData n m) (hD : D.Standing) (θ : Params) (w Δ : ISpace n m)
    (hε : 0 < epsOf w) (hN : w ∈ NSet D θ)
    (hΔ : epsOf Δ = -epsOf w + zeta D θ w * θ.epsHat) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (harm : psi D θ (w + α • Δ) ≤ (1 - 2 * θ.sigma * (1 - θ.delta) * α) * psi D θ w) :
    w + α • Δ ∈ NSet D θ := by
  have hNw : zeta D θ w * θ.epsHat ≤ epsOf w := hN
  have hδ : θ.delta < 1 := θ.delta_lt_one
  have hσ := θ.sigma_pos
  have hcoef : 1 - 2 * θ.sigma * (1 - θ.delta) * α ≤ 1 := by
    have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * θ.sigma)
      (by linarith : (0 : ℝ) ≤ 1 - θ.delta)) hα0
    linarith
  have hpsi0 : 0 ≤ psi D θ w := by unfold psi; positivity
  have hpsi : psi D θ (w + α • Δ) ≤ psi D θ w :=
    le_trans harm (mul_le_of_le_one_left hpsi0 hcoef)
  have hnorm : ‖D.Ehat θ.kp θ.kc (w + α • Δ)‖ ≤ ‖D.Ehat θ.kp θ.kc w‖ := by
    unfold psi at hpsi
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hpsi
  have hzeta : zeta D θ (w + α • Δ) ≤ zeta D θ w := by
    unfold zeta
    exact mul_le_mul_of_nonneg_left
      (min_le_min_left 1 (Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith [θ.tau_pos])))
      θ.r_pos.le
  have hE : epsOf (w + α • Δ) = epsOf w + α * epsOf Δ := by
    simp [epsOf]
  show zeta D θ (w + α • Δ) * θ.epsHat ≤ epsOf (w + α • Δ)
  rw [hE, hΔ]
  have h1 := mul_le_mul_of_nonneg_right hzeta θ.epsHat_pos.le
  have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - α) (by linarith : 0 ≤ epsOf w - zeta D θ w * θ.epsHat)
  nlinarith
