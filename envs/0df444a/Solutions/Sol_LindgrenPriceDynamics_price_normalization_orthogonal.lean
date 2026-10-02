-- Prove2me | solution 1 for LindgrenPriceDynamics.price_normalization_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T15:57:52.827364+00:00
-- url     : https://prove2.me/submissions/2c75a6fb-f1e5-424e-ba9d-2985f2840869

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

open LindgrenPriceDynamics in
theorem solution {l : ℕ} (p : ℝ → Fin l → ℝ)
    (hnorm : ∀ s, dot (p s) (p s) = 1) (s : ℝ) (hp : DifferentiableAt ℝ p s) :
    dot (p s) (deriv p s) = 0 := by
  have hd : HasDerivAt p (deriv p s) s := hp.hasDerivAt
  have hi : ∀ i, HasDerivAt (fun t => p t i) (deriv p s i) s := fun i =>
    (hasDerivAt_pi.mp hd) i
  have hsum : HasDerivAt (fun t => ∑ i, p t i * p t i)
      (∑ i, (deriv p s i * p s i + p s i * deriv p s i)) s :=
    HasDerivAt.fun_sum (fun i _ => (hi i).mul (hi i))
  have hconst : (fun t => ∑ i, p t i * p t i) = fun _ => (1 : ℝ) := by
    funext t; exact hnorm t
  rw [hconst] at hsum
  have h0 := hsum.unique (hasDerivAt_const s (1 : ℝ))
  unfold dot
  have : ∑ i, (deriv p s i * p s i + p s i * deriv p s i) = 2 * ∑ i, p s i * deriv p s i := by
    rw [Finset.mul_sum]; congr 1; funext i; ring
  linarith
