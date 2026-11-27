-- Prove2me | solution 1 for MasulloRH.sixth_order_unit_gaussian_derivative_intervals
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:08:49.600649+00:00
-- url     : https://prove2.me/submissions/e415a82a-6e73-4ec2-935c-c0b7182542a5

import Theorems.Thm_MasulloRH_horner_interval_and_derivative
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set MasulloRH MasulloRH.CentralInterval MasulloRH.InteriorEvaluator
open MasulloRH.ThetaDerivativeCertificate MasulloRH.GaussianApproximation
private abbrev ok := MasulloRH.central_interval_arithmetic_sound
private theorem cf : Covers NineShift.unitFactor (1/Real.sqrt Real.pi) := by
  have pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hl : (56418958354/100000000000:ℝ) ≤ 1/Real.sqrt Real.pi := by
    apply (le_div_iff₀ pos).2
    have h : Real.sqrt Real.pi ≤ 1/(56418958354/100000000000:ℝ) :=
      (Real.sqrt_le_left (by norm_num)).2 (Real.pi_lt_d20.le.trans (by norm_num))
    linarith
  have hu : 1/Real.sqrt Real.pi ≤ (56418958356/100000000000:ℝ) := by
    apply (div_le_iff₀ pos).2
    have h : 1/(56418958356/100000000000:ℝ) ≤ Real.sqrt Real.pi :=
      Real.le_sqrt_of_sq_le ((by norm_num : (1/(56418958356/100000000000:ℝ))^2 ≤ 3.14159265358979323846).trans Real.pi_gt_d20.le)
    linarith
  dsimp [Covers,NineShift.unitFactor]; push_cast; exact ⟨hl,hu⟩
private theorem val_ok {z : Box} {x : ℝ} (hx : Covers z x) : Covers (NineShift.uv z) (unitValue x) :=
  ok.mul_ok cf (ok.exp_ok (ok.neg_ok (ok.sq_ok hx)))
private theorem der (x : ℝ) : HasDerivAt unitValue ((-2*x)*unitValue x) x := by
  have h : HasDerivAt (fun y : ℝ => -y^2) (-2*x) x := by
    apply ((hasDerivAt_id x).pow 2).neg.congr_deriv
    simp
  apply (h.exp.const_mul (1/Real.sqrt Real.pi)).congr_deriv
  unfold unitValue;ring
private theorem pulse_eq (x : ℝ) : pulse 0 x = (unitValue x:ℂ) := by
  unfold pulse unitValue
  push_cast
  simp

private theorem poly_step (n : ℕ) (hn : n < 6) (x : ℝ) :
    hornerSlope (pulseCoeffs n) x+(-2*x)*hornerR (pulseCoeffs n) x =
      hornerR (pulseCoeffs (n+1)) x := by
  interval_cases n <;> norm_num [pulseCoeffs,hornerSlope,hornerR] <;> ring

theorem solution :
    (∀ n < 6, ∀ x : ℝ, HasDerivAt (pJet n) (pJet (n+1) x) x) ∧
    (∀ (n : ℕ) (z : Box) (x : ℝ), Covers z x → Covers (pulseJB n z) (pJet n x)) ∧
    (∀ x : ℝ, pulse 0 x = (pJet 0 x : ℂ)) := by
  refine ⟨?_,?_,?_⟩
  · intro n hn x
    have h := ((MasulloRH.horner_interval_and_derivative (pulseCoeffs n)).1 x).mul (der x)
    apply h.congr_deriv
    dsimp only [pJet]
    rw [←poly_step n hn]
    ring
  · intro n z x hx
    exact ok.mul_ok ((MasulloRH.horner_interval_and_derivative (pulseCoeffs n)).2 z x hx) (val_ok hx)
  · intro x
    simpa [pJet,pulseCoeffs,hornerR] using pulse_eq x
