-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.strict_nat_cutoff_after_scaling_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:37:33.838016+00:00
-- url     : https://prove2.me/submissions/a6f0cdec-9593-4306-a5d7-7c207976eaba

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_nonnegative_majorant_below_of_finite_strict_bounds
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_nat_between_reals_with_gap

theorem solution
    {d : Nat} (s : Nat) (hs : 0 < s)
    (rho : Real) (hrho : 0 <= rho)
    (eps : Real) (heps : 0 < eps)
    (x : Fin d -> Real)
    (hx : forall i, x i < (s : Real) * (rho + eps / 2)) :
    exists k : Nat, 0 < k /\ exists B : Nat,
      (B : Real) < ((s * k : Nat) : Real) * (rho + eps) /\
      forall i, x i * (k : Real) <= (B : Real) := by
  have hsR : 0 < (s : Real) := by exact_mod_cast hs
  have hepsHalf : 0 < eps / 2 := by positivity
  have hc : 0 < (s : Real) * (rho + eps / 2) := by
    apply mul_pos hsR
    linarith
  obtain ⟨M, hM0, hMx, hMc⟩ :=
    OAI.PiExponent.FormalInterpolation.exists_nonnegative_majorant_below_of_finite_strict_bounds
      x hc hx
  let Delta : Real := (s : Real) * (rho + eps) - M
  have hDelta : 0 < Delta := by
    dsimp [Delta]
    nlinarith [mul_pos hsR hepsHalf]
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / Delta)
  have hkposR : 0 < (k : Real) := by
    have hrecip : 0 < 1 / Delta := by positivity
    exact lt_trans hrecip hk
  have hkpos : 0 < k := by exact_mod_cast hkposR
  have hwidth : 1 < (k : Real) * Delta := (div_lt_iff₀ hDelta).mp hk
  have hgap : (k : Real) * M + 1 < (k : Real) * ((s : Real) * (rho + eps)) := by
    dsimp [Delta] at hwidth
    nlinarith [hwidth]
  obtain ⟨B, hBM, hBU⟩ :=
    OAI.PiExponent.FormalInterpolation.exists_nat_between_reals_with_gap
      (a := (k : Real) * M)
      (b := (k : Real) * ((s : Real) * (rho + eps)))
      (mul_nonneg (le_of_lt hkposR) hM0)
      hgap
  refine ⟨k, hkpos, B, ?_, ?_⟩
  · calc
      (B : Real) < (k : Real) * ((s : Real) * (rho + eps)) := hBU
      _ = ((s * k : Nat) : Real) * (rho + eps) := by push_cast; ring
  · intro i
    have hscale : x i * (k : Real) <= (k : Real) * M := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hMx i)) (le_of_lt hkposR)]
    exact le_trans hscale hBM