-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.exists_common_weight_degree
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:01:24.161932+00:00
-- url     : https://prove2.me/submissions/494dc1e6-b778-45bf-a60c-eafc9c5b2898

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Real.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_common_weight_degree_common_multiple
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_common_weight_degree_scaled_gap

theorem solution
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (R : Real) (hR : (rho : Real) < R)
    (eps : Real) (heps : 0 < eps)
    (C : Real) (hC : 0 ≤ C) (N : Nat)
    (hrate : (rho : Real) + eps < R) :
    ∃ s : Nat, 0 < s ∧ N ≤ s ∧
      ∃ D : Real, 0 < D ∧
        (s : Real) * ((rho : Real) + eps) + C < D ∧
        D < (s : Real) * R ∧
        ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
          (w i : Real) * (e : Real) = D := by
  obtain ⟨q, hq, hcommon⟩ :=
    OAI.PiExponent.FormalInterpolation.exists_common_weight_degree.common_multiple
      d w hw
  have hlo : 0 < (rho : Real) + eps := by
    exact add_pos_of_nonneg_of_pos (Rat.cast_nonneg.mpr hrho) heps
  obtain ⟨s, hs, hsN, D, hD, hlow, hhigh, k, hk, hDmul⟩ :=
    OAI.PiExponent.FormalInterpolation.exists_common_weight_degree.scaled_gap
      q hq ((rho : Real) + eps) hlo R hrate C hC N
  refine ⟨s, hs, hsN, D, hD, hlow, hhigh, ?_⟩
  intro i
  obtain ⟨e, he, heq⟩ := hcommon i
  refine ⟨e * k, Nat.mul_pos he hk, ?_⟩
  calc
    (w i : Real) * ((e * k : Nat) : Real) = ((w i : Real) * (e : Real)) * (k : Real) := by
      push_cast
      ring
    _ = q * (k : Real) := by rw [heq]
    _ = D := by rw [hDmul]; ring