-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.synchronize_coordinate_power_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:31:20.034965+00:00
-- url     : https://prove2.me/submissions/f97078a7-f0b6-4b13-b22f-ba3e924174f5

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_commonize_coordinate_power_witnesses_v3
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_scale_coordinate_power_witnesses_v3
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_strict_nat_cutoff_after_scaling_v3
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (eps : Real) (heps : 0 < eps)
    (hcoord : ∀ i : Fin d, ∃ s n : Nat, 0 < s ∧ 0 < n ∧
      MvPolynomial.X i ^ n ∈ I ^ s ∧
      (n : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps / 2)) :
    ∃ s : Nat, 0 < s ∧ ∃ B : Nat,
      (B : Real) < (s : Real) * ((rho : Real) + eps) ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ I ^ s ∧
        (n : Real) * (w i : Real) ≤ (B : Real) := by
  obtain ⟨s, hs, n, hn, hmem, hstrict⟩ :=
    OAI.PiExponent.FormalInterpolation.commonize_coordinate_power_witnesses_v3
      I w hw rho hrho eps heps hcoord
  let x : Fin d → Real := fun i => (n i : Real) * (w i : Real)
  obtain ⟨k, hk, B, hB, hbound⟩ :=
    OAI.PiExponent.FormalInterpolation.strict_nat_cutoff_after_scaling_v3
      s hs (rho : Real) (by exact_mod_cast hrho) eps heps x
      (by intro i; exact hstrict i)
  refine ⟨s * k, Nat.mul_pos hs hk, B, ?_, ?_⟩
  · simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hB
  · intro i
    obtain ⟨hnk, hmemk⟩ :=
      OAI.PiExponent.FormalInterpolation.scale_coordinate_power_witnesses_v3
        I s n hn hmem k hk i
    refine ⟨n i * k, hnk, hmemk, ?_⟩
    calc
      ((n i * k : Nat) : Real) * (w i : Real) = x i * (k : Real) := by
        simp [x, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (B : Real) := hbound i