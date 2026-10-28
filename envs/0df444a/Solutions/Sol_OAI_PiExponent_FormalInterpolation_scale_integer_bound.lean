-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.scale_integer_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T15:05:05.141402+00:00
-- url     : https://prove2.me/submissions/fb261483-2ec2-4416-9452-57b07339df16

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

theorem solution
    {s : Nat} (hs : 0 < s) {D R : Real} (hD : 0 < D)
    (hDR : D < (s : Real) * R) :
    ∃ k : Nat, 0 < k ∧ (k : Real) * D + 1 < ((k * s : Nat) : Real) * R := by
  let δ : Real := (s : Real) * R - D
  have hδ : 0 < δ := sub_pos.mpr hDR
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / δ)
  have hkpos : 0 < (k : Real) := by
    exact lt_trans (div_pos one_pos hδ) hk
  have hmul := mul_lt_mul_of_pos_right hk hδ
  have hrec : (1 / δ) * δ = 1 := by
    field_simp [ne_of_gt hδ]
  have hprod : 1 < (k : Real) * δ := by
    nlinarith [hmul]
  refine ⟨k, by exact_mod_cast hkpos, ?_⟩
  push_cast
  dsimp [δ] at hprod
  nlinarith [hprod]