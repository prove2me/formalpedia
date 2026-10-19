-- Prove2me | solution 1 for MazurTransfer.quadratic_coordinate_kaehler_equiv_of_coprime_of_two_unit
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T04:58:18.772585+00:00
-- url     : https://prove2.me/submissions/74147ca6-cf49-41ae-9d48-41fa813bc17e

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: free rank-one differentials for the actual quadratic coordinate presentation from polynomial coprimality and an invertible two.
Named downstream consumer: the integral relative-dimension-one proof for both actual order-thirteen charts.
The mixed quadratic differential theorem is a previously Proved public input. -/
import Mathlib
import Theorems.Thm_MazurTransfer_mixed_quadratic_coordinate_kaehler_equiv
noncomputable section
universe u
open Polynomial

theorem solution (R : Type u) [CommRing R] (f : Polynomial R)
    (hf : IsCoprime f f.derivative) (h2 : IsUnit (2 : R)) :
    Nonempty (Ω[AdjoinRoot ((X ^ 2 - C f) : Polynomial (Polynomial R))⁄R] ≃ₗ[AdjoinRoot ((X ^ 2 - C f) : Polynomial (Polynomial R))]
      AdjoinRoot ((X ^ 2 - C f) : Polynomial (Polynomial R))) := by
  let q : Polynomial (Polynomial R) := X ^ 2 + C (0 : Polynomial R) * X - C f
  let A := AdjoinRoot q
  let ofp : Polynomial R →+* A := AdjoinRoot.of q
  let y : A := AdjoinRoot.root q
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨unitTwo, hunitTwo⟩ := h2
  let c : A := algebraMap R A ↑(unitTwo⁻¹)
  have hc : (2 : A) * c = 1 := by
    have h : (2 : R) * ↑(unitTwo⁻¹) = 1 := by
      rw [← hunitTwo]
      simp
    simpa only [c, map_mul, map_ofNat, map_one] using congrArg (algebraMap R A) h
  have hy : y ^ 2 = ofp f := by
    have h := AdjoinRoot.eval₂_root q
    simp only [q, eval₂_sub, eval₂_add, eval₂_pow, eval₂_mul, eval₂_X, eval₂_C,
      map_zero, zero_mul, add_zero] at h
    exact sub_eq_zero.mp h
  have hbez : ofp a * ofp f + ofp b * ofp f.derivative = 1 := by
    simpa only [map_add, map_mul, map_one] using congrArg ofp hab
  have hjac : ∃ aa bb : A,
      aa * (ofp (0 : Polynomial R).derivative * y - ofp f.derivative) +
        bb * (2 * y + ofp 0) = 1 := by
    refine ⟨-ofp b, ofp a * y * c, ?_⟩
    simp only [derivative_zero, map_zero, zero_mul, zero_sub, add_zero]
    calc
      _ = ofp b * ofp f.derivative + (ofp a * y ^ 2) * (2 * c) := by ring
      _ = 1 := by rw [hy, hc, mul_one, add_comm]; exact hbez
  have h := MazurTransfer.mixed_quadratic_coordinate_kaehler_equiv R 0 f hjac
  have heq : (X ^ 2 + C (0 : Polynomial R) * X - C f : Polynomial (Polynomial R)) =
      X ^ 2 - C f := by simp
  rw [heq] at h
  exact h

#print axioms solution
