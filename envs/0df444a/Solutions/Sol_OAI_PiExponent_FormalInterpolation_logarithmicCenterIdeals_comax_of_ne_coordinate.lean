-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_comax_of_ne_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:30:47.792369+00:00
-- url     : https://prove2.me/submissions/6c660cab-2154-4cd3-90f5-c206ede4e606

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (c d : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (h : ∃ i, c i ≠ d i) :
    IsCoprime (logarithmicCenterIdeal c T e)
      (logarithmicCenterIdeal d T e) := by
  obtain ⟨i0, hne⟩ := h
  set L : MvPolynomial (Fin (m + 1)) ℂ :=
    Polynomial.aeval (MvPolynomial.X 0 - 1 : MvPolynomial (Fin (m + 1)) ℂ)
      (InterpolationMatrix.truncatedLog (T i0)) with hL
  have hj : logarithmicCoordinate c T i0.succ =
      MvPolynomial.X i0.succ - MvPolynomial.C (c i0) - L := rfl
  have hk : logarithmicCoordinate d T i0.succ =
      MvPolynomial.X i0.succ - MvPolynomial.C (d i0) - L := rfl
  have hcop : IsCoprime (logarithmicCoordinate c T i0.succ)
      (logarithmicCoordinate d T i0.succ) := by
    rw [hj, hk]
    have hd : (d i0 - c i0) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    refine ⟨MvPolynomial.C (d i0 - c i0)⁻¹, -MvPolynomial.C (d i0 - c i0)⁻¹, ?_⟩
    have : MvPolynomial.C (d i0 - c i0)⁻¹ * MvPolynomial.C (d i0 - c i0) =
        (1 : MvPolynomial (Fin (m + 1)) ℂ) := by
      rw [← map_mul, inv_mul_cancel₀ hd, map_one]
    rw [← this, map_sub]; ring
  have hcop2 := hcop.pow (m := e i0.succ) (n := e i0.succ)
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq] at hcop2
  rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hcop2]
  apply sup_le_sup
  · rw [Ideal.span_le]; rintro _ rfl
    exact Ideal.subset_span ⟨i0.succ, rfl⟩
  · rw [Ideal.span_le]; rintro _ rfl
    exact Ideal.subset_span ⟨i0.succ, rfl⟩
