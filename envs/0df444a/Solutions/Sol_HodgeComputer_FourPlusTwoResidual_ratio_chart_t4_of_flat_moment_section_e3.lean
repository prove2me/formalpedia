-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.ratio_chart_t4_of_flat_moment_section_e3
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T12:05:37.429662+00:00
-- url     : https://prove2.me/submissions/be23b605-d749-4da6-9e22-ee42566801e4

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual
open scoped BigOperators

theorem solution
    (h : ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P : K)
      (n : ℕ) (c : Fin n → K) (T0 T2 T4 : Fin n → K)
      (qr qs qt : K),
      n ≠ 0 ∧
        a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (∑ j : Fin n, c j * T0 j = 0) ∧
        (∑ j : Fin n, c j * T2 j = 0) ∧
        (∑ j : Fin n, c j * T4 j = 1) ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) =
          (∑ j : Fin n, c j * T0 j) +
            (∑ j : Fin n, c j * T2 j) * t ^ 2 +
              (∑ j : Fin n, c j * T4 j) * t ^ 4)) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) = t ^ 4) := by
  obtain ⟨K, fieldK, charK, Dr, Ds, Dt, a, s, t, P, n, c, T0, T2, T4, qr, qs, qt,
    _hn, ha, ht, hDra, hDsa, hDta, hDrt, hDst, hDtt, hDss, h0, h2, h4, hsrc⟩ := h
  refine ⟨K, fieldK, charK, Dr, Ds, Dt, a, s, t, P, qr, qs, qt,
    ha, ht, hDra, hDsa, hDta, hDrt, hDst, hDtt, hDss, ?_⟩
  calc
    -(P * (Dr qr + Ds qs + Dt qt) -
        (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P))
        = (∑ j : Fin n, c j * T0 j) +
            (∑ j : Fin n, c j * T2 j) * t ^ 2 +
              (∑ j : Fin n, c j * T4 j) * t ^ 4 := hsrc
    _ = (0 : K) + (0 : K) * t ^ 2 + (1 : K) * t ^ 4 := by
          simp [h0, h2, h4]
    _ = t ^ 4 := by ring
