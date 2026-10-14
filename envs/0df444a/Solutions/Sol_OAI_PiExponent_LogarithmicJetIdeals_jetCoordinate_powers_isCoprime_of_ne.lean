-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.jetCoordinate_powers_isCoprime_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T07:31:57.455546+00:00
-- url     : https://prove2.me/submissions/62a15819-5a1d-4bfc-8f9d-b987185cec28

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (c d : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (i : Fin m) (hcd : c i ≠ d i) :
    IsCoprime
      (Ideal.span ({jetCoordinate c T i.succ ^ e i.succ} : Set (MvPolynomial (Fin (m + 1)) ℂ)))
      (Ideal.span ({jetCoordinate d T i.succ ^ e i.succ} : Set (MvPolynomial (Fin (m + 1)) ℂ))) := by
  let x := jetCoordinate c T i.succ
  let y := jetCoordinate d T i.succ
  have hxy : IsCoprime x y := by
    have hdiff : x - y = MvPolynomial.C (d i - c i) := by
      simp [x, y, jetCoordinate]
    let R := MvPolynomial (Fin (m + 1)) ℂ
    have hscalar :
        (MvPolynomial.C ((d i - c i)⁻¹) : R) * MvPolynomial.C (d i - c i) = 1 := by
      rw [← map_mul]
      simp [sub_ne_zero.mpr (Ne.symm hcd)]
    refine ⟨(MvPolynomial.C ((d i - c i)⁻¹) : R),
      -(MvPolynomial.C ((d i - c i)⁻¹) : R), ?_⟩
    calc
      MvPolynomial.C ((d i - c i)⁻¹) * x + -MvPolynomial.C ((d i - c i)⁻¹) * y =
          MvPolynomial.C ((d i - c i)⁻¹) * (x - y) := by ring
      _ = MvPolynomial.C ((d i - c i)⁻¹) * MvPolynomial.C (d i - c i) := by rw [hdiff]
      _ = 1 := hscalar
  have hpow : IsCoprime (x ^ e i.succ) (y ^ e i.succ) := hxy.pow
  rw [Ideal.isCoprime_iff_exists]
  rcases hpow with ⟨a, b, hab⟩
  refine ⟨a * x ^ e i.succ, ?_, b * y ^ e i.succ, ?_, ?_⟩
  · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · exact hab
