-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coordinateJetGenerators_comaximal_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:06:13.438321+00:00
-- url     : https://prove2.me/submissions/b9d6219f-1baa-4a31-afe3-518b5202d790

import Mathlib
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
theorem solution
    {m : ℕ} (c d : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (i : Fin m)
    (h : c i ≠ d i) :
    Ideal.span ({jetCoordinate c T i.succ ^ e i.succ} : Set (MvPolynomial (Fin (m + 1)) ℂ)) ⊔
      Ideal.span ({jetCoordinate d T i.succ ^ e i.succ} : Set (MvPolynomial (Fin (m + 1)) ℂ)) = ⊤ := by
  have hne : d i - c i ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hdiff : jetCoordinate c T i.succ - jetCoordinate d T i.succ = MvPolynomial.C (d i - c i) := by
    simp only [jetCoordinate, Fin.cases_succ, map_sub]
    ring
  have hcop : IsCoprime (jetCoordinate c T i.succ) (jetCoordinate d T i.succ) := by
    refine ⟨MvPolynomial.C (d i - c i)⁻¹, -MvPolynomial.C (d i - c i)⁻¹, ?_⟩
    have : MvPolynomial.C (d i - c i)⁻¹ * jetCoordinate c T i.succ +
        -MvPolynomial.C (d i - c i)⁻¹ * jetCoordinate d T i.succ =
        MvPolynomial.C (d i - c i)⁻¹ * (jetCoordinate c T i.succ - jetCoordinate d T i.succ) := by ring
    rw [this, hdiff, ← map_mul, inv_mul_cancel₀ hne, map_one]
  have hpow := hcop.pow (m := e i.succ) (n := e i.succ)
  rw [← Ideal.isCoprime_span_singleton_iff] at hpow
  exact Ideal.isCoprime_iff_sup_eq.mp hpow
