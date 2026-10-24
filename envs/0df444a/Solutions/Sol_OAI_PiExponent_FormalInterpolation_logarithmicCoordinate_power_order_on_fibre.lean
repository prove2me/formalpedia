-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCoordinate_power_order_on_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:10:31.743165+00:00
-- url     : https://prove2.me/submissions/740e8b8a-5b10-4e51-8a90-66f625680a0f

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logCoord_aeval_on_fibre
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_transcendental_sub_constant_ne_zero
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_pow

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin m → Complex)
    (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (x : Fin (m + 1) → E) (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ))
    (nu : PolynomialCurvePlace E) (i : Fin m) :
    MvPolynomial.aeval x
        ((logarithmicCoordinate c (fun _ => e 0) i.succ) ^ e i.succ) ≠ 0 ∧
      (polynomialCurveOrder nu
        (MvPolynomial.aeval x
          ((logarithmicCoordinate c (fun _ => e 0) i.succ) ^ e i.succ)) : Real) =
        (e i.succ : Real) *
          (polynomialCurveOrder nu
            (x i.succ - algebraMap Complex E (c i)) : Real) := by
  have heval := OAI.PiExponent.FormalInterpolation.logCoord_aeval_on_fibre
    c e E x hfibre i
  have hne := OAI.PiExponent.FormalInterpolation.transcendental_sub_constant_ne_zero
    (hnonconst i) (c i)
  have hpow := OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_pow nu
    (x i.succ - algebraMap Complex E (c i)) (e i.succ)
  constructor
  · rw [map_pow, heval]
    exact pow_ne_zero _ hne
  · rw [map_pow, heval]
    exact hpow