-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46DefectiveClockCDFTransformV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:15:50.165242+00:00
-- url     : https://prove2.me/submissions/4435ec72-5e4d-4f3e-8750-1c7dd19c45fb

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46FiniteClockLawV1
import Theorems.Thm_Kyprianou_Ch04_exercise46FiniteLawCDFTransformV1
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Reduce the defective transform to the finite-part law. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (B : Omega → WithTop NNReal) (hB : AEMeasurable B P)
    (beta : Real) (hb : 0 ≤ beta) :
    (if beta = 0 then (P {omega | B omega ≠ ⊤}).toReal
      else beta * (∫ t in Ici (0 : Real), Real.exp (-beta * t) *
        (P {omega | B omega ≤ (Real.toNNReal t : WithTop NNReal)}).toReal ∂volume)) =
      ∫ omega, if B omega = ⊤ then (0 : Real)
        else Real.exp (-beta * (((B omega).untopD 0 : NNReal) : Real)) ∂P := by
  obtain ⟨nu, hfin, hs, hm, hc, hi⟩ :=
    Kyprianou.Ch04.exercise46FiniteClockLawV1 P B hB
  letI : IsFiniteMeasure nu := hfin
  rw [← hi beta]
  by_cases h : beta = 0
  · subst beta
    simp [hm, measureReal_def]
  · rw [if_neg h, ← Kyprianou.Ch04.exercise46FiniteLawCDFTransformV1
      nu hs beta (lt_of_le_of_ne hb (Ne.symm h))]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ici
    intro t ht
    simp only [hc t ht]
