-- Prove2me | solution 1 for Kyprianou.Ch06.twoZeroCountsIndependentOfFiniteCompatibleOutsideRectangles
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:24:03.7872+00:00
-- url     : https://prove2.me/submissions/42a0bbc1-53c1-4e57-9f30-94533c9f30f8

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_twoZeroCountsPlusFiniteCompatibleRectanglesPoissonProduct
import Theorems.Thm_Kyprianou_Ch06_twoDisjointMarkedPoissonRectangles
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D : Set E) (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (m : Nat) (starts stops : Fin m → NNReal)
    (C : Fin m → Set E) (counts : Fin m → Nat)
    (hValid : ∀ i, starts i ≤ stops i ∧
      MeasurableSet (C i) ∧ n (C i) < ⊤)
    (hBC : ∀ i, Disjoint B (C i))
    (hDC : ∀ i, Disjoint D (C i))
    (hSep : ∀ i j : Fin m, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (C i) (C j))
    (s t : NNReal) :
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0 ∧
      ∀ i : Fin m,
        N omega (stops i) (C i) -
          N omega (starts i) (C i) = counts i} =
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0} *
    P {omega | ∀ i : Fin m,
        N omega (stops i) (C i) -
          N omega (starts i) (C i) = counts i} := by
  have hJoint :=
    Kyprianou.Ch06.twoZeroCountsPlusFiniteCompatibleRectanglesPoissonProduct
      P n N hPPP B D hB hD hBD hFB hFD
      m starts stops C counts hValid hBC hDC hSep s t
  have hTwo :=
    Kyprianou.Ch06.twoDisjointMarkedPoissonRectangles
      P n N hPPP B D hB hD hBD hFB hFD s t 0 0
  have hOutside := hPPP.2.2 m starts stops C counts hValid hSep
  simpa only [← hTwo, ← hOutside] using hJoint
