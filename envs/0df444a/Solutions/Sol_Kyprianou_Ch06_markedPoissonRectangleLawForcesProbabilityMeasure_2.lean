-- Prove2me | solution 2 for Kyprianou.Ch06.markedPoissonRectangleLawForcesProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:23:00.215196+00:00
-- url     : https://prove2.me/submissions/8c0190f0-2dda-4329-86c0-1776fd714b05

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.markedPoissonRectangleLawForcesProbabilityMeasure
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N) :
    IsProbabilityMeasure P := by
  have h := hPPP.2.2 0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have hs : {omega : Omega | ∀ i : Fin 0,
      N omega (Fin.elim0 i) (Fin.elim0 i) - N omega (Fin.elim0 i) (Fin.elim0 i) = Fin.elim0 i}
      = Set.univ := by
    ext omega; simp
  rw [hs] at h
  exact ⟨by simpa using h⟩

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N) :
    IsProbabilityMeasure P :=
  Kyprianou.Ch06.markedPoissonRectangleLawForcesProbabilityMeasure P n N hPPP
