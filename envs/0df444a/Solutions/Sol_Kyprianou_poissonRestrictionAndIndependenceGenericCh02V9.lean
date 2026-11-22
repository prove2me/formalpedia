-- Prove2me | solution 1 for Kyprianou.poissonRestrictionAndIndependenceGenericCh02V9
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:57:29.359123+00:00
-- url     : https://prove2.me/submissions/d01d537f-c465-4fa0-b612-93ec998986c9

import Mathlib
import Definitions.Def_Kyprianou_Ch02_AbstractPoissonRandomMeasureV8
import Theorems.Thm_Kyprianou_Ch02_abstractPRMRestrictionV8
import Theorems.Thm_Kyprianou_Ch02_abstractPRMDisjointSigmaIndepV8

open MeasureTheory ProbabilityTheory Kyprianou Kyprianou.Ch02
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (N : Ω → Measure E)
    (hN : Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P m N) :
    (∀ (B : Set E), MeasurableSet B →
      Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P
        (m.restrict B) (fun ω => (N ω).restrict B)) ∧
    (∀ (A B : Set E),
      MeasurableSet A → MeasurableSet B → Disjoint A B →
      ProbabilityTheory.Indep
        (⨆ C ∈ {C : Set E | C ⊆ A ∧ MeasurableSet C},
           MeasurableSpace.comap (fun ω => N ω C) inferInstance)
        (⨆ D ∈ {D : Set E | D ⊆ B ∧ MeasurableSet D},
           MeasurableSpace.comap (fun ω => N ω D) inferInstance)
        P) := by
  exact ⟨Kyprianou.Ch02.abstractPRMRestrictionV8 P m N hN,
    Kyprianou.Ch02.abstractPRMDisjointSigmaIndepV8 P m N hN⟩
