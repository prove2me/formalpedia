-- Prove2me | solution 1 for Kyprianou.Ch06.fourOverlapSpacetimeRectanglesSeparated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:38:12.111316+00:00
-- url     : https://prove2.me/submissions/d4e16b64-6eec-468f-9316-171d66a42c89

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {E : Type} [MeasurableSpace E]
    (B C : Set E) (s t : NNReal) (hst : s ≤ t) :
    let starts : Fin 4 → NNReal := fun i => if i = 3 then s else 0
    let stops : Fin 4 → NNReal := fun i => if i = 3 then t else s
    let marks : Fin 4 → Set E := fun i =>
      if i = 0 then B \ C else if i = 1 then B ∩ C
        else if i = 2 then C \ B else C
    ∀ i j : Fin 4, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (marks i) (marks j) := by
  dsimp only
  have hUV : Disjoint (B \ C) (B ∩ C) := by
    apply Set.disjoint_left.mpr
    intro v hv hvi
    exact hv.2 hvi.2
  have hUZ : Disjoint (B \ C) (C \ B) := by
    apply Set.disjoint_left.mpr
    intro v hv hvi
    exact hv.2 hvi.1
  have hVZ : Disjoint (B ∩ C) (C \ B) := by
    apply Set.disjoint_left.mpr
    intro v hv hvi
    exact hvi.2 hv.1
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [hUV, hUZ, hVZ, hUV.symm, hUZ.symm, hVZ.symm]
