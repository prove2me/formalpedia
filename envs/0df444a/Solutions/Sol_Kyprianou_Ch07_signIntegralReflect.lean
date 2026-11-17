-- Prove2me | solution 1 for Kyprianou.Ch07.signIntegralReflect
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:28:36.239247+00:00
-- url     : https://prove2.me/submissions/18281a64-6149-4e6c-83fd-7cbc8686b99c

import Mathlib
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (X : NNReal → Omega → Real) :
    Kyprianou.Ch07.nonnegativeSignIntegral P
      (fun t omega => -X t omega) =
      Kyprianou.Ch07.nonpositiveSignIntegral P X := by
  simp only [Kyprianou.Ch07.nonnegativeSignIntegral,
    Kyprianou.Ch07.nonpositiveSignIntegral]
  congr 1
  funext t
  simp only [neg_nonneg, neg_nonpos]
