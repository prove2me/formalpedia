-- Prove2me | solution 1 for Kyprianou.Ch04.markedPredictableLeAmbientProduct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:47:14.008488+00:00
-- url     : https://prove2.me/submissions/07de4047-148d-4f59-8e37-b340f880fe9f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_generate_sigma
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false
universe u v

/-- The marked predictable sigma-algebra is contained in the ambient product. -/
theorem solution
    {Ω : Type u} {E : Type v} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (F : Filtration NNReal mΩ) :
    F.predictable.prod mE ≤
      ((inferInstance : MeasurableSpace NNReal).prod mΩ).prod mE := by
  rw [AvramDividend.Classical.avram_wave4_p1_predictable_marked_rectangle_generate_sigma F]
  apply MeasurableSpace.generateFrom_le
  rintro S ⟨U, hU, C, hC, rfl⟩
  rcases hU with ⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩
  · exact (measurableSet_singleton _).prod (F.le' _ _ hA) |>.prod hC
  · exact measurableSet_Ioi.prod (F.le' _ _ hA) |>.prod hC
