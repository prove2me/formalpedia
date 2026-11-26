-- Prove2me | solution 1 for Kyprianou.Ch04.completedMeasAECongrV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:52:49.96959+00:00
-- url     : https://prove2.me/submissions/77497d8a-841d-4596-a219-ddbebc21ef63

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The completed natural filtration is closed under ambient almost-sure modification. -/
theorem solution {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : NNReal → Ω → ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (t : NNReal) (W V : Ω → E) (hV : Measurable[F t] V) (hWV : W =ᵐ[P] V) :
    Measurable[F t] W := by
  classical
  have hbad : P {ω | W ω ≠ V ω} = 0 := by
    exact ae_iff.mp hWV
  obtain ⟨N,hsub,hm,hzero⟩ := exists_measurable_superset_of_null hbad
  have hNull (A : Set Ω) (hA : A ⊆ N) : MeasurableSet[F t] A := by
    rw [hF t]
    apply (le_sup_right : MeasurableSpace.generateFrom _ ≤ _)
    exact MeasurableSpace.measurableSet_generateFrom ⟨N,hm,hzero,hA⟩
  intro C hC
  let A := W ⁻¹' C
  let B := V ⁻¹' C
  have hAB : A \ B ⊆ N := by
    intro ω hω
    apply hsub
    intro he
    exact hω.2 (by simpa [A,B,← he] using hω.1)
  have hBA : B \ A ⊆ N := by
    intro ω hω
    apply hsub
    intro he
    exact hω.2 (by simpa [A,B,he] using hω.1)
  have heq : A = (B \ (B \ A)) ∪ (A \ B) := by
    ext ω
    simp only [mem_diff,mem_union]
    tauto
  change MeasurableSet[F t] A
  rw [heq]
  exact ((hV hC).diff (hNull _ hBA)).union (hNull _ hAB)
