-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.stoppedStrictPathEventNullMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:33:57.763346+00:00
-- url     : https://prove2.me/submissions/a463ee49-9b8d-4806-bf0e-6748498fdf8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_stoppedRationalMarginEventNullMeasurable
import Theorems.Thm_Kyprianou_Ch08_StageB_stoppedStrictPathIffRationalMarginAE
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0)
    (h : ℝ)
    (hT : AEMeasurable T P)
    (hf : ∀ r : ℚ, 0 ≤ r →
      AEMeasurable (f (r : ℝ).toNNReal) P)
    (hpath : ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0,
        ContinuousWithinAt (fun s => f s ω) (Set.Ici t) t) ∧
      (∀ z : ℝ≥0,
        UpperSemicontinuousOn (fun s => f s ω) (Set.Icc 0 z))) :
    NullMeasurableSet
      {ω : Ω | ∀ t : ℝ≥0,
        (t : WithTop ℝ≥0) < T ω → f t ω < h} P := by
  have hc :=
    Kyprianou.Ch08.StageB.stoppedRationalMarginEventNullMeasurable
      P f T h hT hf
  have heq :=
    Kyprianou.Ch08.StageB.stoppedStrictPathIffRationalMarginAE
      P f T h hpath
  refine hc.congr ?_
  filter_upwards [heq] with ω hω
  exact propext hω.symm
