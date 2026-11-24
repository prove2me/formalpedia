-- Prove2me | solution 1 for Kyprianou.Ch01.firstNegativePassageMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T16:53:35.937386+00:00
-- url     : https://prove2.me/submissions/e222e324-b6d3-46b9-b6b9-ceb58c6f44c7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_firstNegativePassage_eq_rationalInf

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    Measurable (fun ω : Ω => firstNegativePassage X ω) := by
  have hslice : ∀ t : ℝ≥0, Measurable (fun ω : Ω => X t ω) := by
    intro t
    change Measurable ((fun p : Ω × ℝ≥0 => X p.2 p.1) ∘ fun ω : Ω => (ω, t))
    exact hX.comp (measurable_id.prodMk measurable_const)
  have hite :
      ∀ q : {q : ℚ // 0 < q},
        Measurable fun ω : Ω =>
          if X (Real.toNNReal (q : ℝ)) ω < 0 then
            ((Real.toNNReal (q : ℝ) : ℝ≥0) : WithTop ℝ≥0)
          else ⊤ := by
    intro q
    let t : ℝ≥0 := Real.toNNReal (q : ℝ)
    have hset : MeasurableSet {ω : Ω | X t ω < 0} :=
      (measurableSet_lt (hslice t) measurable_const)
    refine Measurable.ite hset measurable_const measurable_const
  have heq :
      (fun ω : Ω => firstNegativePassage X ω) =
        fun ω : Ω =>
          ⨅ q : {q : ℚ // 0 < q},
            if X (Real.toNNReal (q : ℝ)) ω < 0 then
              ((Real.toNNReal (q : ℝ) : ℝ≥0) : WithTop ℝ≥0)
            else ⊤ := by
    funext ω
    exact firstNegativePassage_eq_rationalInf X hX ω
  rw [heq]
  exact Measurable.iInf hite
