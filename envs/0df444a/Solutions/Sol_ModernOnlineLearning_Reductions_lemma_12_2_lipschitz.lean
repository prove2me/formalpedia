-- Prove2me | solution 1 for ModernOnlineLearning.Reductions.lemma_12_2_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:33:34.828572+00:00
-- url     : https://prove2.me/submissions/61b441d2-f835-43a4-9742-7a00ab176db3

import Definitions.Def_ModernOnlineLearning_Reductions_Setting

set_option autoImplicit false
open ModernOnlineLearning.Reductions

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V) :
    LipschitzWith 1 (distance V) := by
  exact Metric.lipschitz_infDist_pt V

