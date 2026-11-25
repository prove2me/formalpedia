-- Prove2me | solution 1 for Kyprianou.Ch04.cadlagEndpointSupMeasurablePiProxy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:42:52.901876+00:00
-- url     : https://prove2.me/submissions/2b436e7f-3bc5-4d88-bd99-8479798e2aeb

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_exists_measurable_fullpath_drawdown_proxy
import Theorems.Thm_Kyprianou_Ch02_measurableUniversalRightTimeEvaluationV1
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) :
    ∃ G : NNReal × (NNReal → ℝ) → ℝ × ℝ,
      Measurable G ∧ ∀ (t : NNReal) (ω : Ω),
        G (t, fun u : NNReal => L.X u ω) =
          (L.X t ω - runningSup L t ω, runningSup L t ω) := by
  obtain ⟨D, hD, hDe, _⟩ :=
    avram_ws01e_bi_new_exists_measurable_fullpath_drawdown_proxy L
  obtain ⟨E, hE, hEe⟩ := Kyprianou.Ch02.measurableUniversalRightTimeEvaluationV1
  let V : NNReal × (NNReal → ℝ) → ℝ := fun z => E (z.2, z.1)
  have hV : Measurable V := hE.comp (measurable_snd.prodMk measurable_fst)
  refine ⟨fun z => (-D z.1 z.2, V z + D z.1 z.2), hD.neg.prodMk (hV.add hD), ?_⟩
  intro t ω
  have h := hEe (fun u => L.X u ω) (L.rightCont ω) t
  change (-D t (fun u => L.X u ω), E ((fun u => L.X u ω), t) +
    D t (fun u => L.X u ω)) = _
  rw [hDe ω t, h]
  congr 1 <;> ring
