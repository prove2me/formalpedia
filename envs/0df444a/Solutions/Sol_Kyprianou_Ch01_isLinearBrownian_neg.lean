-- Prove2me | solution 1 for Kyprianou.Ch01.isLinearBrownian_neg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:56:09.324481+00:00
-- url     : https://prove2.me/submissions/67e0ee83-ebb9-4e61-8be3-a553eb4fedcc

import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_levyProcess_neg_of_continuous
import Theorems.Thm_Kyprianou_Ch01_brownianCharFun_reflected
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Combine reflected Lévy structure and the reflected Gaussian exponent. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma : ℝ)
    (hX : Kyprianou.Ch01.IsLinearBrownian P X sigma gamma) :
    Kyprianou.Ch01.IsLinearBrownian P
      (fun t ω => -X t ω) sigma (-gamma) := by
  rcases hX with ⟨hlevy, hcont, hchar⟩
  have hOrig : IsLinearBrownian P X sigma gamma :=
    ⟨hlevy, hcont, hchar⟩
  refine ⟨Kyprianou.Ch01.levyProcess_neg_of_continuous
    P X hlevy hcont, ?_,
    Kyprianou.Ch01.brownianCharFun_reflected
    P X sigma gamma hOrig⟩
  filter_upwards [hcont] with ω hc
  exact hc.neg
