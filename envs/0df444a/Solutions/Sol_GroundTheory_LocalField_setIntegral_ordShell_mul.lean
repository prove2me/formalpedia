-- Prove2me | solution 1 for GroundTheory.LocalField.setIntegral_ordShell_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:05:41.571461+00:00
-- url     : https://prove2.me/submissions/f94d576d-fe2a-4a9a-a3f6-7e179d46ff0f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Theorems.Thm_GroundTheory_LocalField_measurableSet_ordShell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Kˣ → E) (v : Kˣ) (k : ℤ) :
    ∫ u in ordShell K (ord (v : K) + k), F u ∂multHaar K =
      ∫ u in ordShell K k, F (v * u) ∂multHaar K := by
  rw [← integral_indicator (measurableSet_ordShell _), ← integral_indicator (measurableSet_ordShell _),
    ← integral_mul_left_eq_self _ v]
  congr 1
  funext u
  by_cases hu : u ∈ ordShell K k
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem ((mul_mem_ordShell_iff v).mpr hu)]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt (mul_mem_ordShell_iff v).mp hu)]
end GroundTheory.LocalField
