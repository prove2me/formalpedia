-- Prove2me | solution 1 for Kyprianou.Ch01.mg1IdleCriticalAndLight
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T09:47:02.939593+00:00
-- url     : https://prove2.me/submissions/d1981b20-f213-4a5a-9fa9-f008b6b29036

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_mg1IdleLight
import Theorems.Thm_Kyprianou_Ch01_mg1IdleCritical

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal

set_option autoImplicit false
universe u

/-- Reduction of Theorem 1.11(ii) (infinite M/G/1 idle time for traffic intensity ≤ 1)
into strictly subcritical (light traffic) and critical traffic intensity cases. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (hload : (rate : ℝ) * mu ≤ 1) :
    ∀ w : ℝ, 0 ≤ w →
      (P {ω | totalIdleTime arrival claims w ω = ⊤}).toReal = 1 := by
  intro w hw
  rcases lt_or_eq_of_le hload with hlight | hcritical
  · exact Kyprianou.Ch01.mg1IdleLight
      P arrival claims rate F hd hrate mu hmu hclaimpos hclaimint hmean hlight w hw
  · exact Kyprianou.Ch01.mg1IdleCritical
      P arrival claims rate F hd hrate mu hmu hclaimpos hclaimint hmean hcritical w hw
