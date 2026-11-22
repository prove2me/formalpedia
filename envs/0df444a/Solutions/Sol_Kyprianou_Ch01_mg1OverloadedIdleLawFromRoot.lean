-- Prove2me | solution 1 for Kyprianou.Ch01.mg1OverloadedIdleLawFromRoot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:34:33.815303+00:00
-- url     : https://prove2.me/submissions/0e249d06-025f-4100-81b4-05affd29cb0c

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_mg1OverloadedZeroIdleAtomFromRoot
import Theorems.Thm_Kyprianou_Ch01_mg1OverloadedPositiveIdleCDFfromRoot
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

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
    (theta : ℝ) (htheta : 0 < theta)
    (hroot : queueLaplaceExponent rate F theta = 0) :
    ∀ w : ℝ, 0 ≤ w →
      (P {ω | totalIdleTime arrival claims w ω = 0}).toReal =
        1 - Real.exp (-theta * w) ∧
      ∀ x : ℝ, 0 ≤ x →
        (P {ω | (0 : ℝ≥0∞) < totalIdleTime arrival claims w ω ∧
          totalIdleTime arrival claims w ω ≤ ENNReal.ofReal x}).toReal =
            Real.exp (-theta * w) * (1 - Real.exp (-theta * x)) := by
  intro w hw
  exact ⟨Kyprianou.Ch01.mg1OverloadedZeroIdleAtomFromRoot
    P arrival claims rate F hd hrate mu hmu
      hclaimpos hclaimint hmean theta htheta hroot w hw,
    Kyprianou.Ch01.mg1OverloadedPositiveIdleCDFfromRoot
      P arrival claims rate F hd hrate mu hmu
        hclaimpos hclaimint hmean theta htheta hroot w hw⟩
