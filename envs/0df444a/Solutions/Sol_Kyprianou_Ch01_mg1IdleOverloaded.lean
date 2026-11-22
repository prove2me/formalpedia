-- Prove2me | solution 1 for Kyprianou.Ch01.mg1IdleOverloaded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:21:58.537751+00:00
-- url     : https://prove2.me/submissions/b1f563b1-ec8a-4889-948b-598d8ce96e10

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponentStrictConvexAndRoot
import Theorems.Thm_Kyprianou_Ch01_mg1OverloadedIdleLawFromRoot
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
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
    (hoverload : 1 < (rate : ℝ) * mu) :
    ∃ theta : ℝ,
      0 < theta ∧ queueLaplaceExponent rate F theta = 0 ∧
      (∀ u : ℝ, theta < u → queueLaplaceExponent rate F u ≠ 0) ∧
      ∀ w : ℝ, 0 ≤ w →
        (P {ω | totalIdleTime arrival claims w ω = 0}).toReal =
          1 - Real.exp (-theta * w) ∧
        ∀ x : ℝ, 0 ≤ x →
          (P {ω | (0 : ℝ≥0∞) < totalIdleTime arrival claims w ω ∧
            totalIdleTime arrival claims w ω ≤ ENNReal.ofReal x}).toReal =
              Real.exp (-theta * w) * (1 - Real.exp (-theta * x)) := by
  have hprops := Kyprianou.Ch01.queueLaplaceExponentStrictConvexAndRoot
    rate hrate F hclaimpos hclaimint mu hmu hmean
  obtain ⟨theta, htheta, hroot⟩ := hprops.2.2.2.1.mpr hoverload
  refine ⟨theta, htheta, hroot, ?_, ?_⟩
  · intro v hv hvr
    have heq : theta = v :=
      hprops.2.2.2.2 theta v htheta (lt_trans htheta hv) hroot hvr
    exact (ne_of_lt hv) heq
  · exact Kyprianou.Ch01.mg1OverloadedIdleLawFromRoot
      P arrival claims rate F hd hrate mu hmu
      hclaimpos hclaimint hmean theta htheta hroot
