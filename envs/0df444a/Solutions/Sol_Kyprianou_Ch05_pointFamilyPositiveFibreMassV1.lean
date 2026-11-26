-- Prove2me | solution 1 for Kyprianou.Ch05.pointFamilyPositiveFibreMassV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:26:56.944078+00:00
-- url     : https://prove2.me/submissions/01e7e43e-c3ef-4044-9558-417218b7a258

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_pointFamilyPairLIntegralV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Omega : Type} (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → ℝ × ℝ)
    (w : Omega)
    (hinj : ∀ i j : ℕ × ℕ, i.2 < K i.1 w → j.2 < K j.1 w →
      (Z i.1 i.2 w).1 = (Z j.1 j.2 w).1 → i = j)
    (i : ℕ × ℕ) (hi : i.2 < K i.1 w) (hz : 0 < (Z i.1 i.2 w).2) :
    (∫⁻ z in {(Z i.1 i.2 w).1} ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)) =
      ENNReal.ofReal (Z i.1 i.2 w).2 := by
  classical
  let S := {(Z i.1 i.2 w).1} ×ˢ Ioi (0 : ℝ)
  have hS : MeasurableSet S := (measurableSet_singleton _).prod measurableSet_Ioi
  let g : ℝ × ℝ → ENNReal := S.indicator (fun z => ENNReal.ofReal z.2)
  have hg : Measurable g := (ENNReal.measurable_ofReal.comp measurable_snd).indicator hS
  change (∫⁻ z in S, ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)) = _
  rw [← lintegral_indicator hS,pointFamilyPairLIntegralV1 K Z w g hg]
  have hzero (j : ℕ × ℕ) (hji : j ≠ i) :
      (if j.2 < K j.1 w then g (Z j.1 j.2 w) else 0) = 0 := by
    by_cases hj : j.2 < K j.1 w
    · rw [if_pos hj]
      apply Set.indicator_of_notMem
      intro hm
      exact hji (hinj j i hj hi hm.1)
    · exact if_neg hj
  rw [tsum_eq_single i hzero,if_pos hi]
  exact Set.indicator_of_mem (show Z i.1 i.2 w ∈ S from ⟨rfl,hz⟩) _
