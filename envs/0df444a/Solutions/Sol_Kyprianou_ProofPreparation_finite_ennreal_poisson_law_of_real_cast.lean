-- Prove2me | solution 1 for Kyprianou.ProofPreparation.finite_ennreal_poisson_law_of_real_cast
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:06:55.034211+00:00
-- url     : https://prove2.me/submissions/be6e412d-6b42-45c0-ae1a-e5c206bc9aa4

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem finite_ennreal_poisson_law_of_real_cast
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (S : Omega -> ENNReal) (rate : NNReal)
    (hS : AEMeasurable S P)
    (hfinite : ∀ᵐ w ∂P, S w < ⊤)
    (hreal :
      P.map (fun w => (S w).toReal) =
        (poissonMeasure rate).map (Nat.cast : Nat -> Real)) :
    P.map S = (poissonMeasure rate).map (Nat.cast : Nat -> ENNReal) := by
  have h1 : P.map S = P.map (ENNReal.ofReal ∘ (fun w => (S w).toReal)) := by
    apply Measure.map_congr
    filter_upwards [hfinite] with w hw
    simp [ENNReal.ofReal_toReal hw.ne]
  have hm : AEMeasurable (fun w => (S w).toReal) P := ENNReal.measurable_toReal.comp_aemeasurable hS
  rw [h1, ← AEMeasurable.map_map_of_aemeasurable ENNReal.measurable_ofReal.aemeasurable hm, hreal,
    AEMeasurable.map_map_of_aemeasurable ENNReal.measurable_ofReal.aemeasurable
      measurable_from_nat.aemeasurable]
  congr 1
  funext n
  simp

end Kyprianou.ProofPreparation

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (S : Omega -> ENNReal) (rate : NNReal)
    (hS : AEMeasurable S P)
    (hfinite : ∀ᵐ w ∂P, S w < ⊤)
    (hreal :
      P.map (fun w => (S w).toReal) =
        (poissonMeasure rate).map (Nat.cast : Nat -> Real)) :
    P.map S = (poissonMeasure rate).map (Nat.cast : Nat -> ENNReal) := by
  first
  | exact Kyprianou.ProofPreparation.finite_ennreal_poisson_law_of_real_cast
  | exact Kyprianou.ProofPreparation.finite_ennreal_poisson_law_of_real_cast ..
  | (apply Kyprianou.ProofPreparation.finite_ennreal_poisson_law_of_real_cast <;> assumption)
