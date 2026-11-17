-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_charfun_continuous_in_rate
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:06:53.65624+00:00
-- url     : https://prove2.me/submissions/eae36b7a-1d4c-49bc-a00a-3f3e2886b94a

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

theorem poisson_charfun_continuous_in_rate
    (rate : ℕ → ℝ≥0) (r : ℝ≥0)
    (hrate : Tendsto rate atTop (𝓝 r)) (t : ℝ) :
    Tendsto (fun n => charFun ((poissonMeasure (rate n)).map
      (Nat.cast : ℕ → ℝ)) t)
      atTop (𝓝 (charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) t)) := by
  simp_rw [charFun_map_cast_poissonMeasure]
  apply Tendsto.cexp
  apply Tendsto.mul_const
  have h1 : Tendsto (fun n => ((rate n : ℝ) : ℂ)) atTop (𝓝 ((r : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp ((NNReal.continuous_coe.tendsto r).comp hrate)
  simpa using h1

end Kyprianou.ProofPreparation

theorem solution
    (rate : ℕ → ℝ≥0) (r : ℝ≥0)
    (hrate : Tendsto rate atTop (𝓝 r)) (t : ℝ) :
    Tendsto (fun n => charFun ((poissonMeasure (rate n)).map
      (Nat.cast : ℕ → ℝ)) t)
      atTop (𝓝 (charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) t)) := by
  first
  | exact Kyprianou.ProofPreparation.poisson_charfun_continuous_in_rate
  | exact Kyprianou.ProofPreparation.poisson_charfun_continuous_in_rate ..
  | (apply Kyprianou.ProofPreparation.poisson_charfun_continuous_in_rate <;> assumption)
