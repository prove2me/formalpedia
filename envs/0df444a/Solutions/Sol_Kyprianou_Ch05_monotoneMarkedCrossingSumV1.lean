-- Prove2me | solution 1 for Kyprianou.Ch05.monotoneMarkedCrossingSumV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:36:00.073868+00:00
-- url     : https://prove2.me/submissions/47bc7e6b-5fe1-4162-8477-d7c766a358e8

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_Kyprianou_Ch05_monotoneMarkedCrossingClockUniqueV1
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
    (f : NNReal → ℝ) (hm : Monotone f) (x eta : ℝ) (A B : Set ℝ)
    (T : ENNReal)
    (hT : T = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t})) :
    (if 0 < T.toNNReal ∧ f T.toNNReal > x ∧
        Function.leftLim f T.toNNReal ∈ Icc (0 : ℝ) x ∧
        f T.toNNReal - x ∈ A ∧ x - Function.leftLim f T.toNNReal ∈ B ∧ T ≠ ⊤
      then ENNReal.ofReal (Real.exp (-eta*T.toReal)) else 0) =
      ∑' t : NNReal, if 0 < t ∧ f t > x ∧
        Function.leftLim f t ∈ Icc (0 : ℝ) x ∧ f t - x ∈ A ∧
        x - Function.leftLim f t ∈ B then ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0 := by
  classical
  let D (t : NNReal) := 0 < t ∧ f t > x ∧ Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
    f t - x ∈ A ∧ x - Function.leftLim f t ∈ B
  have hc (t : NNReal) (ht : D t) : T = (t : ENNReal) :=
    hT.trans (monotoneMarkedCrossingClockUniqueV1 f hm x t ht.1 ht.2.1 ht.2.2.1.2)
  have hzero (t : NNReal) (ht : t ≠ T.toNNReal) :
      (if D t then ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0) = 0 := by
    have hn : ¬ D t := fun hd => ht (by rw [hc t hd]; simp)
    rw [if_neg hn]
  have hD : (D T.toNNReal ∧ T ≠ ⊤) =
      (0 < T.toNNReal ∧ f T.toNNReal > x ∧
        Function.leftLim f T.toNNReal ∈ Icc (0 : ℝ) x ∧
        f T.toNNReal - x ∈ A ∧ x - Function.leftLim f T.toNNReal ∈ B ∧ T ≠ ⊤) := by
    simp only [D,and_assoc]
  have hs : (∑' t : NNReal, if D t then ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0) =
      (if D T.toNNReal then ENNReal.ofReal (Real.exp (-eta*(T.toNNReal : ℝ))) else 0) :=
    tsum_eq_single T.toNNReal hzero
  calc
    _ = (if D T.toNNReal ∧ T ≠ ⊤ then ENNReal.ofReal (Real.exp (-eta*T.toReal)) else 0) := by
      simp only [D,and_assoc]
    _ = (if D T.toNNReal then ENNReal.ofReal (Real.exp (-eta*(T.toNNReal : ℝ))) else 0) := by
      by_cases hd : D T.toNNReal
      · have hf : T ≠ ⊤ := by rw [hc _ hd]; exact ENNReal.coe_ne_top
        rw [if_pos ⟨hd,hf⟩,if_pos hd,ENNReal.coe_toNNReal_eq_toReal]
      · simp [hd]
    _ = _ := hs.symm
