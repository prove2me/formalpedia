-- Prove2me | solution 1 for Kyprianou.Ch02.prmEqualGridCellTwoPointBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:58:35.208426+00:00
-- url     : https://prove2.me/submissions/740fd68f-1242-4347-aa0f-30d76e1fefc9

import Theorems.Thm_Kyprianou_Ch02_poissonRegionTwoOrMoreBoundV1
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (A : Set ℝ) (hA : MeasurableSet A) (hfin : ν A < ⊤)
    (a d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    (P {ω | 1 < N.N ω (Set.Ioc a (a+d) ×ˢ A)}).toReal ≤
      (d * (ν A).toReal)^2 := by
  let R := Set.Ioc a (a+d) ×ˢ A
  have hR : MeasurableSet R := measurableSet_Ioc.prod hA
  have hvalue : LevyStochCalc.Poisson.referenceIntensity ν R =
      ENNReal.ofReal d * ν A := by
    have hset : Set.Ioc a (a+d) ∩ Set.Ici (0 : ℝ) = Set.Ioc a (a+d) := by
      apply Set.inter_eq_left.mpr
      intro x hx
      exact ha.trans hx.1.le
    dsimp [R]
    rw [LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod,
      Measure.restrict_apply measurableSet_Ioc, hset, Real.volume_Ioc]
    congr 2
    ring
  have hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤ := by
    rw [hvalue]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have H := Kyprianou.Ch02.poissonRegionTwoOrMoreBoundV1 P ν N R hR hRfin
  rw [hvalue, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd] at H
  exact H
