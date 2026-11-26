-- Prove2me | solution 1 for Kyprianou.Ch05.positiveLevyMeasureEqOfDeficitPlusDrift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:04:14.852162+00:00
-- url     : https://prove2.me/submissions/07693c63-4714-469e-a688-89ff5fa9c761

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_Kyprianou_Ch05_positiveDeficitSecondDifferenceLaplace
import Theorems.Thm_Kyprianou_Ch05_positiveDeficitSquaredDensityInjective
import Theorems.Thm_Kyprianou_Ch05_measureEqOfFinitePositiveLaplace
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu nu : Measure Real) (d : Real)
    (hm : mu (Set.Iic (0 : Real)) = 0)
    (hn : nu (Set.Iic (0 : Real)) = 0)
    (hmi : ∀ t : Real, 0 < t →
      IntegrableOn (fun x : Real => 1 - Real.exp (-t*x)) (Set.Ioi 0) mu)
    (hni : ∀ t : Real, 0 < t →
      IntegrableOn (fun x : Real => 1 - Real.exp (-t*x)) (Set.Ioi 0) nu)
    (heq : ∀ t : Real, 0 < t →
      d*t + (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-t*x)) ∂mu) =
      (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-t*x)) ∂nu)) :
    mu = nu := by
  apply Kyprianou.Ch05.positiveDeficitSquaredDensityInjective mu nu hm hn
  apply Kyprianou.Ch05.measureEqOfFinitePositiveLaplace
  · intro t ht
    exact (Kyprianou.Ch05.positiveDeficitSecondDifferenceLaplace mu hm hmi t ht).1
  · intro t ht
    rw [(Kyprianou.Ch05.positiveDeficitSecondDifferenceLaplace mu hm hmi t ht).2,
      (Kyprianou.Ch05.positiveDeficitSecondDifferenceLaplace nu hn hni t ht).2]
    congr 1
    have h0 := heq t ht
    have h1 := heq (t+1) (by linarith)
    have h2 := heq (t+2) (by linarith)
    linarith
