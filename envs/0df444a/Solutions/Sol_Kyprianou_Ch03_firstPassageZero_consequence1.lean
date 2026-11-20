-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageZero_consequence1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:25:42.069249+00:00
-- url     : https://prove2.me/submissions/e64dd67c-9e93-4373-960b-5806d80c558e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageFiniteHitMeasurable
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_consequence_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
        forall phi : Real,
      (0 <= phi ∧ L.ψ phi = 0 ∧ (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) ->
      (forall x : Real, 0 <= x ->
        forall finiteTime : Omega -> NNReal,
          (forall omega,
            firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
              firstHittingTime L.X (Set.Ioi x) omega =
                (finiteTime omega : WithTop NNReal)) ->
          (P {omega : Omega |
            firstHittingTime L.X (Set.Ioi x) omega != ⊤}).toReal =
              Real.exp (-phi * x)) := by
  refine fun phi hRoot x hx finiteTime hFinite => ?_
  have hFormula :=
    Kyprianou.Ch03.firstPassageTransform_consequence_zero
      P F L hNotDecreasing 0 rfl phi hRoot x hx finiteTime hFinite
  have hMeas :=
    Kyprianou.Ch03.firstPassageFiniteHitMeasurable P F L x
  have hIndicator :
      (∫ omega,
        if firstHittingTime L.X (Set.Ioi x) omega = ⊤
        then (0 : ℝ) else 1 ∂P) =
      (P {omega : Omega |
        firstHittingTime L.X (Set.Ioi x) omega != ⊤}).toReal := by
    have hfun :
        (fun omega : Omega =>
          if firstHittingTime L.X (Set.Ioi x) omega = ⊤
          then (0 : ℝ) else 1) =
        Set.indicator
          {omega : Omega | firstHittingTime L.X (Set.Ioi x) omega != ⊤}
          (fun _ => (1 : ℝ)) := by
      funext omega
      by_cases htop : firstHittingTime L.X (Set.Ioi x) omega = ⊤
      · simp [Set.indicator, htop]
      · simp [Set.indicator, htop]
    rw [hfun]
    exact MeasureTheory.integral_indicator_one hMeas
  simp only [neg_zero, zero_mul, Real.exp_zero] at hFormula
  rw [hIndicator] at hFormula
  exact hFormula

