-- Prove2me | solution 1 for Kyprianou.Ch04.conditionalENNClockBalance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:28:33.071805+00:00
-- url     : https://prove2.me/submissions/32fb3498-a7f2-4c8e-9f31-bdcb533ddf4e

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_conditionalEventCutoffCompensationENN
import Theorems.Thm_Kyprianou_Ch04_eventCutoffRawIntegral
import Theorems.Thm_Kyprianou_Ch04_eventCutoffIntensityIntegral
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04
/-- Eventwise balance of raw and compensator extended clocks. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real → Real → Omega → Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ w ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x w)
        (nhdsWithin (t : Real) (Set.Iio (t : Real))) (nhds (phi (t : Real) x w)))
    (hJ : ∀ t : NNReal, Measurable ((fun (t : NNReal) w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)) t))
    (hC : ∀ t : NNReal, Measurable ((fun (t : NNReal) w => ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume) t))
    (u t : NNReal) (hut : u ≤ t) (A : Set Omega) (hA : MeasurableSet[F u] A) :
    (∫⁻ w in A, (fun (t : NNReal) w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)) t w ∂P) + (∫⁻ w in A, (fun (t : NNReal) w => ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume) u w ∂P) =
    (∫⁻ w in A, (fun (t : NNReal) w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)) u w ∂P) + (∫⁻ w in A, (fun (t : NNReal) w => ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume) t w ∂P) := by
  let J := (fun (t : NNReal) w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w))
  let C := (fun (t : NNReal) w => ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume)
  let V (w : Omega) := ∫⁻ z in Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ,
    ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)
  let W (w : Omega) := ∫⁻ s in Set.Ioc (u : ℝ) (t : ℝ),
    ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume
  have hA' : MeasurableSet A := F.le u A hA
  have he : (∫⁻ w in A, V w ∂P) = ∫⁻ w in A, W w ∂P := by
    exact (eventCutoffRawIntegral P levyMeasure N phi u t A hA').symm.trans
      ((conditionalEventCutoffCompensationENN P levyMeasure F N hFuture phi
        hPhi hCommon u t A hA).trans (eventCutoffIntensityIntegral P levyMeasure phi u t A hA'))
  have hu : (Set.Icc (0 : ℝ) (u : ℝ)) ∪ Set.Ioc (u : ℝ) (t : ℝ) =
      Set.Icc 0 (t : ℝ) :=
    Set.Icc_union_Ioc_eq_Icc (by positivity) (by exact_mod_cast hut)
  have hd : Disjoint (Set.Icc (0 : ℝ) (u : ℝ)) (Set.Ioc (u : ℝ) (t : ℝ)) :=
    Set.disjoint_left.mpr fun _ ha hb => (not_lt_of_ge ha.2) hb.1
  have hprod : (Set.Icc (0 : ℝ) (u : ℝ) ×ˢ (Set.univ : Set ℝ)) ∪
      (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ) =
      Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ := by
    rw [← Set.union_prod, hu]
  have hpd : Disjoint (Set.Icc (0 : ℝ) (u : ℝ) ×ˢ (Set.univ : Set ℝ))
      (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ) :=
    Set.disjoint_left.mpr fun _ ha hb => (not_lt_of_ge ha.1.2) hb.1.1
  have hj (w : Omega) : J t w = J u w + V w := by
    dsimp [J, V]
    rw [← hprod, lintegral_union (measurableSet_Ioc.prod MeasurableSet.univ) hpd]
  have hc (w : Omega) : C t w = C u w + W w := by
    dsimp [C, W]
    rw [← hu, lintegral_union measurableSet_Ioc hd]
  change (∫⁻ w in A, J t w ∂P) + (∫⁻ w in A, C u w ∂P) =
    (∫⁻ w in A, J u w ∂P) + (∫⁻ w in A, C t w ∂P)
  have hj' : J t = fun w => J u w + V w := funext hj
  have hc' : C t = fun w => C u w + W w := funext hc
  have hjA : (∫⁻ w in A, J t w ∂P) =
      (∫⁻ w in A, J u w ∂P) + (∫⁻ w in A, V w ∂P) := by
    rw [hj']
    exact lintegral_add_left (show Measurable (J u) from hJ u) V
  have hcA : (∫⁻ w in A, C t w ∂P) =
      (∫⁻ w in A, C u w ∂P) + (∫⁻ w in A, W w ∂P) := by
    rw [hc']
    exact lintegral_add_left (show Measurable (C u) from hC u) W
  rw [hjA, hcA, he]
  ac_rfl
