-- Prove2me | solution 1 for Kyprianou.Ch05.renewalJointOvershootUndershoot
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @DAGA
-- created : 2026-11-26T03:10:58.219565+00:00
-- url     : https://prove2.me/submissions/1139647f-f616-4a81-82ce-fa9ebe2a132a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Theorems.Thm_Kyprianou_Ch05_renewalJointFiniteLevelSum
import Theorems.Thm_Kyprianou_Ch05_renewalKernelSumInterchange
import Theorems.Thm_Kyprianou_Ch05_renewalMeanPos
import Theorems.Thm_Kyprianou_Ch05_renewalTailDRI
import Theorems.Thm_Kyprianou_Ch05_renewalTailEventKernel
import Theorems.Thm_Kyprianou_Ch05_renewalTailIntegralEq
import Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_keyRenewalConvolution
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
open Kyprianou.Ch05
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F) :
  ((∀ (x : Real), 0 < x →
      ∀ (A B : Set Real), MeasurableSet A → MeasurableSet B →
        A ⊆ Set.Ioi (0 : Real) →
        B ⊆ Set.Ioc (0 : Real) x →
          P {omega : Omega |
            0 < renewalOvershoot Z x omega ∧
            renewalOvershoot Z x omega ∈ A ∧
            renewalUndershoot Z x omega ∈ B} =
          renewalJointKernel (renewalMeasure F) F x A B) ∧
   ((Integrable (fun z : Real => z) F) →
      NonLatticeMeasure F →
        ∀ (u y : Real), 0 < u → 0 < y →
          Tendsto
            (fun x : Real =>
              (P {omega : Omega |
                u < renewalOvershoot Z x omega ∧
                y < renewalUndershoot Z x omega}).toReal)
            atTop
            (nhds
              ((∫ z in Set.Ioi (u+y),
                 (F (Set.Ioi z)).toReal ∂volume) /
                (∫ z : Real, z ∂F))))) := by
  refine ⟨?_, ?_⟩
  · intro x hx A B hA hB hA2 hB2
    exact (renewalJointFiniteLevelSum P Z F hRenewal x hx A B hA hB hA2 hB2).trans
      (renewalKernelSumInterchange F x A B)
  · intro hInt hNL u y hu hy
    haveI : IsProbabilityMeasure F := by
      refine ⟨?_⟩
      rw [← hRenewal.2.1 0, Measure.map_apply (hRenewal.1 0) MeasurableSet.univ,
        Set.preimage_univ, measure_univ]
    have hmu : 0 < ∫ z : Real, z ∂F := renewalMeanPos P Z F hRenewal hInt
    have hlim : Tendsto
        (fun x : Real => ∫ z in Set.Icc (0 : Real) x,
          (fun t : Real => if y < t then (F (Set.Ioi (t + u))).toReal else 0) (x - z)
          ∂(renewalMeasure F))
        atTop
        (nhds ((∫ z in Set.Ici (0 : Real),
          (fun t : Real => if y < t then (F (Set.Ioi (t + u))).toReal else 0) z ∂volume) /
          ∫ z : Real, z ∂F)) :=
      classicalRenewalTheorem_keyRenewalConvolution F hRenewal.2.2.1 hInt hmu hNL _
        (renewalTailDRI F hRenewal.2.2.1 hInt u y hu hy)
    rw [show (∫ z in Set.Ici (0 : Real),
          (fun t : Real => if y < t then (F (Set.Ioi (t + u))).toReal else 0) z ∂volume)
        = ∫ z in Set.Ioi (u + y), (F (Set.Ioi z)).toReal ∂volume from
      renewalTailIntegralEq F u y] at hlim
    refine Tendsto.congr' ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    exact (renewalTailEventKernel P Z F hRenewal x u y hx hu hy).symm
