-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_jump_integral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:13:28.679103+00:00
-- url     : https://prove2.me/submissions/d6acbbb1-946e-4964-92d5-f55af85582a8

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_jump_cutoff_measurable
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_jump_cutoff_limit
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
theorem solution   {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      forall t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega)))
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :
    ∀ t : NNReal, AEMeasurable (fun w =>
      ∫ z in Set.Icc (0:ℝ) (t:ℝ) ×ˢ (Set.univ : Set ℝ),
        g (z.1,Xleft (Real.toNNReal z.1) w)*z.2^2/2
          ∂(pathJumpMeasure X Xleft w)) P := by
  intro t
  refine aemeasurable_of_tendsto_metrizable_ae atTop
    (fun m => ito43_weighted_jump_cutoff_measurable P X hLevy triplet hTriplet Xleft hLeft g hg t m) ?_
  exact ito43_weighted_jump_cutoff_limit P X hLevy triplet hTriplet Xleft hLeft g hg t
