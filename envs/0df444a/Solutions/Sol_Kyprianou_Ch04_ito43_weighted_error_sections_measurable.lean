-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_error_sections_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:55:14.749056+00:00
-- url     : https://prove2.me/submissions/06ce8e68-b0e4-43c3-8b33-a202128b58c8

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_time_integral_measurable
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_grid_sum_measurable
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_jump_integral_measurable
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
theorem solution  {Omega : Type} [MeasurableSpace Omega]
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
    ∀ T : NNReal,
    let B : ℕ → NNReal → Omega → ℝ := fun n t omega =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      ((triplet.gaussianVariance : ℝ) / 2) *
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), g (s,X (Real.toNNReal s) omega) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      g (z.1,Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
      g ((u k : ℝ), X (u k) omega) * (X (v (k+1)) omega - X (v k) omega)^2 / 2)
    ∀ n t, AEMeasurable (B n t) P := by
  intro T B n t
  have hI := ito43_weighted_time_integral_measurable P X hLevy triplet hTriplet Xleft hLeft g hg t
  have hJ := ito43_weighted_jump_integral_measurable P X hLevy triplet hTriplet Xleft hLeft g hg t
  have hG := ito43_weighted_grid_sum_measurable P X hLevy triplet hTriplet Xleft hLeft g hg T n t
  exact ((aemeasurable_const.mul hI).add hJ).sub hG
