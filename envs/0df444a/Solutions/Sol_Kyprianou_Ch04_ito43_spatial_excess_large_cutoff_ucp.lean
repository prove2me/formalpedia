-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_excess_large_cutoff_ucp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:27:48.737484+00:00
-- url     : https://prove2.me/submissions/13284667-bea7-4a2e-9648-15831efd3af3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_pathwise_uniform
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_sup_aemeasurable
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_countable_envelope
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
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
    (f : Real × Real -> Real)
    (hfJointC1 : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (hfSpaceC2 : forall s : NNReal,
      ContDiff Real 2 (fun x : Real => f ((s : Real), x)))
    (hfSpaceSecondContinuous :
      ContinuousOn
        (fun z : Real × Real =>
          iteratedDeriv 2 (fun x : Real => f (z.1, x)) z.2)
        (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    ∀ (T : NNReal) (m : ℕ) (epsilon : ℝ), 0 < epsilon →
      Tendsto (fun n : ℕ =>
        (P {omega : Omega | ∃ t : NNReal, t ≤ T ∧
          let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
          let v : ℕ → NNReal := fun k => min t (u k)
          let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
          epsilon ≤ |(∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
       (f (z.1,Xleft (Real.toNNReal z.1) omega + z.2) -
        f (z.1,Xleft (Real.toNNReal z.1) omega) -
        z.2 * fderiv ℝ f (z.1,Xleft (Real.toNNReal z.1) omega) (0,1) -
        iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2)
          * chi z.2 ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
       let dx := X (v (k+1)) omega - X (v k) omega
       (f ((v k : ℝ),X (v (k+1)) omega) - f ((v k : ℝ),X (v k) omega) -
        deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx -
        iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx^2 / 2)
          * chi dx)|}).toReal) atTop (nhds 0) := by
  intro T m epsilon he
  let E : ℕ → NNReal → Omega → ℝ := fun n t omega =>
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
    (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
     (f (z.1,Xleft (Real.toNNReal z.1) omega + z.2) -
      f (z.1,Xleft (Real.toNNReal z.1) omega) -
      z.2 * fderiv ℝ f (z.1,Xleft (Real.toNNReal z.1) omega) (0,1) -
      iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2)
        * chi z.2 ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
     let dx := X (v (k+1)) omega - X (v k) omega
     (f ((v k : ℝ),X (v (k+1)) omega) - f ((v k : ℝ),X (v k) omega) -
      deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx -
      iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx^2 / 2)
        * chi dx)
  let B : ℕ → Omega → ℝ := fun n w =>
    sSup (Set.range (fun t : Set.Iic T => |E n t w|))
  have hP := Kyprianou.Ch04.ito43_cutoff_pathwise_uniform P X
    hLevy.cadlag_ae Xleft hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T m
  have hM := Kyprianou.Ch04.ito43_cutoff_sup_aemeasurable P X
    hLevy Xleft hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T m
  have hlim : ∀ᵐ w ∂P, Tendsto (fun n => B n w) atTop (nhds 0) := by
    filter_upwards [hP] with w hw
    exact hw.1
  have hbound : ∀ᵐ w ∂P, ∀ n t, t ≤ T → |E n t w| ≤ |B n w| := by
    filter_upwards [hP] with w hw
    exact hw.2
  exact Kyprianou.Ch04.ito43_ucp_countable_envelope P E B T hM hlim hbound epsilon he
