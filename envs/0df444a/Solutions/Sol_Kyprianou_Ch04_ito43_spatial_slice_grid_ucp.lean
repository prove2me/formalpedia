-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_slice_grid_ucp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:53:23.054899+00:00
-- url     : https://prove2.me/submissions/5a4ff2c7-026f-4f46-8e2d-4ee3fb0d3d82

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_quadratic_grid_ucp
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_taylor_excess_ucp
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_transfer
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Split the spatial residual into weighted quadratic variation and Taylor excess. -/
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
        (Set.prod (Set.Ici (0 : Real)) Set.univ))
 :
    ∀ (T : NNReal) (epsilon : Real), 0 < epsilon →
    Tendsto (fun n : Nat =>
      (P {omega : Omega | ∃ t : NNReal, t ≤ T ∧
        let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
        let v : ℕ → NNReal := fun k => min t (u k)
        epsilon ≤ abs (((triplet.gaussianVariance : Real) / 2) *
          (∫ s in Set.Icc (0 : Real) (t : Real),
            iteratedDeriv 2 (fun x : Real => f ((s : Real), x))
              (X (Real.toNNReal s) omega) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega) -
           z.2 * fderiv Real f
             (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1))
          ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
          (f ((v k : Real), X (v (k+1)) omega) -
          f ((v k : Real), X (v k) omega) -
          deriv (fun x : Real => f ((u k : Real), x)) (X (u k) omega) *
            (X (v (k+1)) omega - X (v k) omega))))}).toReal)
      atTop (nhds 0) := by
  intro T e he
  let Q : NNReal → Omega → ℝ := fun t omega => ((triplet.gaussianVariance : ℝ) / 2) *
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), iteratedDeriv 2 (fun x : ℝ => f (s,x)) (X (Real.toNNReal s) omega) ∂volume)
  let J : NNReal → Omega → ℝ := fun t omega => (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega) -
           z.2 * fderiv Real f
             (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1))
          ∂(pathJumpMeasure X Xleft omega))
  let JQ : NNReal → Omega → ℝ := fun t omega => (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega))
  let W : ℕ → NNReal → Omega → ℝ := fun n t omega =>
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∑ k ∈ Finset.range n,
      iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * (X (v (k+1)) omega - X (v k) omega)^2 / 2)
  let A : ℕ → NNReal → Omega → ℝ := fun n t omega =>
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∑ k ∈ Finset.range n,
          (f ((v k : Real), X (v (k+1)) omega) -
          f ((v k : Real), X (v k) omega) -
          deriv (fun x : Real => f ((u k : Real), x)) (X (u k) omega) *
            (X (v (k+1)) omega - X (v k) omega)))
  let E : ℕ → NNReal → Omega → ℝ := fun n t w => Q t w + JQ t w - W n t w
  let G : ℕ → NNReal → Omega → ℝ := fun n t w => J t w - JQ t w - (A n t w - W n t w)
  let H : ℕ → NNReal → Omega → ℝ := fun n t w => Q t w + J t w - A n t w
  have hE : ∀ e : ℝ, 0 < e → Tendsto
      (fun n => (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal) atTop (nhds 0) :=
    Kyprianou.Ch04.ito43_weighted_quadratic_grid_ucp P X hLevy triplet hTriplet Xleft
      hLeft (fun z : ℝ × ℝ => iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) z.2) hfSpaceSecondContinuous T
  have hG : ∀ e : ℝ, 0 < e → Tendsto
      (fun n => (P {w | ∃ t ≤ T, e ≤ |G n t w|}).toReal) atTop (nhds 0) :=
    Kyprianou.Ch04.ito43_spatial_taylor_excess_ucp P X hLevy triplet hTriplet Xleft
      hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T
  apply Kyprianou.Ch04.ito43_ucp_transfer P E G H T hE hG _ e he
  intro n hn t ht w
  dsimp only [E,G,H]
  ring
