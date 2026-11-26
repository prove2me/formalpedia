-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_taylor_excess_ucp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:05:02.331306+00:00
-- url     : https://prove2.me/submissions/bd9911b3-ad01-4cad-b78c-bd4fd038956f
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
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_excess_large_cutoff_ucp
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_excess_small_tail
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_approximation
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Continuous cutoff decomposition of the Taylor excess. -/
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
    ∀ (T : NNReal) (epsilon : ℝ), 0 < epsilon →
      Tendsto (fun n : ℕ =>
        (P {omega : Omega | ∃ t : NNReal, t ≤ T ∧
          let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
          let v : ℕ → NNReal := fun k => min t (u k)
          epsilon ≤ |(∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega) -
           z.2 * fderiv Real f
             (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1))
          ∂(pathJumpMeasure X Xleft omega)) - (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega)) - ((∑ k ∈ Finset.range n,
          (f ((v k : Real), X (v (k+1)) omega) -
          f ((v k : Real), X (v k) omega) -
          deriv (fun x : Real => f ((u k : Real), x)) (X (u k) omega) *
            (X (v (k+1)) omega - X (v k) omega))) - (∑ k ∈ Finset.range n,
      iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * (X (v (k+1)) omega - X (v k) omega)^2 / 2))|}).toReal) atTop (nhds 0) := by
  intro T e he
  let E : ℕ → NNReal → Omega → ℝ := fun n t omega =>
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega) -
           z.2 * fderiv Real f
             (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1))
          ∂(pathJumpMeasure X Xleft omega)) - (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega)) - ((∑ k ∈ Finset.range n,
          (f ((v k : Real), X (v (k+1)) omega) -
          f ((v k : Real), X (v k) omega) -
          deriv (fun x : Real => f ((u k : Real), x)) (X (u k) omega) *
            (X (v (k+1)) omega - X (v k) omega))) - (∑ k ∈ Finset.range n,
      iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * (X (v (k+1)) omega - X (v k) omega)^2 / 2))
  let A : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t omega =>
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
  let B : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t w => E n t w - A m n t w
  have hA : ∀ (m : ℕ) (a : ℝ), 0 < a → Tendsto
      (fun n => (P {w | ∃ t ≤ T, a ≤ |A m n t w|}).toReal) atTop (nhds 0) :=
    Kyprianou.Ch04.ito43_spatial_excess_large_cutoff_ucp P X hLevy triplet hTriplet Xleft
      hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T
  have hB : ∀ a : ℝ, 0 < a → ∀ eta : ℝ, 0 < eta → ∃ m : ℕ,
      ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, a ≤ |B m n t w|}).toReal ≤ eta :=
    Kyprianou.Ch04.ito43_spatial_excess_small_tail P X hLevy triplet hTriplet Xleft
      hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T
  apply Kyprianou.Ch04.ito43_ucp_approximation P E A B T _ hA hB e he
  intro m n t w
  dsimp only [B]
  ring
