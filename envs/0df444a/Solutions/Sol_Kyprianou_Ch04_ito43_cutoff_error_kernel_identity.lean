-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_error_kernel_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:03:37.678751+00:00
-- url     : https://prove2.me/submissions/42523e7e-f011-4e88-a607-6efd44e3b11f

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_atomic_integral_identity
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_grid_kernel_identity
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hCad : ∀ᵐ w ∂P, IsCadlag (fun t => X t w))
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
    ∀ (T : NNReal) (m : ℕ),
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
    let K : NNReal → ℝ → ℝ → ℝ := fun s x z =>
      (f ((s : ℝ),x+z) - f ((s : ℝ),x) -
        deriv (fun y : ℝ => f ((s : ℝ),y)) x*z -
        iteratedDeriv 2 (fun y : ℝ => f ((s : ℝ),y)) x*z^2/2) *
      min 1 (max 0 (|z| * ((m : ℝ)+1)-1))
    ∀ᵐ w ∂P, ∀ (n : ℕ) (t : NNReal),
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      E n t w =
        (∑' s : Set.Ioc (0 : NNReal) t,
          K s.1 (Xleft s.1 w) (X s.1 w-Xleft s.1 w)) -
        (∑ k ∈ Finset.range n, K (u k) (X (u k) w)
          (X (v (k+1)) w-X (v k) w)) := by
  intro T m E K
  have ha := Kyprianou.Ch04.ito43_cutoff_atomic_integral_identity
    P X hCad Xleft hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous m
  have hg := Kyprianou.Ch04.ito43_cutoff_grid_kernel_identity
    P X hCad Xleft hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T m
  filter_upwards [ha] with w hw
  intro n t u v
  exact congrArg₂ (· - ·) (hw t) (hg n t w)
