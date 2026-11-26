-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_right_continuous_bounded_path
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:52:23.010208+00:00
-- url     : https://prove2.me/submissions/3e4d35c3-d84d-456b-b7cd-b3fbc223ea49
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
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_taylor_kernel_data
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_error_kernel_identity
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_generic_right_continuous_bounded
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
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
    ∀ᵐ w ∂P, ∀ n,
      (∀ t, ContinuousWithinAt (fun s => |E n s w|) (Set.Ici t) t) ∧
      BddAbove (Set.range (fun t : Set.Iic T => |E n t w|)) := by
  intro T m E
  let K : NNReal → ℝ → ℝ → ℝ := fun s x z =>
    (f ((s : ℝ),x+z) - f ((s : ℝ),x) -
      deriv (fun y : ℝ => f ((s : ℝ),y)) x*z -
      iteratedDeriv 2 (fun y : ℝ => f ((s : ℝ),y)) x*z^2/2) *
    min 1 (max 0 (|z| * ((m : ℝ)+1)-1))
  obtain ⟨hK,hzero⟩ := Kyprianou.Ch04.ito43_cutoff_taylor_kernel_data
    f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous m
  have hRep := Kyprianou.Ch04.ito43_cutoff_error_kernel_identity
    P X hCad Xleft hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T m
  filter_upwards [hCad,hLeft,hRep] with w hc hl hr
  have hG := Kyprianou.Ch04.ito43_cutoff_generic_right_continuous_bounded
    (fun s => X s w) (fun s => Xleft s w) hc hl K hK
    (1/((m:ℝ)+1)) (by positivity) hzero T
  intro n
  let G : NNReal → ℝ := fun t =>
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∑' s : Set.Ioc (0 : NNReal) t,
      K s.1 (Xleft s.1 w) (X s.1 w-Xleft s.1 w)) -
    (∑ k ∈ Finset.range n, K (u k) (X (u k) w)
      (X (v (k+1)) w-X (v k) w))
  have hEq : (fun t => |E n t w|) = (fun t => |G t|) :=
    funext fun t => congrArg abs (hr n t)
  have hEq2 : (fun t : Set.Iic T => |E n t w|) =
      (fun t : Set.Iic T => |G t|) :=
    funext fun t => congrArg abs (hr n t.1)
  rw [hEq,hEq2]
  exact hG n
