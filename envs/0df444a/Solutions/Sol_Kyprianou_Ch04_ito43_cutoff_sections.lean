-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_sections
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:43:28.274532+00:00
-- url     : https://prove2.me/submissions/ca73d798-69a5-46e3-a2f8-6fc360f13c5b
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
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_grid_sections
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_pathwise_uniform
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
    ∀ n t, AEMeasurable (E n t) P := by
  intro T m E n t
  let J : NNReal → Omega → ℝ := fun t omega =>
    let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
    (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
       (f (z.1,Xleft (Real.toNNReal z.1) omega + z.2) -
        f (z.1,Xleft (Real.toNNReal z.1) omega) -
        z.2 * fderiv ℝ f (z.1,Xleft (Real.toNNReal z.1) omega) (0,1) -
        iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2)
          * chi z.2 ∂(pathJumpMeasure X Xleft omega))
  let S : NNReal → ℕ → NNReal → Omega → ℝ := fun H n t omega =>
    let u : ℕ → NNReal := fun k => H * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
    (∑ k ∈ Finset.range n,let dx := X (v (k+1)) omega - X (v k) omega
     (f ((v k : ℝ),X (v (k+1)) omega) - f ((v k : ℝ),X (v k) omega) -
      deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx -
      iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx^2 / 2)
        * chi dx)
  have hS (H : NNReal) (j : ℕ) (r : NNReal) :
      AEMeasurable (S H j r) P :=
    Kyprianou.Ch04.ito43_cutoff_grid_sections P X hLevy Xleft hLeft f
      hfJointC1 hfSpaceC2 hfSpaceSecondContinuous H m j r
  have hP := Kyprianou.Ch04.ito43_cutoff_pathwise_uniform P X hLevy.cadlag_ae
    Xleft hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous t m
  have hJ : AEMeasurable (J t) P := by
    refine aemeasurable_of_tendsto_metrizable_ae atTop (fun j => hS t j t) ?_
    filter_upwards [hP] with w hw
    obtain ⟨hl,hbound⟩ := hw
    apply Metric.tendsto_atTop.mpr
    intro e he
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hl e he
    refine ⟨N,fun j hj => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact (hbound j t le_rfl).trans_lt (by
      simpa only [Real.dist_eq,sub_zero] using hN j hj)
  change AEMeasurable (fun w => J t w - S T n t w) P
  exact hJ.sub (hS T n t)
