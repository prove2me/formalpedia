-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_pathwise_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:57:34.307723+00:00
-- url     : https://prove2.me/submissions/4a2af539-2850-4c45-a318-66241d1cf257

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
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_right_continuous_bounded_path
import Theorems.Thm_Kyprianou_Ch04_ito43_cadlag_stopped_cutoff_kernel_uniform
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
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
    let B : ℕ → Omega → ℝ := fun n w =>
      sSup (Set.range (fun t : Set.Iic T => |E n t w|))
    ∀ᵐ w ∂P, Tendsto (fun n => B n w) atTop (nhds 0) ∧
      ∀ n t, t ≤ T → |E n t w| ≤ |B n w| := by
  intro T m E B
  let K : NNReal → ℝ → ℝ → ℝ := fun s x z =>
    (f ((s : ℝ),x+z) - f ((s : ℝ),x) -
      deriv (fun y : ℝ => f ((s : ℝ),y)) x*z -
      iteratedDeriv 2 (fun y : ℝ => f ((s : ℝ),y)) x*z^2/2) *
    min 1 (max 0 (|z| * ((m : ℝ)+1)-1))
  obtain ⟨hK,hzero⟩ := Kyprianou.Ch04.ito43_cutoff_taylor_kernel_data
    f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous m
  have hRep := Kyprianou.Ch04.ito43_cutoff_error_kernel_identity
    P X hCad Xleft hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T m
  have hB := Kyprianou.Ch04.ito43_cutoff_right_continuous_bounded_path
    P X hCad Xleft hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T m
  filter_upwards [hCad,hLeft,hRep,hB] with w hc hl hr hb
  have hG := Kyprianou.Ch04.ito43_cadlag_stopped_cutoff_kernel_uniform
    (fun s => X s w) (fun s => Xleft s w) hc hl K hK
    (1/((m:ℝ)+1)) (by positivity) hzero T
  have hbound (n : ℕ) (t : NNReal) (ht : t ≤ T) :
      |E n t w| ≤ B n w :=
    le_csSup (hb n).2 ⟨⟨t,ht⟩,rfl⟩
  have hnon (n : ℕ) : 0 ≤ B n w :=
    (abs_nonneg _).trans (hbound n 0 (by positivity))
  refine ⟨?_, fun n t ht => by rw [abs_of_nonneg (hnon n)]; exact hbound n t ht⟩
  apply Metric.tendsto_atTop.mpr
  intro e he
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hG (e/2) (by positivity))
  refine ⟨N,fun n hn => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hnon n)]
  have hh : B n w ≤ e/2 := by
    apply csSup_le
    · exact ⟨_,⟨⟨0,Set.mem_Iic.mpr (by positivity)⟩,rfl⟩⟩
    · rintro y ⟨t,rfl⟩
      have ht := hN n hn t.1 t.2
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t.1 (u k)
      have hEq : E n t.1 w =
          (∑' s : Set.Ioc (0 : NNReal) t.1,
            K s.1 (Xleft s.1 w) (X s.1 w-Xleft s.1 w)) -
          (∑ k ∈ Finset.range n, K (u k) (X (u k) w)
            (X (v (k+1)) w-X (v k) w)) := hr n t.1
      change |E n t.1 w| ≤ e/2
      rw [hEq,abs_sub_comm]
      exact ht.le
  linarith
