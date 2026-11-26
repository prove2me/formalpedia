-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_atomic_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:01:25.727187+00:00
-- url     : https://prove2.me/submissions/3f4688d8-cc54-41c8-baaa-aae88c48904d

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_exercise41CadlagPhysicalJumpsCountableV17
import Theorems.Thm_Kyprianou_Ch04_bvPathJumpMeasureAtomicV1
import Theorems.Thm_Kyprianou_Ch04_bvRestrictedDiracIntegralV1
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_slice_derivative
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
    ∀ m : ℕ,
    let K : NNReal → ℝ → ℝ → ℝ := fun s x z =>
      (f ((s : ℝ),x+z) - f ((s : ℝ),x) -
        deriv (fun y : ℝ => f ((s : ℝ),y)) x*z -
        iteratedDeriv 2 (fun y : ℝ => f ((s : ℝ),y)) x*z^2/2) *
      min 1 (max 0 (|z| * ((m : ℝ)+1)-1))
    let J : NNReal → Omega → ℝ := fun t omega =>
      let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
      (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
       (f (z.1,Xleft (Real.toNNReal z.1) omega + z.2) -
        f (z.1,Xleft (Real.toNNReal z.1) omega) -
        z.2 * fderiv ℝ f (z.1,Xleft (Real.toNNReal z.1) omega) (0,1) -
        iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2)
          * chi z.2 ∂(pathJumpMeasure X Xleft omega))
    ∀ᵐ w ∂P, ∀ t : NNReal, J t w =
      ∑' s : Set.Ioc (0 : NNReal) t, K s.1 (Xleft s.1 w) (X s.1 w-Xleft s.1 w) := by
  intro m K J0
  filter_upwards [hCad,hLeft] with w hc hl
  intro t
  classical
  let J : Set NNReal := {s | 0 < s ∧ X s w ≠ Xleft s w}
  let φ : J → ℝ × ℝ := fun s => ((s.1 : ℝ),X s.1 w-Xleft s.1 w)
  let B : Set (ℝ × ℝ) := Icc (0:ℝ) (t:ℝ) ×ˢ univ
  let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m:ℝ)+1)-1))
  let g : ℝ × ℝ → ℝ := fun z =>
    (f (z.1,Xleft (Real.toNNReal z.1) w+z.2) -
      f (z.1,Xleft (Real.toNNReal z.1) w) -
      z.2 * fderiv ℝ f (z.1,Xleft (Real.toNNReal z.1) w) (0,1) -
      iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) w)*z.2^2/2) *
      chi z.2
  have hJ := Kyprianou.Ch04.exercise41CadlagPhysicalJumpsCountableV17
    (fun s => X s w) (fun s => Xleft s w) (fun s => (hc s).1) hl
  letI : Countable J := hJ.to_subtype
  change (∫ z in B, g z ∂(pathJumpMeasure X Xleft w)) =
      ∑' s : Ioc (0:NNReal) t, K s.1 (Xleft s.1 w) (X s.1 w-Xleft s.1 w)
  rw [Kyprianou.Ch04.bvPathJumpMeasureAtomicV1 X Xleft w hJ]
  rw [Kyprianou.Ch04.bvRestrictedDiracIntegralV1 φ B
    (measurableSet_Icc.prod MeasurableSet.univ) g]
  let F : NNReal → ℝ := fun s => B.indicator g ((s:ℝ),X s w-Xleft s w)
  let G : NNReal → ℝ := fun s => K s (Xleft s w) (X s w-Xleft s w)
  change (∑' s : J, F s) = ∑' s : Ioc (0:NNReal) t, G s
  rw [tsum_subtype J F,tsum_subtype (Ioc (0:NNReal) t) G]
  apply tsum_congr
  intro s
  by_cases h : X s w = Xleft s w
  · simp [J,F,G,K,Set.indicator_apply,h]
  · by_cases hs : 0 < s
    · have hm : ((s:ℝ),X s w-Xleft s w) ∈ B ↔ s ≤ t := by
        change ((0:ℝ) ≤ (s:ℝ) ∧ (s:ℝ) ≤ (t:ℝ)) ∧
          X s w-Xleft s w ∈ (univ : Set ℝ) ↔ s ≤ t
        simp
      have hd := Kyprianou.Ch04.ito43_spatial_slice_derivative f hfJointC1
        (s:ℝ) (Xleft s w) (by exact_mod_cast hs)
      simp [J,F,G,B,Set.indicator_apply,h,hs,hm,g,K,chi,hd,mul_comm]
    · simp [J,F,G,Set.indicator_apply,hs]
