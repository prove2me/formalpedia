-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_small_tail_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:40:50.536936+00:00
-- url     : https://prove2.me/submissions/0cb6caf1-5ebc-4778-b02b-c80c083fecc3

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_small_cutoff_sum
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_small_tail_jump_pathwise
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_small_tail_grid_pathwise
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_combined_error_bound
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Choose a common compact cutoff and combine jump and grid inequalities. -/
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
    ∀ (T H : NNReal), T ≤ H → ∀ (M a : ℝ), 0 < a →
      ∃ m : ℕ, ∀ omega : Omega,
        IsCadlag (fun s : NNReal => X s omega) →
        (∀ s : NNReal, 0 < s → Tendsto (fun r => X r omega)
          (nhdsWithin s (Set.Iio s)) (nhds (Xleft s omega))) →
        (∀ s : NNReal, s ≤ H → |X s omega| ≤ M) →
        Summable (fun s : Set.Ioc (0 : NNReal) H => (X s omega-Xleft s omega)^2) →
        ∀ (n : ℕ) (t : NNReal), t ≤ T →
          let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
          let v : ℕ → NNReal := fun k => min t (u k)
          let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
          |((∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
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
      iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * (X (v (k+1)) omega - X (v k) omega)^2 / 2))) - ((∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
       (f (z.1,Xleft (Real.toNNReal z.1) omega + z.2) -
        f (z.1,Xleft (Real.toNNReal z.1) omega) -
        z.2 * fderiv ℝ f (z.1,Xleft (Real.toNNReal z.1) omega) (0,1) -
        iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2)
          * chi z.2 ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
       let dx := X (v (k+1)) omega - X (v k) omega
       (f ((v k : ℝ),X (v (k+1)) omega) - f ((v k : ℝ),X (v k) omega) -
        deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx -
        iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx^2 / 2)
          * chi dx))| ≤
            a*((∑ k ∈ Finset.range n, (X (v (k+1)) omega-X (v k) omega)^2) +
              (∑' s : Set.Ioc (0 : NNReal) H, (X s omega-Xleft s omega)^2)) := by
  intro T H hTH M a ha
  have hfc (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (H : ℝ)) :
      ContDiff ℝ 2 (fun x : ℝ => f (s,x)) := by
    simpa only [Real.coe_toNNReal s hs.1] using hfSpaceC2 s.toNNReal
  have hgc := hfSpaceSecondContinuous.mono
    (show Set.Icc (0 : ℝ) (H : ℝ) ×ˢ Set.Icc (-M) M ⊆
      Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ) from
      fun z hz => ⟨hz.1.1,Set.mem_univ _⟩)
  obtain ⟨m,hm⟩ := Kyprianou.Ch04.ito43_spatial_small_cutoff_sum f (H : ℝ) M hfc hgc a ha
  have hcut (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (H : ℝ))
      (x : ℝ) (hx : x ∈ Set.Icc (-M) M) (y : ℝ) (hy : y ∈ Set.Icc (-M) M) :
      |(f (s,y)-f (s,x)-deriv (fun z : ℝ => f (s,z)) x*(y-x) -
          iteratedDeriv 2 (fun z : ℝ => f (s,z)) x*(y-x)^2/2) *
          (1-min 1 (max 0 (|y-x| *((m : ℝ)+1)-1)))| ≤ a*(y-x)^2 := by
    simpa only [Finset.range_one,Finset.sum_singleton] using
      hm 1 (fun _ => s) (fun _ => x) (fun _ => y) (fun _ _ => ⟨hs,hx,hy⟩)
  refine ⟨m,?_⟩
  intro omega hcad hl hbounded hE n t ht u v chi
  have hj := Kyprianou.Ch04.ito43_spatial_small_tail_jump_pathwise P X hLevy triplet
    hTriplet Xleft hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous H M a ha m hcut
    omega hbounded hcad hl hE t (ht.trans hTH)
  have hg := Kyprianou.Ch04.ito43_spatial_small_tail_grid_pathwise P X hLevy triplet
    hTriplet Xleft hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous H M a ha m hcut
    omega hbounded T hTH n t ht
  dsimp only at hj hg ⊢
  exact Kyprianou.Ch04.ito43_cutoff_combined_error_bound _ _ _ _ _ _ _ _ _ hj hg
