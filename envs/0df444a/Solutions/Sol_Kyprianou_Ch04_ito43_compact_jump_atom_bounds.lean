-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_compact_jump_atom_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:43:02.585817+00:00
-- url     : https://prove2.me/submissions/aca9cb78-151a-4356-b988-dedca8337978

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_path_jump_kernel_energy_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_compact_taylor_global_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_cadlag_left_compact_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_integral_cutoff_difference
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_slice_derivative
import Theorems.Thm_Kyprianou_Ch04_exercise41CadlagPhysicalJumpsCountableV17
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Uniform bounds for all three spatial Taylor kernels at positive times. -/
theorem solution
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
    (H : NNReal) (M a : ℝ) (ha : 0 < a) (m : ℕ)
    (hcut : ∀ s ∈ Set.Icc (0 : ℝ) (H : ℝ),
      ∀ x ∈ Set.Icc (-M) M, ∀ y ∈ Set.Icc (-M) M,
        |(f (s,y)-f (s,x)-deriv (fun z : ℝ => f (s,z)) x*(y-x) -
          iteratedDeriv 2 (fun z : ℝ => f (s,z)) x*(y-x)^2/2) *
          (1-min 1 (max 0 (|y-x| *((m : ℝ)+1)-1)))| ≤ a*(y-x)^2)
    : ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ Set.Icc (0 : ℝ) (H : ℝ), 0 < s →
      ∀ x ∈ Set.Icc (-M) M, ∀ y ∈ Set.Icc (-M) M,
        |f (s,y)-f (s,x)-(y-x)*fderiv ℝ f (s,x) (0,1)| ≤ (C/2)*(y-x)^2 ∧
        |iteratedDeriv 2 (fun z : ℝ => f (s,z)) x*(y-x)^2/2| ≤ (C/2)*(y-x)^2 ∧
        |(f (s,y)-f (s,x)-(y-x)*fderiv ℝ f (s,x) (0,1) -
          iteratedDeriv 2 (fun z : ℝ => f (s,z)) x*(y-x)^2/2) *
          (1-min 1 (max 0 (|y-x| *((m : ℝ)+1)-1)))| ≤ a*(y-x)^2 := by
  have hfc (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (H : ℝ)) :
      ContDiff ℝ 2 (fun x : ℝ => f (s,x)) := by
    simpa only [Real.coe_toNNReal s hs.1] using hfSpaceC2 s.toNNReal
  have hgc := hfSpaceSecondContinuous.mono
    (show Set.Icc (0 : ℝ) (H : ℝ) ×ˢ Set.Icc (-M) M ⊆
      Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ) from
      fun z hz => ⟨hz.1.1,Set.mem_univ _⟩)
  obtain ⟨C,hC,hcurv,hrem⟩ := Kyprianou.Ch04.ito43_compact_taylor_global_bound
    f (H : ℝ) M hfc hgc
  refine ⟨C,hC,?_⟩
  intro t ht htpos x hx y hy
  rw [Kyprianou.Ch04.ito43_spatial_slice_derivative f hfJointC1 _ _ htpos]
  rw [mul_comm (y-x)]
  refine ⟨(hrem _ ht _ hx _ hy).trans_eq (by ring),?_,hcut _ ht _ hx _ hy⟩
  rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (y-x)),
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ C*(y-x)^2/2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcurv _ ht _ hx) (sq_nonneg _)) (by norm_num)
    _ = _ := by ring
