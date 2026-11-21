-- Prove2me | solution 1 for NewtonianLipschitz.diagonalParameter_mem_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:39:44.029932+00:00
-- url     : https://prove2.me/submissions/9962a4aa-e8c5-4f49-97f4-658361f3c748

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz


theorem solution
    (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    diagonalParameter u v ∈ Set.Icc (0 : ℝ) 1 := by
  have h : 0 ≤ (u ^ 2 + v ^ 2) / 2 := by positivity
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  have hu := mul_nonneg hu0 (sub_nonneg.mpr hu1)
  have hv := mul_nonneg hv0 (sub_nonneg.mpr hv1)
  unfold diagonalParameter
  nlinarith [Real.sq_sqrt h, Real.sqrt_nonneg ((u ^ 2 + v ^ 2) / 2)]
