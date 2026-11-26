-- Prove2me | solution 2 for Kyprianou.Ch05.exercise54QuadrupleKernelUnfold
-- status  : ACCEPTED   (prove)
-- author  : @Cloud 
-- created : 2026-11-26T03:13:50.60655+00:00
-- url     : https://prove2.me/submissions/2beb7e59-6c00-4c8f-a68b-7557864c57e7

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_BivariateKilledSubordinator
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
attribute [instance] Classical.propDecidable
open Kyprianou.Ch05

theorem solution (U Pi : Measure (Real × Real)) (x : Real) (T S B A : Set Real) :
    bivariateQuadrupleKernel U Pi x T S B A =
      ∫⁻ pre : Real × Real,
    ∫⁻ jump : Real × Real,
      (if jump.1 ∈ T ∧ pre.1 ∈ S ∧
        x-pre.2 ∈ B ∧ pre.2+jump.2-x ∈ A ∧
        pre.2 ≤ x ∧ x < pre.2+jump.2
       then (1 : ENNReal) else 0) ∂Pi ∂U := rfl
