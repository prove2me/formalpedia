-- Prove2me | solution 1 for IsLowerSemianalytic.const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:57.960678+00:00
-- url     : https://prove2.me/submissions/b0e33c05-e0e4-4457-8203-6ee1e7d7ca6b

import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra

set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X]
namespace IsLowerSemianalytic
theorem _root_.solution [PolishSpace X] (c : ℝ≥0∞) :
    IsLowerSemianalytic (fun _ : X => c) := by
  intro d
  by_cases hcd : c < d
  · have h : {x : X | (fun _ : X => c) x < d} = univ :=
      eq_univ_of_forall fun _ => hcd
    rw [h]
    exact isClosed_univ.analyticSet
  · have h : {x : X | (fun _ : X => c) x < d} = ∅ := by
      ext x
      simp [hcd]
    rw [h]
    exact analyticSet_empty
end IsLowerSemianalytic
