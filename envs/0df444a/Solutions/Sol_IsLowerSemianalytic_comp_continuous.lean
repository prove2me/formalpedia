-- Prove2me | solution 1 for IsLowerSemianalytic.comp_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:47.213809+00:00
-- url     : https://prove2.me/submissions/73341e20-6cf4-4f96-8741-67d56c162714

import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Theorems.Thm_MeasureTheory_AnalyticSet_preimage_of_continuous


set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X]
namespace IsLowerSemianalytic
theorem _root_.solution [PolishSpace X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : Y → ℝ≥0∞} (hf : IsLowerSemianalytic f)
    {g : X → Y} (hg : Continuous g) :
    IsLowerSemianalytic (f ∘ g) := by
  intro c
  have h : {x | (f ∘ g) x < c} = g ⁻¹' {y | f y < c} := rfl
  rw [h]
  exact (hf c).preimage_of_continuous hg
end IsLowerSemianalytic
