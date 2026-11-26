-- Prove2me | solution 1 for IsLowerSemianalytic.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:44.429194+00:00
-- url     : https://prove2.me/submissions/76430bf7-0589-4937-bd07-c0b1b1a6725a

import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Theorems.Thm_P2M_MeasureTheory_AnalyticSet_inter__f59a23aaf291


set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X]
namespace IsLowerSemianalytic
theorem _root_.solution [T2Space X] {f g : X → ℝ≥0∞}
    (hf : IsLowerSemianalytic f) (hg : IsLowerSemianalytic g) :
    IsLowerSemianalytic (fun x => f x + g x) := by
  intro c
  show AnalyticSet {x | f x + g x < c}
  have hdecomp : {x | f x + g x < c}
      = ⋃ q : ℚ, ({x | f x < (Real.toNNReal q : ℝ≥0∞)}
          ∩ {x | g x < c - (Real.toNNReal q : ℝ≥0∞)}) := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp
        (lt_tsub_iff_right.mpr h)
      exact ⟨q, hq1, lt_tsub_iff_left.mpr (lt_tsub_iff_right.mp hq2)⟩
    · rintro ⟨q, hq1, hq2⟩
      exact lt_trans (ENNReal.add_lt_add_right (ne_top_of_lt hq2) hq1)
        (lt_tsub_iff_left.mp hq2)
  rw [hdecomp]
  exact AnalyticSet.iUnion fun q => (hf _).inter' (hg _)
end IsLowerSemianalytic
