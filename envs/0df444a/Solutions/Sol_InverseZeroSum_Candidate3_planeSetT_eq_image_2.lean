-- Prove2me | solution 2 for InverseZeroSum.Candidate3.planeSetT_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:32.773078+00:00
-- url     : https://prove2.me/submissions/69921b5c-4af4-43f3-af93-87ca1aa385b6

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planePointT_onPlane
public import Theorems.Thm_InverseZeroSum_Candidate3_planePointT_surjective_on
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution (p : PlaneIdx) :
    planeSetT p = Finset.univ.image (planePointT p) := by
  classical
  ext x
  constructor
  · intro hx
    have hon : onPlaneTB p x = true := (Finset.mem_filter.mp hx).2
    obtain ⟨q, hq⟩ := planePointT_surjective_on p x hon
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hq⟩
  · intro hx
    obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, planePointT_onPlane p q⟩
end InverseZeroSum.Candidate3
