-- Prove2me | solution 1 for InverseZeroSum.Candidate3.pair_planes_coverT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:19.88492+00:00
-- url     : https://prove2.me/submissions/7d26eb4d-0104-4f7d-890b-61a3b150f1e8

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_planeValueT_sub
public import Theorems.Thm_InverseZeroSum_Candidate3_relative_plane_directionT
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution (x y z : F3T) (hxy : x ≠ y) :
    ∃ p : PlaneIdx,
      onPlaneTB p x = true ∧ onPlaneTB p y = true ∧ onPlaneTB p z = true := by
  have hdiff : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  obtain ⟨n, hnyx, hnzx⟩ :=
    relative_plane_directionT (y - x) (z - x) hdiff
  have hny : planeValueT n y = planeValueT n x := by
    have hsub := planeValueT_sub n y x
    rw [hsub] at hnyx
    exact sub_eq_zero.mp hnyx
  have hnz : planeValueT n z = planeValueT n x := by
    have hsub := planeValueT_sub n z x
    rw [hsub] at hnzx
    exact sub_eq_zero.mp hnzx
  refine ⟨(n, planeValueT n x), ?_⟩
  simp [onPlaneTB, hny, hnz]
end InverseZeroSum.Candidate3
