-- Prove2me | solution 1 for NOF.isMultidimCorner_forget_of_isForbiddenPattern
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:13:36.833545+00:00
-- url     : https://prove2.me/submissions/354e0d19-2edf-407e-94ad-443c4f107335

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Definitions.Def_ChandraFurstLipton_MultidimCorners

set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} {a : ι → ι → G} {v : ι → G}
variable [Fintype ι] [AddCommGroup G]
variable [DecidableEq ι]
namespace NOF
theorem _root_.solution (a : ι → ι → G) (h : IsForbiddenPattern a)
    (hS : ∀ i, ∑ j, a i j = 0) (i : ι) :
    IsMultidimCorner (fun j ↦ forget i (a j)) (forget i (a i)) := by
    rw [IsForbiddenPattern] at h
    obtain ⟨v, hv⟩ := h
    refine ⟨fun k l ↦ ?_, fun k l hneq ↦ ?_⟩
    · rw [← sub_eq_zero]
      calc
        ∑ j : {j // j ≠ i}, a k j - ∑ j : { j // j ≠ i }, a l j
          = ∑ j : {j // j ≠ i}, (a k j - a l j) := by rw [Finset.sum_sub_distrib]
        _ = ∑ j ∈ {i}ᶜ, (a k j - a l j) := (Finset.sum_subtype _ (by simp) (a k - a l)).symm
        _ = ∑ j ∈ {i}ᶜ, (a k j - a l j) + (a k i - a l i) := by simp [hv k.2, hv l.2]
        _ = ∑ j : ι, (a k j - a l j) := by rw [← Fintype.sum_eq_sum_compl_add]
        _ = 0 := by rw [Finset.sum_sub_distrib, sub_eq_zero, hS k, hS l]
    · rw [forget, forget, hv, hv l.2.symm]
      aesop
end NOF
