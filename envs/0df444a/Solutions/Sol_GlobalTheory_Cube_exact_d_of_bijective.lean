-- Prove2me | solution 1 for GlobalTheory.Cube.exact_d_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:42.817219+00:00
-- url     : https://prove2.me/submissions/a12ee608-1d8f-4702-9f92-d88378442809

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_Cube_eq_zero_of_d_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
open GlobalTheory.Cube
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory.Cube
theorem _root_.solution (A : Cube.{v} ι R) (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → Function.Bijective (res A (Finset.subset_insert i s))) (p : ℕ) :
    Function.Exact (d A p) (d A (p + 1)) := by
  intro x
  refine ⟨fun hx => ?_, by rintro ⟨y, rfl⟩; exact d_d A p y⟩
  have hy : ∀ s : Finset ι, ∃ y : A.obj s, (i ∈ s → y = 0) ∧ (i ∉ s →
      res A (Finset.subset_insert i s) y =
        cubeSign (insert i s) i • extend A (p + 1) x (insert i s)) := by
    intro s
    by_cases hs : i ∈ s
    · exact ⟨0, fun _ => rfl, fun h => absurd hs h⟩
    · obtain ⟨y, hy⟩ := (hA s hs).2 (cubeSign (insert i s) i • extend A (p + 1) x (insert i s))
      exact ⟨y, fun h => absurd h hs, fun _ => hy⟩
  choose y hy0 hy1 using hy
  refine ⟨fun s => y s.1, (sub_eq_zero.1 ?_)⟩
  refine eq_zero_of_d_eq_zero A i (fun s hs => (hA s hs).1) _ (by rw [map_sub, d_d, hx, sub_zero])
    ?_
  rintro ⟨t, ht⟩ hi
  obtain ⟨s, hs, rfl⟩ : ∃ s, i ∉ s ∧ t = insert i s :=
    ⟨t.erase i, by simp, (Finset.insert_erase hi).symm⟩
  rw [Pi.sub_apply, d_apply_eq_totalD A _ y (fun _ => rfl), totalD_apply, Finset.sum_eq_single i,
    res_congr A _ (Finset.erase_insert hs) _ (Finset.subset_insert i s), hy1 s hs,
    cubeSign_smul_smul, extend_apply_of_eq A x ht, sub_self]
  · intro j _ hji
    rw [hy0 _ (by simp [hji.symm]), map_zero, smul_zero]
  · simp
end GlobalTheory.Cube
