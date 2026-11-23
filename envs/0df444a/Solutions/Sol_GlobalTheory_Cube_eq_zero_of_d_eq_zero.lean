-- Prove2me | solution 1 for GlobalTheory.Cube.eq_zero_of_d_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:11.837255+00:00
-- url     : https://prove2.me/submissions/1862180e-8c77-45cb-ad21-01bd76fe1f7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_Cube_extend_apply_of_ne

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
theorem _root_.solution (A : Cube.{v} ι R) (i : ι) {p : ℕ}
    (hA : ∀ s : Finset ι, i ∉ s → Function.Injective (res A (Finset.subset_insert i s)))
    (x : Term A p) (hx : d A p x = 0) (h0 : ∀ s : {s : Finset ι // s.card = p}, i ∈ s.1 → x s = 0) :
    x = 0 := by
  ext s
  by_cases hs : i ∈ s.1
  · exact h0 s hs
  have h := congrFun hx ⟨insert i s.1, by rw [Finset.card_insert_of_notMem hs, s.2]⟩
  rw [d_apply_extend, Finset.sum_eq_single i, Pi.zero_apply, cubeSign_smul_eq_zero,
    res_congr A _ (Finset.erase_insert hs) _ (Finset.subset_insert i s.1),
    extend_apply_of_eq A x s.2] at h
  · exact (map_eq_zero_iff _ (hA s.1 hs)).1 h
  · intro j _ hji
    by_cases hc : ((insert i s.1).erase j).card = p
    · rw [extend_apply_of_eq A x hc, h0 _ (by simp [hji.symm]), map_zero, smul_zero]
    · rw [extend_apply_of_ne A x hc, map_zero, smul_zero]
  · simp
end GlobalTheory.Cube
