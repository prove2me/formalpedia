-- Prove2me | solution 1 for GlobalTheory.exists_triple_of_card_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:18.805587+00:00
-- url     : https://prove2.me/submissions/a0b7d0aa-d02a-431a-b679-2ee80632623c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdea
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open MvPolynomial DirectSum
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [LinearOrder ι] {t : Finset ι}
    (ht : t.card = 3) : ∃ i j l, i < j ∧ j < l ∧ t = {i, j, l} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 ht
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  all_goals first
    | exact ⟨a, b, c, by assumption, by assumption, rfl⟩
    | exact ⟨a, b, c, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨a, c, b, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨b, a, c, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨b, c, a, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨c, a, b, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨c, b, a, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | (exfalso; order)
end GlobalTheory
