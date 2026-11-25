-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_cohTrivial_of_isZero_neg_two_of_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:45.979522+00:00
-- url     : https://prove2.me/submissions/5c974690-d5aa-46e1-962e-c57244e594b3

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
import Theorems.Thm_GroundTheory_GroupCoh_isZero_groupHomology_one_of_addEquiv
import Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_cohTrivial_of_sum_eq
import Theorems.Thm_GroundTheory_GroupCoh_exists_iso_free_of_isZero_groupHomology_one
import Theorems.Thm_GroundTheory_GroupCoh_exists_sum_eq_of_basis
import Theorems.Thm_GroundTheory_GroupCoh_free_asModule_of_iso_free
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_of_sum_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupHomology
universe u
variable {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
variable [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0)
    (h : IsZero (tateCohomology M (-2))) : TateAcyclic M ∧ CohTrivial M := by
  have h1 : IsZero (groupHomology M 1) := h.of_iso (tateNegTwoIsoH1 M).symm
  have h1' : IsZero (groupHomology (zmodRep p M hM) 1) :=
    isZero_groupHomology_one_of_addEquiv (AddEquiv.refl M.V) (fun _ _ => rfl) h1
  obtain ⟨ι, ⟨e⟩⟩ := exists_iso_free_of_isZero_groupHomology_one hG _ h1'
  have := free_asModule_of_iso_free e
  obtain ⟨φ, hφ⟩ := exists_sum_eq_of_basis (zmodRep p M hM) (Module.Free.chooseBasis _ _)
  refine ⟨tateAcyclic_of_sum_eq M
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M.V M.V _ _ M.hV2 M.hV2 ⟨φ, map_add φ⟩ ?_) hφ,
    cohTrivial_of_sum_eq M
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M.V M.V _ _ M.hV2 M.hV2 ⟨φ, map_add φ⟩ ?_) hφ⟩
  all_goals
    intro n x
    have hmod : M.hV2 = AddCommGroup.toIntModule M.V := Subsingleton.elim _ _
    rw [hmod]
    exact map_zsmul φ n x
end GroundTheory.GroupCoh
