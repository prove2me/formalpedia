-- Prove2me | solution 1 for GroundTheory.LocalField.subsingleton_tateZero_of_complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:05.421833+00:00
-- url     : https://prove2.me/submissions/55bde518-4bb6-439a-a7d7-a6316b846b29

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Theorems.Thm_GroundTheory_LocalField_mem_invariants
import Theorems.Thm_GroundTheory_LocalField_tateNorm_mem_invariants
import Theorems.Thm_GroundTheory_LocalField_subsingleton_tateZero_iff
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_tateNorm_mem
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_subsingleton_tateZero_gr_iff
import Theorems.Thm_GroundTheory_LocalField_map_eq_of_graded_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F

set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
variable {V : Type*} [CommGroup V]
variable {G : Type*} [Group G] [Fintype G] [MulDistribMulAction G V]
namespace GroundTheory.LocalField
theorem _root_.solution (S : StableFiltration G V) (h0 : S.F 0 = ⊤)
    (hc : FiltrationComplete S.F) (hs : FiltrationSeparated S.F)
    (hgr : ∀ n, Subsingleton (TateZero G (S.gr n))) : Subsingleton (TateZero G V) := by
  rw [subsingleton_tateZero_iff]
  intro x hx
  let f : V →* invariants G V := (tateNorm G V).codRestrict _ tateNorm_mem_invariants
  let E : ℕ → Subgroup (invariants G V) := fun n => (S.F n).subgroupOf (invariants G V)
  have key := map_eq_of_graded_surjective (F := S.F) (E := E) S.antitone
    (fun a b hab y hy => Subgroup.mem_subgroupOf.mpr (S.antitone hab (Subgroup.mem_subgroupOf.mp hy)))
    hc (fun y hy => Subtype.ext (hs _ fun n => Subgroup.mem_subgroupOf.mp (hy n))) f tendsto_id 0
    (fun n _ y hy => Subgroup.mem_subgroupOf.mpr (S.tateNorm_mem hy))
    (fun n _ h hh => by
      have hh' : (h : V) ∈ S.F n := Subgroup.mem_subgroupOf.mp hh
      obtain ⟨y, hy, hhy⟩ := (S.subsingleton_tateZero_gr_iff n).mp (hgr n) h hh' fun g => by
        rw [h.2 g, div_self']
        exact Subgroup.one_mem _
      exact ⟨y, hy, Subgroup.mem_subgroupOf.mpr hhy⟩)
  have hx0 : (⟨x, (mem_invariants G V).mpr hx⟩ : invariants G V) ∈ (S.F 0).map f := by
    rw [key]
    change _ ∈ E 0
    rw [Subgroup.mem_subgroupOf, h0]
    exact Subgroup.mem_top _
  obtain ⟨y, -, hy⟩ := hx0
  exact ⟨y, congrArg Subtype.val hy⟩
end GroundTheory.LocalField
