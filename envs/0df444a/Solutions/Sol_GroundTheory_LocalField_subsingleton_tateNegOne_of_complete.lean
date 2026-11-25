-- Prove2me | solution 1 for GroundTheory.LocalField.subsingleton_tateNegOne_of_complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:01.360166+00:00
-- url     : https://prove2.me/submissions/afcd1e17-0802-4ca8-8d15-edb926f1edda

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Theorems.Thm_GroundTheory_LocalField_tateNorm_augMap
import Theorems.Thm_GroundTheory_LocalField_augmentation_eq_range
import Theorems.Thm_GroundTheory_LocalField_subsingleton_tateNegOne_iff
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_augMap_mem
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_subsingleton_tateNegOne_gr_iff
import Theorems.Thm_GroundTheory_LocalField_filtrationComplete_pi
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
    (hgr : ∀ n, Subsingleton (TateNegOne G (S.gr n))) : Subsingleton (TateNegOne G V) := by
  rw [subsingleton_tateNegOne_iff, augmentation_eq_range]
  intro x hx
  let f : (G → V) →* (tateNorm G V).ker := (augMap G V).codRestrict _ tateNorm_augMap
  let P : ℕ → Subgroup (G → V) := fun n => Subgroup.pi Set.univ fun _ : G => S.F n
  let E : ℕ → Subgroup (tateNorm G V).ker := fun n => (S.F n).subgroupOf (tateNorm G V).ker
  have key := map_eq_of_graded_surjective (F := P) (E := E)
    (fun a b hab m hm => (Subgroup.mem_pi _).mpr fun g _ =>
      S.antitone hab ((Subgroup.mem_pi _).mp hm g (Set.mem_univ g)))
    (fun a b hab y hy => Subgroup.mem_subgroupOf.mpr (S.antitone hab (Subgroup.mem_subgroupOf.mp hy)))
    (filtrationComplete_pi hc)
    (fun y hy => Subtype.ext (hs _ fun n => Subgroup.mem_subgroupOf.mp (hy n))) f tendsto_id 0
    (fun n _ m hm => Subgroup.mem_subgroupOf.mpr
      (S.augMap_mem fun g => (Subgroup.mem_pi _).mp hm g (Set.mem_univ g)))
    (fun n _ h hh => by
      have hh' : (h : V) ∈ S.F n := Subgroup.mem_subgroupOf.mp hh
      have hN : tateNorm G V h ∈ S.F (n + 1) := by
        rw [h.2]
        exact Subgroup.one_mem _
      obtain ⟨m, hm, hhm⟩ := (S.subsingleton_tateNegOne_gr_iff n).mp (hgr n) h hh' hN
      exact ⟨m, (Subgroup.mem_pi _).mpr fun g _ => hm g, Subgroup.mem_subgroupOf.mpr hhm⟩)
  have hx0 : (⟨x, MonoidHom.mem_ker.mpr hx⟩ : (tateNorm G V).ker) ∈ (P 0).map f := by
    rw [key]
    change _ ∈ E 0
    rw [Subgroup.mem_subgroupOf, h0]
    exact Subgroup.mem_top _
  obtain ⟨m, -, hm⟩ := hx0
  exact ⟨m, congrArg Subtype.val hm⟩
end GroundTheory.LocalField
