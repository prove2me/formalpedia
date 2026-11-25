-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.norm_mem_range_of_mem_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:04:13.816566+00:00
-- url     : https://prove2.me/submissions/a7f32c70-5d57-4636-be56-6a536cdf13af

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_units_eq_map_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_norm_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A)
variable {D} {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hax : ClassFieldAxiom G A) {S : OpenSubgroup G} (hSK : S ≤ K)
    (hLK : L ≤ K) (hu : (S : Subgroup G) ⊓ D.deg.ker ≤ L) {u : fixedModule A (S : Subgroup G)}
    (hu' : u ∈ D.units S) :
    norm A (K : Subgroup G) (S : Subgroup G) u ∈ (norm A (K : Subgroup G) (L : Subgroup G)).range := by
  set M : OpenSubgroup G := L ⊓ S with hMdef
  have hMS : M ≤ S := inf_le_right
  have hML : M ≤ L := inf_le_left
  have hMu : (S : Subgroup G) ⊓ D.deg.ker ≤ M := fun x hx => ⟨hu hx, hx.1⟩
  rw [D.units_eq_map_norm hax hMS hMu] at hu'
  obtain ⟨w, -, rfl⟩ := hu'
  rw [norm_norm (fun x hx => hMS hx) (fun x hx => hSK hx) w]
  exact ⟨norm A (L : Subgroup G) (M : Subgroup G) w,
    norm_norm (fun x hx => hML hx) (fun x hx => hLK hx) w⟩
end GroundTheory.LocalField.Abstract.ClassFieldData
