-- Prove2me | solution 1 for GroundTheory.Global.index_range_powMonoidHom_eq_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:40.638864+00:00
-- url     : https://prove2.me/submissions/99e0993e-2190-44c2-b811-ea7840f7a9ff

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_ExistenceTheorem_PowerIndex
import Theorems.Thm_GroundTheory_Global_range_powMonoidHom_subgroupOf_torsion
import Theorems.Thm_GroundTheory_Global_range_powMonoidHom_sup_torsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Module
noncomputable section
variable {G : Type*} [CommGroup G]
namespace GroundTheory.Global
theorem _root_.solution [Group.FG G] {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.index =
      n ^ finrank ℤ (Additive (G ⧸ CommGroup.torsion G)) *
        (powMonoidHom n : CommGroup.torsion G →* CommGroup.torsion G).range.index := by
  set T := CommGroup.torsion G
  set N := (powMonoidHom n : G →* G).range
  have hQ : (powMonoidHom n : G ⧸ T →* G ⧸ T).range.index =
      n ^ finrank ℤ (Additive (G ⧸ T)) :=
    AddSubgroup.index_range_nsmul (Additive (G ⧸ T)) n
  have hsup : (N ⊔ T).index = n ^ finrank ℤ (Additive (G ⧸ T)) := by
    rw [range_powMonoidHom_sup_torsion, Subgroup.index_comap_of_surjective _
      (QuotientGroup.mk'_surjective T), hQ]
  have hrel : N.relIndex T = (powMonoidHom n : T →* T).range.index := by
    rw [Subgroup.relIndex, range_powMonoidHom_subgroupOf_torsion hn]
  rw [← Subgroup.relIndex_mul_index (le_sup_left : N ≤ N ⊔ T), Subgroup.relIndex_sup_left, hrel,
    hsup, mul_comm]
end GroundTheory.Global
