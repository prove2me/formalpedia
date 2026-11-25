-- Prove2me | solution 1 for GroundTheory.Global.range_powMonoidHom_subgroupOf_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:21.965154+00:00
-- url     : https://prove2.me/submissions/2c703d07-2f0a-4680-a5c3-3ee1cff333f9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_ExistenceTheorem_PowerIndex
import Theorems.Thm_GroundTheory_Global_mem_torsion_of_pow_mem_torsion

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
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.subgroupOf (CommGroup.torsion G) =
      (powMonoidHom n : CommGroup.torsion G →* CommGroup.torsion G).range := by
  ext ⟨t, ht⟩
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    rw [powMonoidHom_apply] at hx
    refine ⟨⟨x, mem_torsion_of_pow_mem_torsion hn ?_⟩, Subtype.ext ?_⟩
    · rw [hx]
      exact ht
    · exact hx
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩
end GroundTheory.Global
