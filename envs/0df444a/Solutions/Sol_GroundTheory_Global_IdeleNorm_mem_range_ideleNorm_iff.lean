-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.mem_range_ideleNorm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:23.088362+00:00
-- url     : https://prove2.me/submissions/a1ad41d3-0d53-4574-8d74-345b8cac6a12

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Theorems.Thm_GroundTheory_Global_IdeleNorm_finiteProj_ideleNorm
import Theorems.Thm_GroundTheory_Global_IdeleNorm_infiniteProj_ideleNorm
import Theorems.Thm_GroundTheory_Global_IdeleNorm_eventually_finiteProj_mem
import Theorems.Thm_GroundTheory_Global_IdeleNorm_eventually_forall_placesOver
import Theorems.Thm_GroundTheory_Global_IdeleNorm_mem_range_ideleNorm

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
open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]
variable {L}
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution (x : IdeleGroup K) :
    x ∈ (ideleNorm K L).range ↔
      (∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range) ∧
      (∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range) ∧
      ∀ᶠ v in cofinite,
        IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v) := by
  refine ⟨?_, fun ⟨h1, h2, h3⟩ ↦ mem_range_ideleNorm x h1 h2 h3⟩
  rintro ⟨y, rfl⟩
  refine ⟨fun v ↦ ⟨_, (finiteProj_ideleNorm y v).symm⟩,
    fun v ↦ ⟨_, (infiniteProj_ideleNorm y v).symm⟩, ?_⟩
  refine (eventually_forall_placesOver K (eventually_finiteProj_mem y)).mono fun v hv ↦ ?_
  exact ⟨_, mem_integerUnitsOver.2 hv, (finiteProj_ideleNorm y v).symm⟩
end GroundTheory.Global.IdeleNorm
