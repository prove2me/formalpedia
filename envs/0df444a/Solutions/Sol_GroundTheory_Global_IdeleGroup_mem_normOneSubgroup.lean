-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.mem_normOneSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:07:26.253554+00:00
-- url     : https://prove2.me/submissions/dbeb8cc5-1843-49df-8b41-258971a7bab0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms

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
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution {x : IdeleGroup K} :
    x ∈ normOneSubgroup K ↔ (ideleModule K x : ℝ) = 1 := by
  rw [normOneSubgroup, MonoidHom.mem_ker]
  exact ⟨fun h ↦ by rw [h, Positive.val_one], fun h ↦ Subtype.ext (h.trans Positive.val_one.symm)⟩
end GroundTheory.Global.IdeleGroup
