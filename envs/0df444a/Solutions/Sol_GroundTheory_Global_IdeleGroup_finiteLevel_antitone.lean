-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.finiteLevel_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:07:20.180407+00:00
-- url     : https://prove2.me/submissions/35c22e88-5d29-4e98-a54d-7054443c473c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_finiteLevel
import Theorems.Thm_GroundTheory_Global_unitsLevel_antitone


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution {m n : HeightOneSpectrum (𝓞 K) → ℕ} (h : m ≤ n) :
    finiteLevel n ≤ finiteLevel m := fun _ hx ↦
  mem_finiteLevel.2 fun v ↦ unitsLevel_antitone v (h v) (mem_finiteLevel.1 hx v)
end GroundTheory.Global.IdeleGroup
