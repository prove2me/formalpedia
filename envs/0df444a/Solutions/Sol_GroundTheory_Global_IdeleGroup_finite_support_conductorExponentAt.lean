-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.finite_support_conductorExponentAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:25:39.726539+00:00
-- url     : https://prove2.me/submissions/3e35eea6-17ba-470d-a728-e127874aabc8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Theorems.Thm_GroundTheory_Global_IdeleGroup_exists_finiteLevel_le_ker
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteLevel_le_ker_iff

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
variable {H : Type*} [Group H] [TopologicalSpace H]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (hH : NoSmallSubgroups H)
    (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (hχ : Continuous χ) :
    (support (conductorExponentAt χ)).Finite := by
  obtain ⟨S, n, -, h0, hker⟩ := exists_finiteLevel_le_ker hH χ hχ
  have h := (finiteLevel_le_ker_iff hH χ hχ n).1 hker
  refine S.finite_toSet.subset fun v hv ↦ ?_
  by_contra hvS
  exact hv (Nat.eq_zero_of_le_zero ((h v).trans (h0 v hvS).le))
end GroundTheory.Global.IdeleGroup
