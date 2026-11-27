-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.isOpen_ker_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:43.666251+00:00
-- url     : https://prove2.me/submissions/2320d5b4-de2f-4bec-9536-10ec6208d84d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_finiteLevel
import Theorems.Thm_GroundTheory_Global_IdeleGroup_exists_finiteLevel_le_ker

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
theorem _root_.solution (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) : IsOpen (χ.ker : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  obtain ⟨S, n, -, h0, hn⟩ := exists_finiteLevel_le_ker hH χ hχ
  refine Subgroup.isOpen_mono hn (isOpen_finiteLevel (S.finite_toSet.subset fun v hv ↦ ?_))
  by_contra hvS
  exact hv (h0 v hvS)
end GroundTheory.Global.IdeleGroup
