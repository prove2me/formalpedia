-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.exists_finiteLevel_le_ker_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:29.465798+00:00
-- url     : https://prove2.me/submissions/25cdc1e9-e294-45cd-a503-259b9bd074ea

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Theorems.Thm_GroundTheory_Global_IdeleGroup_exists_finiteLevel_le_ker
import Theorems.Thm_GroundTheory_Global_Circle_noSmallSubgroups


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
theorem _root_.solution (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* Circle)
    (hχ : Continuous χ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ finiteLevel n ≤ χ.ker :=
  exists_finiteLevel_le_ker Circle.noSmallSubgroups χ hχ
end GroundTheory.Global.IdeleGroup
