-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.conductorExponentAt_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:24.893882+00:00
-- url     : https://prove2.me/submissions/4e33859f-feef-4c0b-9d8c-1bd2ce75819c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_conductorExponent_eq_zero_iff


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
    (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) :
    conductorExponentAt χ v = 0 ↔
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤
        (χ.comp (finiteUnitsSingle v)).ker :=
  conductorExponent_eq_zero_iff v hH _ (hχ.comp (continuous_finiteUnitsSingle v))
end GroundTheory.Global.IdeleGroup
