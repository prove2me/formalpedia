-- Prove2me | solution 1 for GroundTheory.Global.mem_finiteIntegralUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:46:29.352972+00:00
-- url     : https://prove2.me/submissions/2667cb40-6f64-4f03-bf53-03306893e9f5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open InfinitePlace
namespace GroundTheory.Global
theorem _root_.solution {x : (FiniteAdeleRing (𝓞 K) K)ˣ} :
    x ∈ finiteIntegralUnits K ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
        ((x⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
          v.adicCompletionIntegers K :=
  IdeleGroup.mem_standardOpenSubgroup K (x := (IdeleGroup.prodEquiv K).symm (1, x))
end GroundTheory.Global
