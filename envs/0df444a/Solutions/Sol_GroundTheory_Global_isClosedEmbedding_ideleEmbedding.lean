-- Prove2me | solution 1 for GroundTheory.Global.isClosedEmbedding_ideleEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:39:57.062796+00:00
-- url     : https://prove2.me/submissions/1fc2f760-1b60-46bf-a31a-e77670ed4009

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_isClosedEmbedding_adeleMap


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
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
open AdeleBaseChange
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {K L}
namespace GroundTheory.Global
theorem _root_.solution : IsClosedEmbedding (ideleEmbedding K L) :=
  haveI : T2Space (FiniteAdeleRing (𝓞 L) L) := inferInstanceAs (T2Space
    (Πʳ w : HeightOneSpectrum (𝓞 L), [w.adicCompletion L, w.adicCompletionIntegers L]))
  haveI : T2Space (InfiniteAdeleRing L) :=
    inferInstanceAs (T2Space ((w : NumberField.InfinitePlace L) → w.Completion))
  haveI : T2Space 𝔸[L] := inferInstanceAs (T2Space (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L))
  haveI : T2Space (FiniteAdeleRing (𝓞 K) K) := inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]))
  haveI : T2Space (InfiniteAdeleRing K) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace K) → v.Completion))
  haveI : T2Space 𝔸[K] := inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
  Topology.IsClosedEmbedding.units_map (f := (adeleMap K L).toMonoidHom) isClosedEmbedding_adeleMap
end GroundTheory.Global
