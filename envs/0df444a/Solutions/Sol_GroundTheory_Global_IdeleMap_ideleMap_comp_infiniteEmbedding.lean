-- Prove2me | solution 1 for GroundTheory.Global.IdeleMap.ideleMap_comp_infiniteEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:28:13.605169+00:00
-- url     : https://prove2.me/submissions/ee96e5b4-9b41-43de-b8a5-dfe6e2552c56

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_Adele_IdeleBasis
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_Abstract

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
open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleMap
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
variable (hφ : ∀ᶠ v in cofinite,
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)
namespace GroundTheory.Global.IdeleMap
theorem _root_.solution (w : InfinitePlace K) :
    (ideleMap φ φinf hφ).comp (infiniteEmbedding w) = φinf w :=
  MonoidHom.ext (ideleMap_infiniteEmbedding φ φinf hφ w)
end GroundTheory.Global.IdeleMap
