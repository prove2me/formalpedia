-- Prove2me | solution 1 for GroundTheory.Global.IdeleMap.continuousIdeleMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:39:55.019886+00:00
-- url     : https://prove2.me/submissions/857d3501-e48f-499a-9538-9e747d826ea4

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
variable [TopologicalSpace G] [DiscreteTopology G]
namespace GroundTheory.Global.IdeleMap
theorem _root_.solution (hφc : ∀ v, Continuous (φ v))
    (hφinfc : ∀ w, Continuous (φinf w)) (x : IdeleGroup K) :
    continuousIdeleMap φ φinf hφ hφc hφinfc x = ideleMap φ φinf hφ x :=
  rfl
end GroundTheory.Global.IdeleMap
