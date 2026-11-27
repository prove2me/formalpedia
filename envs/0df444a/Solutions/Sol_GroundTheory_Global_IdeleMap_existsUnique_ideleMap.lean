-- Prove2me | solution 1 for GroundTheory.Global.IdeleMap.existsUnique_ideleMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:35.173148+00:00
-- url     : https://prove2.me/submissions/6ba3bbdf-569d-4d7d-bd79-33c6ea191343

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_Abstract
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_AbstractUnique
import Theorems.Thm_GroundTheory_Global_IdeleMap_eq_ideleMap
import Theorems.Thm_GroundTheory_Global_IdeleMap_ideleMap_comp_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleMap_ideleMap_comp_infiniteEmbedding


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
  [TopologicalSpace G] [DiscreteTopology G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
  (hφ : ∀ᶠ v in cofinite,
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)
include hφ
namespace GroundTheory.Global.IdeleMap
theorem _root_.solution (hφc : ∀ v, Continuous (φ v))
    (hφinfc : ∀ w, Continuous (φinf w)) :
    ∃! ψ : IdeleGroup K →* G, Continuous ψ ∧ (∀ v, ψ.comp (finiteEmbedding v) = φ v) ∧
      ∀ w, ψ.comp (infiniteEmbedding w) = φinf w :=
  ⟨ideleMap φ φinf hφ, ⟨continuous_ideleMap φ φinf hφ hφc hφinfc,
      ideleMap_comp_finiteEmbedding φ φinf hφ, ideleMap_comp_infiniteEmbedding φ φinf hφ⟩,
    fun _ hψ ↦ eq_ideleMap φ φinf hφ hφc hφinfc hψ.1 hψ.2.1 hψ.2.2⟩
end GroundTheory.Global.IdeleMap
