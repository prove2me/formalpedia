-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.norm_apply_le_norm_homeomorphMixedSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:07.969039+00:00
-- url     : https://prove2.me/submissions/f3b34bf0-a9ef-4f0a-8284-ad7991a35faa

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
import Theorems.Thm_GroundTheory_Global_homeomorphMixedSpace_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
open scoped Classical
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    ‖x w‖ ≤ ‖GroundTheory.Global.homeomorphMixedSpace K x‖ := by
  rw [GroundTheory.Global.homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  by_cases hw : w.IsReal
  · calc ‖x w‖ = ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x w)‖ :=
          ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
            (map_zero _) _).symm
      _ ≤ ‖fun v : {w : InfinitePlace K // w.IsReal} =>
            InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)‖ :=
          norm_le_pi_norm (fun v : {w : InfinitePlace K // w.IsReal} =>
            InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)) ⟨w, hw⟩
      _ ≤ _ := by rw [Prod.norm_def]; exact le_max_left _ _
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hw
    calc ‖x w‖ = ‖InfinitePlace.Completion.extensionEmbedding w (x w)‖ :=
          ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
            (map_zero _) _).symm
      _ ≤ ‖fun v : {w : InfinitePlace K // w.IsComplex} =>
            InfinitePlace.Completion.extensionEmbedding v.1 (x v)‖ :=
          norm_le_pi_norm (fun v : {w : InfinitePlace K // w.IsComplex} =>
            InfinitePlace.Completion.extensionEmbedding v.1 (x v)) ⟨w, hc⟩
      _ ≤ _ := by rw [Prod.norm_def]; exact le_max_right _ _
end GroundTheory.Automorphic.Reduction
