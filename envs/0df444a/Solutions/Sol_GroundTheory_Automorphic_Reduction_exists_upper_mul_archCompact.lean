-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.exists_upper_mul_archCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:48.486333+00:00
-- url     : https://prove2.me/submissions/736bef50-0c47-4ffc-acd2-b71eabfe546c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_upper_mul_of_ringEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (w : InfinitePlace K) (h : GL (Fin n) w.Completion) :
    ∃ b : GL (Fin n) w.Completion, (b : Matrix (Fin n) (Fin n) w.Completion).IsUpperTriangular ∧
      ∃ k ∈ archCompact w, h = b * k := by
  by_cases hw : w.IsReal
  · exact exists_upper_mul_of_ringEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (fun x => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) x) h
  · have hc := InfinitePlace.not_isReal_iff_isComplex.1 hw
    exact exists_upper_mul_of_ringEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc)
      (fun x => (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) x) h
end GroundTheory.Automorphic.Reduction
