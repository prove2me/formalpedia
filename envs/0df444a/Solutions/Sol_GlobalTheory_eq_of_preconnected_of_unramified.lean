-- Prove2me | solution 1 for GlobalTheory.eq_of_preconnected_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:57.399312+00:00
-- url     : https://prove2.me/submissions/4a0a5182-23b6-4f0c-abb2-67bf65db0c1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_P2M_GlobalTheory_isOpenImmersion_equalizer___of_unramified_d71f398b7582
import Theorems.Thm_P2M_GlobalTheory_isClosedImmersion_equalizer___of_isSeparated_bdcf708e7a7d
import Theorems.Thm_P2M_GlobalTheory_range_subset_range_equalizer___aeb7241b0453
import Theorems.Thm_P2M_GlobalTheory_eq_of_range_equalizer___eq_univ_5724cbc41fd4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X S T Z : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f] [PreconnectedSpace T]
    {a b : T ⟶ X} (hab : a ≫ f = b ≫ f)
    (j : Z ⟶ T) [Nonempty Z] (hj : j ≫ a = j ≫ b) : a = b := by
  have := isOpenImmersion_equalizer_ι_of_unramified f hab
  have := isClosedImmersion_equalizer_ι_of_isSeparated f hab
  refine eq_of_range_equalizer_ι_eq_univ f hab (IsClopen.eq_univ
    ⟨(equalizer.ι a b).isClosedEmbedding.isClosed_range,
      (equalizer.ι a b).isOpenEmbedding.isOpen_range⟩ ?_)
  exact (Set.range_nonempty j).mono (range_subset_range_equalizer_ι j hj)
end GlobalTheory
