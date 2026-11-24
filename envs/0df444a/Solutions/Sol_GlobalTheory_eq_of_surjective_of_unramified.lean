-- Prove2me | solution 1 for GlobalTheory.eq_of_surjective_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:37:12.481867+00:00
-- url     : https://prove2.me/submissions/96aec05d-7723-4b87-878e-121e2938dae5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
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
    [FormallyUnramified f] [LocallyOfFiniteType f] {a b : T ⟶ X} (hab : a ≫ f = b ≫ f)
    (j : Z ⟶ T) [Surjective j] (hj : j ≫ a = j ≫ b) : a = b :=
  eq_of_range_equalizer_ι_eq_univ f hab (Set.eq_univ_of_univ_subset
    (j.surjective.range_eq ▸ range_subset_range_equalizer_ι j hj))
end GlobalTheory
