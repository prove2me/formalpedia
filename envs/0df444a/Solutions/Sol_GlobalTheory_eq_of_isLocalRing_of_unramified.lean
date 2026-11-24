-- Prove2me | solution 1 for GlobalTheory.eq_of_isLocalRing_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:42.992159+00:00
-- url     : https://prove2.me/submissions/cd79c96d-afaa-46d1-93ff-6fcb69735343

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_P2M_GlobalTheory_isOpenImmersion_equalizer___of_unramified_d71f398b7582
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
theorem _root_.solution {X S Z : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] {R : CommRingCat.{u}} [IsLocalRing R]
    {a b : Spec R ⟶ X} (hab : a ≫ f = b ≫ f)
    (j : Z ⟶ Spec R) (hz : IsLocalRing.closedPoint R ∈ Set.range j) (hj : j ≫ a = j ≫ b) :
    a = b := by
  have := isOpenImmersion_equalizer_ι_of_unramified f hab
  refine eq_of_range_equalizer_ι_eq_univ f hab ?_
  have h := (IsLocalRing.closed_point_mem_iff (R := R)
    (U := (equalizer.ι a b).opensRange)).mp (range_subset_range_equalizer_ι j hj hz)
  exact congr(SetLike.coe $h)
end GlobalTheory
