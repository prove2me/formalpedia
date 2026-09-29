-- Prove2me | solution 1 for IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/156870f5-486c-5ea3-b96f-620141af732b

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Theorems.Thm_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top
import Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top
p2m_attr_erase "instance" "FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {A : Type*} [CommSemiring A] [Algebra A R]
    (hA : ∀ (σ : G) (a : A), σ • algebraMap A R a = algebraMap A R a)
    {H : Subgroup G} [H.Normal] [Fintype H] [IsDiscreteValuationRing (FixedPoints.subring R H)]
    {x : R} (hx : Algebra.adjoin A {x} = ⊤)
    {y : R} (hy : y ∈ FixedPoints.subring R H)
    (hy' : ∀ z ∈ FixedPoints.subring R H, z ∈ Algebra.adjoin A {y})
    (he : ∀ z : FixedPoints.subring R H,
      IsDiscreteValuationRing.addVal R (z : R) =
        (IsLocalRing.lowerRamificationCard R H 0 : ℕ∞) *
          IsDiscreteValuationRing.addVal (FixedPoints.subring R H) z)
    (n : ℕ) :
    (IsLocalRing.lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
      IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H)
        ⌈IsLocalRing.herbrandPhi R H (n : ℚ)⌉₊ :=
  IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
    (IsDiscreteValuationRing.iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top
      hA hx hy hy')
    he n

end S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top
end P2MW
export P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top (solution)
