-- Prove2me | solution 1 for IsDiscreteValuationRing.upperRamificationQuotientCompat_of_isSeparable_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/edadf74f-c207-51a9-aa8d-b89ea1b4a5c3

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
import Theorems.Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_upperRamificationQuotientCompat_of_isSeparable_residueField
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (H : Subgroup G) [H.Normal] :
    IsLocalRing.UpperRamificationQuotientCompat R G (FixedPoints.subring R H) H :=
  IsLocalRing.upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq fun n =>
    IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
      (R := R) (G := G) (H := H) n

end S_IsDiscreteValuationRing_upperRamificationQuotientCompat_of_isSeparable_residueField
end P2MW
export P2MW.S_IsDiscreteValuationRing_upperRamificationQuotientCompat_of_isSeparable_residueField (solution)
