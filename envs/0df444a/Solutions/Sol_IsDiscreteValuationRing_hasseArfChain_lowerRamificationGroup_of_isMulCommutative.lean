-- Prove2me | solution 1 for IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isMulCommutative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ade51941-7035-596e-a14e-1e1734d35327

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild
import Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient
import Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic
import Theorems.Thm_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring
import Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [IsMulCommutative G]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)] :
    RamificationChain.HasseArfChain (IsLocalRing.lowerRamificationGroup R G) := by

  refine IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient (R := R) (G := G) ?_
  intro H _ hcycH
  haveI : IsDiscreteValuationRing (FixedPoints.subring R H) := FixedPoints.isDiscreteValuationRing_subring
  obtain ⟨hf, hperf, hlo, hsep⟩ :=
    FixedPoints.faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring (R := R) (G := G) H
  haveI := hf
  haveI := hperf
  haveI := hlo
  haveI := hsep
  haveI : IsCyclic (G ⧸ H) := hcycH
  exact IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isCyclic
    (R := FixedPoints.subring R H) (G := G ⧸ H)

end S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative
end P2MW
export P2MW.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative (solution)
