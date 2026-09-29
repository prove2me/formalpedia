-- Prove2me | solution 1 for ModularCurve.finrank_parabolicHoms_gamma0_le_two_mul_genusFormula
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a130281b-311b-5e9a-8bdb-b98f5bf0c7ab

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
import Theorems.Thm_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one
import Theorems.Thm_ModularCurve_two_mul_card_orbitRelQuotient_zpowers_S_gamma0_eq
import Theorems.Thm_ModularCurve_three_mul_card_orbitRelQuotient_zpowers_S_mul_T_gamma0_eq
import Theorems.Thm_ModularCurve_natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_twelve_mul_genusFormula
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_parabolicHoms_gamma0_le_two_mul_genusFormula
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one"

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (N : ℕ) [NeZero N] (K : Type) [Field K] [CharZero K] :
    (Module.finrank K (ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K) : ℚ)
      ≤ 2 * ModularCurve.genusFormula N := by
  have hneg : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp
  have hD := ModularCurve.Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
    (CongruenceSubgroup.Gamma0 N) hneg K
  have hH := Matrix.SpecialLinearGroup.finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one
    (CongruenceSubgroup.Gamma0 N) hneg K two_ne_zero three_ne_zero
  have hS := ModularCurve.two_mul_card_orbitRelQuotient_zpowers_S_gamma0_eq N
  have hST := ModularCurve.three_mul_card_orbitRelQuotient_zpowers_S_mul_T_gamma0_eq N
  rw [ModularCurve.natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount N] at hD
  rw [ModularCurve.Gamma0_index N] at hH
  have hG := ModularCurve.twelve_mul_genusFormula N

  have hD' : (Module.finrank K (ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K) : ℚ)
      + (ModularCurve.cuspCount N : ℚ)
      ≤ (Module.finrank K (Additive (CongruenceSubgroup.Gamma0 N) →+ K) : ℚ) + 1 := by exact_mod_cast hD
  have hH' : (Module.finrank K (Additive (CongruenceSubgroup.Gamma0 N) →+ K) : ℚ)
      + (Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.S)
          (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)) : ℚ)
      + (Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))
          (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)) : ℚ)
      ≤ (ModularCurve.dedekindPsi N : ℚ) + 1 := by exact_mod_cast hH
  have hS' : 2 * (Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.S)
          (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)) : ℚ)
      = (ModularCurve.dedekindPsi N : ℚ) + (ModularCurve.nuTwo N : ℚ) := by exact_mod_cast hS
  have hST' : 3 * (Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))
          (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)) : ℚ)
      = (ModularCurve.dedekindPsi N : ℚ) + 2 * (ModularCurve.nuThree N : ℚ) := by exact_mod_cast hST
  linarith

#print axioms solution

end S_ModularCurve_finrank_parabolicHoms_gamma0_le_two_mul_genusFormula
end P2MW
export P2MW.S_ModularCurve_finrank_parabolicHoms_gamma0_le_two_mul_genusFormula (solution)
