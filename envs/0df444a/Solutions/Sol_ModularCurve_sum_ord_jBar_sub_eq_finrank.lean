-- Prove2me | solution 1 for ModularCurve.sum_ord_jBar_sub_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f3a2f85f-686e-51e3-bf38-1705ba4b0519

import Definitions.Def_ModularCurve_X0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_HahnSeries_RamificationBound
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Theorems.Thm_ModularCurve_sum_ord_jBar_sub_eq_dedekindPsi
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sum_ord_jBar_sub_eq_finrank
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_sum_ord_jBar_sub_eq_finrank.ModularCurve Polynomial"

namespace ModularCurve p2m_export "ModularCurve" "dedekindPsi jBar modularFunctionFieldBar sum_ord_jBar_sub_eq_dedekindPsi deg_eq_one_modularFunctionFieldBar CompEq.finrank_adjoin_jBar_eq_dedekindPsi" end ModularCurve
p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.sum_ord_jBar_sub_eq_finrank_aux (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ)
    [FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N)]
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)) :
    ∑ v ∈ S, v.ord (jBar N -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) =
      Module.finrank
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({jBar N} : Set ↥(modularFunctionFieldBar N)))
        ↥(modularFunctionFieldBar N) := by
  rw [ModularCurve.sum_ord_jBar_sub_eq_dedekindPsi N j₀
        (ModularCurve.deg_eq_one_modularFunctionFieldBar N) S hS,
    ModularCurve.CompEq.finrank_adjoin_jBar_eq_dedekindPsi N]

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_sum_ord_jBar_sub_eq_finrank.ModularCurve Polynomial in

theorem solution (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ)
    [FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N)]
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)) :
    ∑ v ∈ S, v.ord (jBar N -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) =
      Module.finrank
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({jBar N} : Set ↥(modularFunctionFieldBar N)))
        ↥(modularFunctionFieldBar N) :=
  ModularCurve.sum_ord_jBar_sub_eq_finrank_aux N j₀ S hS

#print axioms solution

end S_ModularCurve_sum_ord_jBar_sub_eq_finrank
end P2MW
export P2MW.S_ModularCurve_sum_ord_jBar_sub_eq_finrank (solution)
