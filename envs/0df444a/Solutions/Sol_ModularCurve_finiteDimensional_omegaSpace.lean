-- Prove2me | solution 1 for ModularCurve.finiteDimensional_omegaSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/247eafbb-2e6d-5ea8-af4c-160258a7b0bc

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_exists_isRational
import Theorems.Thm_AlgebraicCurve_finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finiteDimensional_omegaSpace
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open AlgebraicCurve ModularCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (D : AlgebraicCurve.Divisor K ↥(modularFunctionFieldC K N)) :
    FiniteDimensional K ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D) := by
  haveI hco : IsCurveOver K ↥(modularFunctionFieldC K N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField K N
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)
  haveI : Algebra.EssFiniteType K ↥(modularFunctionFieldC K N) := by
    rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K p N hpN]
    exact ModularCurve.essFiniteType_modularFunctionFieldFullC K N
  have hC : ConstantsAreBase K ↥(modularFunctionFieldC K N) := by
    have hdeg : (ModularCurve.cuspInftyGeom K N).deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed _
    refine AlgebraicCurve.constantsAreBase_of_exists_isRational (ModularCurve.cuspInftyGeom K N) ?_
      (by rw [hdeg]; exact one_ne_zero)
    haveI : Module.Finite K (ModularCurve.cuspInftyGeom K N).ResidueField := IsCurveOver.finiteResidue _
    haveI : Algebra.IsIntegral K (ModularCurve.cuspInftyGeom K N).ResidueField := Algebra.IsIntegral.of_finite K _
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)).2
  obtain ⟨hfin, e, -⟩ := AlgebraicCurve.finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace hC D
  haveI := hfin
  exact Module.Finite.equiv e

end S_ModularCurve_finiteDimensional_omegaSpace
end P2MW
export P2MW.S_ModularCurve_finiteDimensional_omegaSpace (solution)
