-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2c49a763-c68e-5784-ba7d-e93ae232e851

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Mathlib.Topology.Algebra.OpenSubgroup
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_norm_jacquetWhittaker3_le_of_rootSize_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
import Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne
import Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.CubicInduction"

noncomputable section

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl3Entry_mul (g k : LocalGL3 v) (i j : Fin 3) :
    gl3Entry v (g * k) i j =
      gl3Entry v g i 0 * gl3Entry v k 0 j + gl3Entry v g i 1 * gl3Entry v k 1 j +
        gl3Entry v g i 2 * gl3Entry v k 2 j := by
  simp only [gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private def rightMinor (g : LocalGL3 v) : v.adicCompletion ℚ :=
  gl3Entry v g 1 1 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 1

private theorem cornerEntry_mul_rightMinor (g : LocalGL3 v) :
    cornerEntry v g * rightMinor v g = gl3Entry v g 2 1 * outerMinor v g - gl3Entry v g 2 2 * lowerMinor v g := by
  simp only [cornerEntry, rightMinor, outerMinor, lowerMinor]
  ring

private theorem cornerEntry_mul (g k : LocalGL3 v) :
    cornerEntry v (g * k) =
      cornerEntry v g * gl3Entry v k 0 0 + gl3Entry v g 2 1 * gl3Entry v k 1 0 +
        gl3Entry v g 2 2 * gl3Entry v k 2 0 := by
  simp only [cornerEntry, gl3Entry_mul]

private theorem lowerMinor_mul (g k : LocalGL3 v) :
    lowerMinor v (g * k) =
      lowerMinor v g * (gl3Entry v k 0 0 * gl3Entry v k 1 1 - gl3Entry v k 0 1 * gl3Entry v k 1 0) +
        outerMinor v g * (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) +
          rightMinor v g * (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0) := by
  simp only [lowerMinor, outerMinor, rightMinor, gl3Entry_mul]
  ring

private theorem outerMinor_mul (g k : LocalGL3 v) :
    outerMinor v (g * k) =
      lowerMinor v g * (gl3Entry v k 0 0 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 0) +
        outerMinor v g * (gl3Entry v k 0 0 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 0) +
          rightMinor v g * (gl3Entry v k 1 0 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 0) := by
  simp only [lowerMinor, outerMinor, rightMinor, gl3Entry_mul]
  ring

private theorem gl3Det_mul (g k : LocalGL3 v) : gl3Det v (g * k) = gl3Det v g * gl3Det v k := by
  simp only [gl3Det, Units.val_mul, Matrix.det_mul]

private theorem cellRatio_zero_mul_cornerEntry {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) :
    cellRatio v g 0 * cornerEntry v g = gl3Entry v g 2 1 := by
  show gl3Entry v g 2 1 / cornerEntry v g * cornerEntry v g = gl3Entry v g 2 1
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hc, mul_one]

private theorem cellRatio_one_mul_cornerEntry {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) :
    cellRatio v g 1 * cornerEntry v g = gl3Entry v g 2 2 := by
  show gl3Entry v g 2 2 / cornerEntry v g * cornerEntry v g = gl3Entry v g 2 2
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hc, mul_one]

private theorem cellRatio_two_mul_lowerMinor {g : LocalGL3 v} (hl : lowerMinor v g ≠ 0) :
    cellRatio v g 2 * lowerMinor v g = outerMinor v g := by
  show outerMinor v g / lowerMinor v g * lowerMinor v g = outerMinor v g
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hl, mul_one]

private theorem rightMinor_eq_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) :
    rightMinor v g = (cellRatio v g 0 * cellRatio v g 2 - cellRatio v g 1) * lowerMinor v g := by
  apply mul_left_cancel₀ hc
  rw [cornerEntry_mul_rightMinor, ← cellRatio_zero_mul_cornerEntry v hc, ← cellRatio_one_mul_cornerEntry v hc,
    ← cellRatio_two_mul_lowerMinor v hl]
  ring

private theorem cornerEntry_mul_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    cornerEntry v (g * k) =
      cornerEntry v g *
        (gl3Entry v k 0 0 + cellRatio v g 0 * gl3Entry v k 1 0 + cellRatio v g 1 * gl3Entry v k 2 0) := by
  rw [cornerEntry_mul, ← cellRatio_zero_mul_cornerEntry v hc, ← cellRatio_one_mul_cornerEntry v hc]
  ring

private theorem gl3Entry_two_one_mul_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    gl3Entry v (g * k) 2 1 =
      cornerEntry v g *
        (gl3Entry v k 0 1 + cellRatio v g 0 * gl3Entry v k 1 1 + cellRatio v g 1 * gl3Entry v k 2 1) := by
  rw [gl3Entry_mul, ← cellRatio_zero_mul_cornerEntry v hc, ← cellRatio_one_mul_cornerEntry v hc]
  simp only [cornerEntry]
  ring

private theorem gl3Entry_two_two_mul_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    gl3Entry v (g * k) 2 2 =
      cornerEntry v g *
        (gl3Entry v k 0 2 + cellRatio v g 0 * gl3Entry v k 1 2 + cellRatio v g 1 * gl3Entry v k 2 2) := by
  rw [gl3Entry_mul, ← cellRatio_zero_mul_cornerEntry v hc, ← cellRatio_one_mul_cornerEntry v hc]
  simp only [cornerEntry]
  ring

private theorem lowerMinor_mul_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0)
    (k : LocalGL3 v) :
    lowerMinor v (g * k) =
      lowerMinor v g *
        ((gl3Entry v k 0 0 * gl3Entry v k 1 1 - gl3Entry v k 0 1 * gl3Entry v k 1 0) +
          cellRatio v g 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) +
            (cellRatio v g 0 * cellRatio v g 2 - cellRatio v g 1) *
              (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0)) := by
  rw [lowerMinor_mul, ← cellRatio_two_mul_lowerMinor v hl, rightMinor_eq_of_ne_zero v hc hl]
  ring

private theorem outerMinor_mul_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0)
    (k : LocalGL3 v) :
    outerMinor v (g * k) =
      lowerMinor v g *
        ((gl3Entry v k 0 0 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 0) +
          cellRatio v g 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 0) +
            (cellRatio v g 0 * cellRatio v g 2 - cellRatio v g 1) *
              (gl3Entry v k 1 0 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 0)) := by
  rw [outerMinor_mul, ← cellRatio_two_mul_lowerMinor v hl, rightMinor_eq_of_ne_zero v hc hl]
  ring

end

set_option autoImplicit false

noncomputable section

p2m_open "IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal Matrix"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section RightLaws

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl3Entry_mul_diagonal3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) (i j : Fin 3) :
    gl3Entry v (g * diagonal3 v a) i j = gl3Entry v g i j * (a j : v.adicCompletion ℚ) := by
  simp [gl3Entry, Matrix.mul_diagonal]

private theorem gl3Entry_mul_upperUnipotent3_zero (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 x y z) i 0 = gl3Entry v g i 0 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_upperUnipotent3_one (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 x y z) i 1 = gl3Entry v g i 0 * x + gl3Entry v g i 1 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_upperUnipotent3_two (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 x y z) i 2 =
      gl3Entry v g i 0 * z + gl3Entry v g i 1 * y + gl3Entry v g i 2 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem cornerEntry_mul_diagonal3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    cornerEntry v (g * diagonal3 v a) = cornerEntry v g * (a 0 : v.adicCompletion ℚ) := by
  simp [cornerEntry, gl3Entry_mul_diagonal3]

private theorem lowerMinor_mul_diagonal3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    lowerMinor v (g * diagonal3 v a) = (a 0 : v.adicCompletion ℚ) * a 1 * lowerMinor v g := by
  simp only [lowerMinor, gl3Entry_mul_diagonal3]
  ring

private theorem outerMinor_mul_diagonal3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    outerMinor v (g * diagonal3 v a) = (a 0 : v.adicCompletion ℚ) * a 2 * outerMinor v g := by
  simp only [outerMinor, gl3Entry_mul_diagonal3]
  ring

private theorem gl3Det_mul_diagonal3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    gl3Det v (g * diagonal3 v a) = gl3Det v g * ((a 0 : v.adicCompletion ℚ) * a 1 * a 2) := by
  rw [gl3Det, gl3Det, Units.val_mul, Matrix.det_mul, diagonal3_coe, Matrix.det_diagonal, Fin.prod_univ_three]

private theorem cornerEntry_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    cornerEntry v (g * upperUnipotent3 x y z) = cornerEntry v g := by
  simp [cornerEntry, gl3Entry_mul_upperUnipotent3_zero]

private theorem lowerMinor_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    lowerMinor v (g * upperUnipotent3 x y z) = lowerMinor v g := by
  simp only [lowerMinor, gl3Entry_mul_upperUnipotent3_zero, gl3Entry_mul_upperUnipotent3_one]
  ring

private theorem outerMinor_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    outerMinor v (g * upperUnipotent3 x y z) = outerMinor v g + y * lowerMinor v g := by
  simp only [outerMinor, lowerMinor, gl3Entry_mul_upperUnipotent3_zero, gl3Entry_mul_upperUnipotent3_two]
  ring

private theorem gl3Det_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    gl3Det v (g * upperUnipotent3 x y z) = gl3Det v g := by
  have h1 : Matrix.det !![(1 : v.adicCompletion ℚ), x, z; 0, 1, y; 0, 0, 1] = 1 := by
    simp [Matrix.det_fin_three]
  rw [gl3Det, gl3Det, Units.val_mul, Matrix.det_mul, upperUnipotent3_coe, h1, mul_one]

private theorem cellRatio_mul_diagonal3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v)
    (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) :
    cellRatio v (g * diagonal3 v a) =
      ![cellRatio v g 0 * ((a 1 : v.adicCompletion ℚ) / a 0), cellRatio v g 1 * ((a 2 : v.adicCompletion ℚ) / a 0),
        cellRatio v g 2 * ((a 2 : v.adicCompletion ℚ) / a 1)] := by
  have h0 : (a 0 : v.adicCompletion ℚ) ≠ 0 := (a 0).ne_zero
  have h1 : (a 1 : v.adicCompletion ℚ) ≠ 0 := (a 1).ne_zero
  simp only [cellRatio, gl3Entry_mul_diagonal3, outerMinor_mul_diagonal3, lowerMinor_mul_diagonal3, cornerEntry]
    at hc ⊢
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    field_simp
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    field_simp

private theorem cellRatio_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) (g : LocalGL3 v)
    (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) :
    cellRatio v (g * upperUnipotent3 x y z) =
      ![cellRatio v g 0 + x, cellRatio v g 1 + cellRatio v g 0 * y + z, cellRatio v g 2 + y] := by
  simp only [cellRatio, gl3Entry_mul_upperUnipotent3_zero, gl3Entry_mul_upperUnipotent3_one,
    gl3Entry_mul_upperUnipotent3_two, outerMinor_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3, cornerEntry]
    at hc ⊢
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    field_simp
    ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp
    ring
  · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    field_simp

private theorem cellValue_mul_diagonal3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) :
    cellValue v χ (g * diagonal3 v a) =
      (χ 0 (a 2) : ℂ) * (χ 1 (a 1) : ℂ) * (χ 2 (a 0) : ℂ) *
        ((‖(a 2 : v.adicCompletion ℚ)‖ / ‖(a 0 : v.adicCompletion ℚ)‖ : ℝ) : ℂ) * cellValue v χ g := by
  have h0 : (a 0 : v.adicCompletion ℚ) ≠ 0 := (a 0).ne_zero
  have h1 : (a 1 : v.adicCompletion ℚ) ≠ 0 := (a 1).ne_zero
  have h01 : (a 0 : v.adicCompletion ℚ) * a 1 ≠ 0 := mul_ne_zero h0 h1
  have hdet : gl3Det v (g * diagonal3 v a) / lowerMinor v (g * diagonal3 v a)
      = (a 2 : v.adicCompletion ℚ) * (gl3Det v g / lowerMinor v g) := by
    rw [gl3Det_mul_diagonal3, lowerMinor_mul_diagonal3,
      show gl3Det v g * ((a 0 : v.adicCompletion ℚ) * a 1 * a 2)
          = ((a 0 : v.adicCompletion ℚ) * a 1) * (a 2 * gl3Det v g) by ring,
      mul_div_mul_left _ _ h01, mul_div_assoc]
  have hlow : lowerMinor v (g * diagonal3 v a) / cornerEntry v (g * diagonal3 v a)
      = (a 1 : v.adicCompletion ℚ) * (lowerMinor v g / cornerEntry v g) := by
    rw [lowerMinor_mul_diagonal3, cornerEntry_mul_diagonal3,
      show (a 0 : v.adicCompletion ℚ) * a 1 * lowerMinor v g
          = (a 0 : v.adicCompletion ℚ) * (a 1 * lowerMinor v g) by ring,
      show cornerEntry v g * (a 0 : v.adicCompletion ℚ) = (a 0 : v.adicCompletion ℚ) * cornerEntry v g by ring,
      mul_div_mul_left _ _ h0, mul_div_assoc]
  have hcor : cornerEntry v (g * diagonal3 v a) = (a 0 : v.adicCompletion ℚ) * cornerEntry v g := by
    rw [cornerEntry_mul_diagonal3, mul_comm]
  unfold cellValue
  rw [hdet, hlow, hcor]
  simp only [charExt_units_mul, norm_mul]
  push_cast
  ring

private theorem cellValue_mul_upperUnipotent3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (x y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) : cellValue v χ (g * upperUnipotent3 x y z) = cellValue v χ g := by
  unfold cellValue
  rw [gl3Det_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3, cornerEntry_mul_upperUnipotent3]

end RightLaws

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section CellSectionLaws

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def datumRescale (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) :
    (Fin 3 → v.adicCompletion ℚ) → ℂ :=
  fun r => Φ ![r 0 * ((a 1 : v.adicCompletion ℚ) / a 0), r 1 * ((a 2 : v.adicCompletion ℚ) / a 0),
    r 2 * ((a 2 : v.adicCompletion ℚ) / a 1)]

private def datumShear (x y z : v.adicCompletion ℚ) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) :
    (Fin 3 → v.adicCompletion ℚ) → ℂ :=
  fun r => Φ ![r 0 + x, r 1 + r 0 * y + z, r 2 + y]

private theorem datumRescale_apply (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (r : Fin 3 → v.adicCompletion ℚ) :
    datumRescale v a Φ r = Φ ![r 0 * ((a 1 : v.adicCompletion ℚ) / a 0), r 1 * ((a 2 : v.adicCompletion ℚ) / a 0),
      r 2 * ((a 2 : v.adicCompletion ℚ) / a 1)] :=
  rfl

private theorem datumShear_apply (x y z : v.adicCompletion ℚ) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (r : Fin 3 → v.adicCompletion ℚ) : datumShear v x y z Φ r = Φ ![r 0 + x, r 1 + r 0 * y + z, r 2 + y] :=
  rfl

private theorem mul_diagonal3_mem_bigCell3_iff (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    g * diagonal3 v a ∈ bigCell3 v ↔ g ∈ bigCell3 v := by
  have h0 : (a 0 : v.adicCompletion ℚ) ≠ 0 := (a 0).ne_zero
  have h1 : (a 1 : v.adicCompletion ℚ) ≠ 0 := (a 1).ne_zero
  simp only [mem_bigCell3_iff, cornerEntry_mul_diagonal3, lowerMinor_mul_diagonal3, ne_eq, mul_eq_zero, h0, h1,
    or_false, false_or]

private theorem mul_upperUnipotent3_mem_bigCell3_iff (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    g * upperUnipotent3 x y z ∈ bigCell3 v ↔ g ∈ bigCell3 v := by
  simp only [mem_bigCell3_iff, cornerEntry_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3]

private theorem cellSectionOf_mul_diagonal3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    cellSectionOf v χ Φ (g * diagonal3 v a) =
      (χ 0 (a 2) : ℂ) * (χ 1 (a 1) : ℂ) * (χ 2 (a 0) : ℂ) *
        ((‖(a 2 : v.adicCompletion ℚ)‖ / ‖(a 0 : v.adicCompletion ℚ)‖ : ℝ) : ℂ) *
          cellSectionOf v χ (datumRescale v a Φ) g := by
  by_cases hg : g ∈ bigCell3 v
  · have hga : g * diagonal3 v a ∈ bigCell3 v := (mul_diagonal3_mem_bigCell3_iff v a g).mpr hg
    rw [cellSectionOf_apply_of_mem v χ _ hga, cellSectionOf_apply_of_mem v χ _ hg, cellValue_mul_diagonal3,
      cellRatio_mul_diagonal3 v a g hg.1 hg.2, datumRescale_apply]
    ring
  · have hga : g * diagonal3 v a ∉ bigCell3 v := fun h => hg ((mul_diagonal3_mem_bigCell3_iff v a g).mp h)
    rw [cellSectionOf_apply_of_notMem v χ _ hga, cellSectionOf_apply_of_notMem v χ _ hg, mul_zero]

private theorem cellSectionOf_mul_upperUnipotent3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    cellSectionOf v χ Φ (g * upperUnipotent3 x y z) = cellSectionOf v χ (datumShear v x y z Φ) g := by
  by_cases hg : g ∈ bigCell3 v
  · have hgn : g * upperUnipotent3 x y z ∈ bigCell3 v := (mul_upperUnipotent3_mem_bigCell3_iff v x y z g).mpr hg
    rw [cellSectionOf_apply_of_mem v χ _ hgn, cellSectionOf_apply_of_mem v χ _ hg, cellValue_mul_upperUnipotent3,
      cellRatio_mul_upperUnipotent3 v x y z g hg.1 hg.2, datumShear_apply]
  · have hgn : g * upperUnipotent3 x y z ∉ bigCell3 v :=
      fun h => hg ((mul_upperUnipotent3_mem_bigCell3_iff v x y z g).mp h)
    rw [cellSectionOf_apply_of_notMem v χ _ hgn, cellSectionOf_apply_of_notMem v χ _ hg]

private theorem gl3AmbientRightTranslate_diagonal3_cellSectionOf (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) (cellSectionOf v χ Φ) =
      fun g => (χ 0 (a 2) : ℂ) * (χ 1 (a 1) : ℂ) * (χ 2 (a 0) : ℂ) *
        ((‖(a 2 : v.adicCompletion ℚ)‖ / ‖(a 0 : v.adicCompletion ℚ)‖ : ℝ) : ℂ) *
          cellSectionOf v χ (datumRescale v a Φ) g := by
  funext g
  exact cellSectionOf_mul_diagonal3 v χ Φ a g

private theorem gl3AmbientRightTranslate_upperUnipotent3_cellSectionOf (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (x y z : v.adicCompletion ℚ) :
    gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) (cellSectionOf v χ Φ) =
      cellSectionOf v χ (datumShear v x y z Φ) := by
  funext g
  exact cellSectionOf_mul_upperUnipotent3 v χ Φ x y z g

end CellSectionLaws

section DatumRegularity

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem continuous_vec3 {f₀ f₁ f₂ : (Fin 3 → v.adicCompletion ℚ) → v.adicCompletion ℚ}
    (h₀ : Continuous f₀) (h₁ : Continuous f₁) (h₂ : Continuous f₂) :
    Continuous fun r : Fin 3 → v.adicCompletion ℚ => ![f₀ r, f₁ r, f₂ r] :=
  h₀.matrixVecCons (h₁.matrixVecCons (h₂.matrixVecCons continuous_const))

variable (v)

private def rescaleHomeomorph3 (c₀ c₁ c₂ : v.adicCompletion ℚ) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    (Fin 3 → v.adicCompletion ℚ) ≃ₜ (Fin 3 → v.adicCompletion ℚ) where
  toFun r := ![r 0 * c₀, r 1 * c₁, r 2 * c₂]
  invFun r := ![r 0 * c₀⁻¹, r 1 * c₁⁻¹, r 2 * c₂⁻¹]
  left_inv r := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      field_simp
  right_inv r := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      field_simp
  continuous_toFun := continuous_vec3 ((continuous_apply 0).mul continuous_const)
    ((continuous_apply 1).mul continuous_const) ((continuous_apply 2).mul continuous_const)
  continuous_invFun := continuous_vec3 ((continuous_apply 0).mul continuous_const)
    ((continuous_apply 1).mul continuous_const) ((continuous_apply 2).mul continuous_const)

private def shearHomeomorph3 (x y z : v.adicCompletion ℚ) :
    (Fin 3 → v.adicCompletion ℚ) ≃ₜ (Fin 3 → v.adicCompletion ℚ) where
  toFun r := ![r 0 + x, r 1 + r 0 * y + z, r 2 + y]
  invFun r := ![r 0 - x, r 1 - (r 0 - x) * y - z, r 2 - y]
  left_inv r := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      ring
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      ring
    · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      ring
  right_inv r := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      ring
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      ring
    · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      ring
  continuous_toFun := continuous_vec3 ((continuous_apply 0).add continuous_const)
    (((continuous_apply 1).add ((continuous_apply 0).mul continuous_const)).add continuous_const)
    ((continuous_apply 2).add continuous_const)
  continuous_invFun := continuous_vec3 ((continuous_apply 0).sub continuous_const)
    (((continuous_apply 1).sub (((continuous_apply 0).sub continuous_const).mul continuous_const)).sub
      continuous_const) ((continuous_apply 2).sub continuous_const)

private theorem datumRescale_eq_comp (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) :
    datumRescale v a Φ = Φ ∘ rescaleHomeomorph3 v ((a 1 : v.adicCompletion ℚ) / a 0)
      ((a 2 : v.adicCompletion ℚ) / a 0) ((a 2 : v.adicCompletion ℚ) / a 1)
      (div_ne_zero (a 1).ne_zero (a 0).ne_zero) (div_ne_zero (a 2).ne_zero (a 0).ne_zero)
      (div_ne_zero (a 2).ne_zero (a 1).ne_zero) :=
  rfl

private theorem datumShear_eq_comp (x y z : v.adicCompletion ℚ) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) :
    datumShear v x y z Φ = Φ ∘ shearHomeomorph3 v x y z :=
  rfl

private theorem isLocallyConstant_datumRescale (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : IsLocallyConstant Φ) :
    IsLocallyConstant (datumRescale v a Φ) := by
  rw [datumRescale_eq_comp]
  exact hΦ.comp_continuous (Homeomorph.continuous _)

private theorem hasCompactSupport_datumRescale (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : HasCompactSupport Φ) :
    HasCompactSupport (datumRescale v a Φ) := by
  rw [datumRescale_eq_comp]
  exact hΦ.comp_homeomorph _

private theorem isLocallyConstant_datumShear (x y z : v.adicCompletion ℚ)
    {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : IsLocallyConstant Φ) :
    IsLocallyConstant (datumShear v x y z Φ) := by
  rw [datumShear_eq_comp]
  exact hΦ.comp_continuous (Homeomorph.continuous _)

private theorem hasCompactSupport_datumShear (x y z : v.adicCompletion ℚ)
    {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : HasCompactSupport Φ) :
    HasCompactSupport (datumShear v x y z Φ) := by
  rw [datumShear_eq_comp]
  exact hΦ.comp_homeomorph _

end DatumRegularity

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "localBorel borelSpace_localBorel selfDualHaarAt stdRootNumberAt higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt hasConductorExponentAt_zero_iff localLFactorAt modulus modulus_of_ne_zero modulus_ne_zero modulus_mul charExt charExt_zero charExt_of_ne_zero mulMeasure setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq modulus_adicCompletion_eq_nnnorm psiLocal_eq_one_of_mem_integers psiLocal_ne_one forall_eq_one_and_exists_ne_one_of_addCharLevel addCharLevel_psiLocal_rat"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

section GaussShell

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ)

private def gaussShell (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : v.adicCompletion K) : ℂ :=
  ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ u ∂μ

omit [BorelSpace (v.adicCompletion K)] [μ.IsAddHaarMeasure] in
private theorem gaussShell_def (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : v.adicCompletion K) :
    gaussShell K v μ ψ χ c = ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ u ∂μ :=
  rfl

variable {K v μ ψ}

private theorem gaussShell_eq_zero_of_valued_ne {n : ℤ}
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {f : ℕ} (hf : 1 ≤ f) (hχ : HasConductorExponentAt K v χ f)
    {c : v.adicCompletion K} (hc : Valued.v c ≠ WithZero.exp (n + f)) : gaussShell K v μ ψ χ c = 0 :=
  setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne K v μ ψ n hψn hψn' χ f hf hχ c hc

private theorem gaussShell_mul_gaussShell_inv {n : ℤ}
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {f : ℕ} (hf : 1 ≤ f) (hχ : HasConductorExponentAt K v χ f)
    {c : v.adicCompletion K} (hc : Valued.v c = WithZero.exp (n + f)) :
    gaussShell K v μ ψ χ c * gaussShell K v μ ψ χ⁻¹ c * (Ideal.absNorm v.asIdeal : ℂ) ^ f
      = charExt χ (-1) * ((μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) ^ 2 :=
  setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq K v μ ψ n hψn hψn' χ f hf hχ c hc

omit [BorelSpace (v.adicCompletion K)] in

private theorem measure_integers_ne_zero : μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ≠ 0 :=
  (Valued.isOpen_valuationSubring _ : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))).measure_ne_zero
    μ ⟨0, zero_mem _⟩

omit [BorelSpace (v.adicCompletion K)] in

private theorem measure_integers_ne_top : μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ≠ ⊤ :=
  (isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers K) from inferInstance) :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K))).measure_lt_top.ne

omit [BorelSpace (v.adicCompletion K)] in

private theorem measureReal_integers_pos : 0 < μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  ENNReal.toReal_pos (measure_integers_ne_zero (μ := μ)) (measure_integers_ne_top (μ := μ))

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
private theorem charExt_neg_one_ne_zero (χ : (v.adicCompletion K)ˣ →* ℂˣ) : charExt χ (-1 : v.adicCompletion K) ≠ 0 := by
  rw [charExt_of_ne_zero χ (neg_ne_zero.mpr one_ne_zero)]
  exact Units.ne_zero _

private theorem gaussShell_ne_zero {n : ℤ}
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {f : ℕ} (hf : 1 ≤ f) (hχ : HasConductorExponentAt K v χ f)
    {c : v.adicCompletion K} (hc : Valued.v c = WithZero.exp (n + f)) : gaussShell K v μ ψ χ c ≠ 0 := by
  intro h0
  have hprod := gaussShell_mul_gaussShell_inv (μ := μ) hψn hψn' hf hχ hc
  rw [h0, zero_mul, zero_mul] at hprod
  have hvol : (((μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (measureReal_integers_pos (μ := μ)).ne')
  exact mul_ne_zero (charExt_neg_one_ne_zero χ) hvol hprod.symm

private theorem gaussShell_inv_ne_zero {n : ℤ}
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {f : ℕ} (hf : 1 ≤ f) (hχ : HasConductorExponentAt K v χ f)
    {c : v.adicCompletion K} (hc : Valued.v c = WithZero.exp (n + f)) : gaussShell K v μ ψ χ⁻¹ c ≠ 0 := by
  intro h0
  have hprod := gaussShell_mul_gaussShell_inv (μ := μ) hψn hψn' hf hχ hc
  rw [h0, mul_zero, zero_mul] at hprod
  have hvol : (((μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (measureReal_integers_pos (μ := μ)).ne')
  exact mul_ne_zero (charExt_neg_one_ne_zero χ) hvol hprod.symm

end GaussShell

section Scaling

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem one_lt_absNorm_asIdeal : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  have hN : (0 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
    exact_mod_cast Nat.zero_lt_one.trans (one_lt_absNorm_asIdeal K v)
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos hN).ne'

private theorem regular_selfDualHaarAt :
    letI := localBorel K v
    (selfDualHaarAt K v).Regular := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  unfold selfDualHaarAt
  infer_instance

variable {K v}

private theorem charExt_mul_eq_mul_of_ne_zero (χ : (v.adicCompletion K)ˣ →* ℂˣ) {x y : v.adicCompletion K} (hx : x ≠ 0)
    (hy : y ≠ 0) : charExt χ (x * y) = charExt χ x * charExt χ y := by
  rw [charExt_of_ne_zero χ (mul_ne_zero hx hy), Units.mk0_mul, map_mul, Units.val_mul, charExt_of_ne_zero χ hx,
    charExt_of_ne_zero χ hy]

private theorem preimage_unitShell_mul_left {w : v.adicCompletion K} (hw : Valued.v w = 1) :
    (fun x : v.adicCompletion K => w * x) ⁻¹' {u : v.adicCompletion K | Valued.v u = 1}
      = {u : v.adicCompletion K | Valued.v u = 1} := by
  ext u
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Valuation.map_mul, hw, one_mul]

private theorem isClosed_closedBall_valued (γ : WithZero (Multiplicative ℤ)) :
    IsClosed {x : v.adicCompletion K | Valued.v x ≤ γ} := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually]
  intro x hx
  have hx' : ¬ Valued.v x ≤ γ := hx
  have hxv : Valued.v x ≠ 0 := fun h => hx' (by rw [h]; exact zero_le')
  filter_upwards [Valued.locally_const hxv] with y hy
  intro hy'
  exact hx' (by rw [← hy]; exact hy')

private theorem isClosed_setOf_valued_eq_one : IsClosed {u : v.adicCompletion K | Valued.v u = 1} := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually]
  intro x hx
  have hx' : Valued.v x ≠ 1 := hx
  by_cases hx0 : x = 0
  · subst hx0
    have h0 : ∀ᶠ y in nhds (0 : v.adicCompletion K), Valued.v y < Valued.v (1 : v.adicCompletion K) := by
      rw [Filter.Eventually, Valued.mem_nhds_zero]
      refine ⟨Units.mk0 (Valued.v.restrict (1 : v.adicCompletion K)) ((Valuation.ne_zero_iff _).mpr one_ne_zero),
        fun y hy => ?_⟩
      exact (Valuation.restrict_lt_iff _).mp hy
    filter_upwards [h0] with y hy
    intro hy1
    have hy1' : Valued.v y = 1 := hy1
    rw [map_one, hy1'] at hy
    exact lt_irrefl _ hy
  · have hxv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    filter_upwards [Valued.locally_const hxv] with y hy
    intro hy1
    have hy1' : Valued.v y = 1 := hy1
    exact hx' (by rw [← hy, hy1'])

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  {μ : Measure (v.adicCompletion K)} [μ.IsAddHaarMeasure]

private theorem map_mul_left_eq_modulus_inv_smul {a : v.adicCompletion K} (ha : a ≠ 0) :
    Measure.map (fun x : v.adicCompletion K => a * x) μ = (modulus a)⁻¹ • μ := by
  have h1 : (DomMulAct.mk (Units.mk0 a ha)⁻¹ • μ) = Measure.map (fun x : v.adicCompletion K => a * x) μ := by
    show μ.map _ = _
    congr 1
  have h2 := Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk (Units.mk0 a ha)⁻¹ • μ) μ
  rw [addHaarScalarFactor_smul_eq_distribHaarChar] at h2
  have h3 : distribHaarChar (v.adicCompletion K) (Units.mk0 a ha)⁻¹ = (modulus a)⁻¹ := by
    rw [map_inv, modulus_of_ne_zero ha]
  rw [← h1, h2, h3]

private theorem integral_comp_mul_left_eq_modulus_inv_smul {a : v.adicCompletion K} (ha : a ≠ 0)
    (f : v.adicCompletion K → ℂ) : ∫ x, f (a * x) ∂μ = (modulus a)⁻¹ • ∫ x, f x ∂μ := by
  have hemb : MeasurableEmbedding (fun x : v.adicCompletion K => a * x) :=
    (Homeomorph.mulLeft₀ a ha).measurableEmbedding
  rw [← hemb.integral_map, map_mul_left_eq_modulus_inv_smul ha, integral_smul_nnreal_measure]

private theorem setIntegral_comp_mul_left_eq_modulus_inv_smul {a : v.adicCompletion K} (ha : a ≠ 0)
    {S : Set (v.adicCompletion K)} (hS : MeasurableSet S) (f : v.adicCompletion K → ℂ) :
    ∫ x in (fun x : v.adicCompletion K => a * x) ⁻¹' S, f (a * x) ∂μ = (modulus a)⁻¹ • ∫ x in S, f x ∂μ := by
  have hemb : MeasurableEmbedding (fun x : v.adicCompletion K => a * x) :=
    (Homeomorph.mulLeft₀ a ha).measurableEmbedding
  rw [← hemb.integral_map, ← Measure.restrict_map hemb.measurable hS, map_mul_left_eq_modulus_inv_smul ha,
    Measure.restrict_smul, integral_smul_nnreal_measure]

private theorem modulus_eq_one_of_valued_eq_one [μ.Regular] {w : v.adicCompletion K} (hw : Valued.v w = 1) :
    modulus w = 1 := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  rw [modulus_of_ne_zero hw0]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
    (s := (v.adicCompletionIntegers K : Set (v.adicCompletion K))) (measure_integers_ne_zero (μ := μ))
    (measure_integers_ne_top (μ := μ)) ?_
  rw [ENNReal.coe_one, one_mul]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hy ⊢
    show Valued.v (Units.mk0 w hw0 • y) ≤ 1
    rw [Units.smul_def, Units.val_mk0, smul_eq_mul, Valuation.map_mul, hw, one_mul]
    exact hy
  · intro hx
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hx
    refine ⟨w⁻¹ * x, ?_, ?_⟩
    · rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, hw, inv_one,
        one_mul]
      exact hx
    · show Units.mk0 w hw0 • (w⁻¹ * x) = x
      rw [Units.smul_def, Units.val_mk0, smul_eq_mul, mul_inv_cancel_left₀ hw0]

private theorem map_mul_left_eq_self_of_valued_eq_one [μ.Regular] {w : v.adicCompletion K} (hw : Valued.v w = 1) :
    Measure.map (fun x : v.adicCompletion K => w * x) μ = μ := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  rw [map_mul_left_eq_modulus_inv_smul hw0, modulus_eq_one_of_valued_eq_one (μ := μ) hw, inv_one, one_smul]

private theorem measurePreserving_add_mul_left_of_valued_eq_one [μ.Regular] (t : v.adicCompletion K)
    {w : v.adicCompletion K} (hw : Valued.v w = 1) :
    MeasurePreserving (fun x : v.adicCompletion K => t + w * x) μ μ := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have h1 : MeasurePreserving (fun x : v.adicCompletion K => w * x) μ μ :=
    ⟨(Homeomorph.mulLeft₀ w hw0).measurableEmbedding.measurable, map_mul_left_eq_self_of_valued_eq_one hw⟩
  exact (measurePreserving_add_left μ t).comp h1

private theorem measurableSet_closedBall_valued (γ : WithZero (Multiplicative ℤ)) :
    MeasurableSet {x : v.adicCompletion K | Valued.v x ≤ γ} :=
  (isClosed_closedBall_valued γ).measurableSet

private theorem measurableSet_unitShell : MeasurableSet {u : v.adicCompletion K | Valued.v u = 1} :=
  isClosed_setOf_valued_eq_one.measurableSet

private theorem charExt_mul_gaussShell_mul [μ.Regular] (ψ : AddChar (v.adicCompletion K) ℂ)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : v.adicCompletion K) {w : v.adicCompletion K} (hw : Valued.v w = 1) :
    charExt χ w * gaussShell K v μ ψ χ (c * w) = gaussShell K v μ ψ χ c := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hemb : MeasurableEmbedding (fun x : v.adicCompletion K => w * x) :=
    (Homeomorph.mulLeft₀ w hw0).measurableEmbedding
  have hmp : MeasurePreserving (fun x : v.adicCompletion K => w * x) μ μ :=
    ⟨hemb.measurable, map_mul_left_eq_self_of_valued_eq_one hw⟩

  set g : v.adicCompletion K → ℂ := fun u => ψ (c * u) * charExt χ (w⁻¹ * u) with hg
  have hsub := hmp.setIntegral_preimage_emb hemb g {u : v.adicCompletion K | Valued.v u = 1}
  rw [preimage_unitShell_mul_left hw] at hsub

  have hleft : ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, g (w * u) ∂μ = gaussShell K v μ ψ χ (c * w) := by
    rw [gaussShell_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hg, inv_mul_cancel_left₀ hw0, mul_assoc]

  have hright : charExt χ w * ∫ u in {u : v.adicCompletion K | Valued.v u = 1}, g u ∂μ = gaussShell K v μ ψ χ c := by
    rw [gaussShell_def, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_unitShell fun u hu => ?_
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    have hcw : charExt χ w * charExt χ w⁻¹ = 1 := by
      rw [← charExt_mul_eq_mul_of_ne_zero χ hw0 (inv_ne_zero hw0), mul_inv_cancel₀ hw0,
        charExt_of_ne_zero χ one_ne_zero]
      simp
    simp only [hg]
    rw [charExt_mul_eq_mul_of_ne_zero χ (inv_ne_zero hw0) hu0]
    linear_combination (ψ (c * u) * charExt χ u) * hcw
  rw [← hleft, hsub, hright]

private theorem setIntegral_charExt_one_add_mul_eq_zero [μ.Regular] {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : HasConductorExponentAt K v χ a) {m : ℕ} (hm1 : 1 ≤ m) (hma : m < a) {r : v.adicCompletion K} {j : ℤ}
    (hr : Valued.v r * WithZero.exp j = WithZero.exp (-(m : ℤ))) :
    ∫ x in {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp j}, charExt χ (1 + x * r) ∂μ = 0 := by
  obtain ⟨u₀, hu₀, hχu₀⟩ := hχ.2 m hma
  obtain ⟨hu₀v, hu₀m⟩ := (mem_higherUnitsAt_iff K v).mp hu₀
  have hm0 : m ≠ 0 := by omega
  have hu₀m' : Valued.v ((u₀ : v.adicCompletion K) - 1) ≤ WithZero.exp (-(m : ℤ)) := hu₀m.resolve_left hm0
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero, zero_mul] at hr
    exact WithZero.exp_ne_zero hr.symm
  have hvr : Valued.v r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  set t : v.adicCompletion K := ((u₀ : v.adicCompletion K) - 1) / r with ht
  have hvt : Valued.v t ≤ WithZero.exp j := by
    rw [ht, Valuation.map_div, div_le_iff₀' (pos_iff_ne_zero.mpr hvr), hr]
    exact hu₀m'

  set A : v.adicCompletion K → v.adicCompletion K := fun x => t + (u₀ : v.adicCompletion K) * x with hA
  have hAball : A ⁻¹' {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp j}
      = {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp j} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hA]
    constructor
    · intro hx
      have : Valued.v ((u₀ : v.adicCompletion K) * x) = Valued.v (t + (u₀ : v.adicCompletion K) * x - t) := by
        rw [add_sub_cancel_left]
      rw [← one_mul (Valued.v x), ← hu₀v, ← Valuation.map_mul, this]
      exact (Valuation.map_sub _ _ _).trans (max_le hx hvt)
    · intro hx
      refine (Valuation.map_add _ _ _).trans (max_le hvt ?_)
      rw [Valuation.map_mul, hu₀v, one_mul]
      exact hx
  have hAmp : MeasurePreserving A μ μ := measurePreserving_add_mul_left_of_valued_eq_one t hu₀v
  have hAemb : MeasurableEmbedding A :=
    ((Homeomorph.mulLeft₀ (u₀ : v.adicCompletion K) u₀.ne_zero).trans (Homeomorph.addLeft t)).measurableEmbedding

  have hkey : ∀ x : v.adicCompletion K, 1 + A x * r = (u₀ : v.adicCompletion K) * (1 + x * r) := by
    intro x
    simp only [hA, ht]
    field_simp
    ring

  have hunit : ∀ x ∈ {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp j}, (1 : v.adicCompletion K) + x * r ≠ 0 := by
    intro x hx
    have hlt : Valued.v (x * r) < 1 := by
      rw [Valuation.map_mul]
      calc Valued.v x * Valued.v r ≤ WithZero.exp j * Valued.v r := mul_le_mul' hx le_rfl
        _ = WithZero.exp (-(m : ℤ)) := by rw [mul_comm]; exact hr
        _ < 1 := by
          rw [← WithZero.exp_zero]
          exact WithZero.exp_lt_exp.mpr (by omega)
    have h1 : Valued.v ((1 : v.adicCompletion K) + x * r) = 1 := Valuation.map_one_add_of_lt _ hlt
    intro h0
    rw [h0, Valuation.map_zero] at h1
    exact zero_ne_one h1
  set I : ℂ := ∫ x in {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp j}, charExt χ (1 + x * r) ∂μ with hI

  have hsub := hAmp.setIntegral_preimage_emb hAemb (fun x => charExt χ (1 + x * r))
    {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp j}
  rw [hAball] at hsub
  have hmulI : ∫ x in {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp j}, charExt χ (1 + A x * r) ∂μ
      = ((χ u₀ : ℂˣ) : ℂ) * I := by
    rw [hI, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_closedBall_valued _) fun x hx => ?_
    rw [hkey x, charExt_mul_eq_mul_of_ne_zero χ u₀.ne_zero (hunit x hx), charExt_of_ne_zero χ u₀.ne_zero,
      Units.mk0_val]
  have hII : I = ((χ u₀ : ℂˣ) : ℂ) * I := by
    rw [← hmulI]
    exact hsub.symm
  have hne : ((χ u₀ : ℂˣ) : ℂ) - 1 ≠ 0 := by
    intro h
    apply hχu₀
    exact Units.ext (sub_eq_zero.mp h)
  have : (((χ u₀ : ℂˣ) : ℂ) - 1) * I = 0 := by
    rw [sub_mul, one_mul, ← hII, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hne

end Scaling

section Cosets

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem isCompact_setOf_valued_le_exp_one :
    IsCompact {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (1 : ℤ)} := by
  have hO : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)
  set π : v.adicCompletion K := (NumberField.AdelicLevel.uniformizerUnit K v : v.adicCompletion K) with hπ
  have hπv : Valued.v π = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit K v
  have hπ0 : π ≠ 0 := (NumberField.AdelicLevel.uniformizerUnit K v).ne_zero
  have h11 : WithZero.exp (-1 : ℤ) * WithZero.exp (1 : ℤ) = 1 := by
    rw [← WithZero.exp_add]
    norm_num
  have himage : {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (1 : ℤ)}
      = (fun y : v.adicCompletion K => π⁻¹ * y) '' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x
    constructor
    · intro hx
      have hx' : Valued.v x ≤ WithZero.exp (1 : ℤ) := hx
      refine ⟨π * x, ?_, ?_⟩
      · rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, hπv, ← h11]
        exact mul_le_mul' le_rfl hx'
      · show π⁻¹ * (π * x) = x
        rw [← mul_assoc, inv_mul_cancel₀ hπ0, one_mul]
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hy
      show Valued.v (π⁻¹ * y) ≤ WithZero.exp (1 : ℤ)
      rw [Valuation.map_mul, map_inv₀, hπv, ← WithZero.exp_neg, neg_neg]
      calc WithZero.exp (1 : ℤ) * Valued.v y ≤ WithZero.exp (1 : ℤ) * 1 := mul_le_mul' le_rfl hy
        _ = WithZero.exp (1 : ℤ) := mul_one _
  rw [himage]
  exact hO.image (continuous_const.mul continuous_id)

private def integerCoset (x₀ : v.adicCompletion K) : Set (v.adicCompletion K) := {x | Valued.v (x - x₀) ≤ 1}

variable {K v}

private theorem mem_integerCoset {x₀ x : v.adicCompletion K} : x ∈ integerCoset K v x₀ ↔ Valued.v (x - x₀) ≤ 1 := Iff.rfl

private theorem self_mem_integerCoset (x₀ : v.adicCompletion K) : x₀ ∈ integerCoset K v x₀ := by
  rw [mem_integerCoset, sub_self, Valuation.map_zero]
  exact zero_le'

private theorem integerCoset_eq_preimage (x₀ : v.adicCompletion K) :
    integerCoset K v x₀ = (fun x => -x₀ + x) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext x
  rw [mem_integerCoset, Set.mem_preimage, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
    neg_add_eq_sub]

private theorem isOpen_integerCoset (x₀ : v.adicCompletion K) : IsOpen (integerCoset K v x₀) := by
  rw [integerCoset_eq_preimage]
  exact (Valued.isOpen_valuationSubring _ : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))).preimage
    (continuous_const.add continuous_id)

private theorem integerCoset_subset_setOf_valued_le_exp_one {x₀ : v.adicCompletion K}
    (hx₀ : Valued.v x₀ ≤ WithZero.exp (1 : ℤ)) :
    integerCoset K v x₀ ⊆ {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (1 : ℤ)} := by
  intro x hx
  have hx' : Valued.v (x - x₀) ≤ 1 := hx
  have h1 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (1 : ℤ) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr zero_le_one
  show Valued.v x ≤ WithZero.exp (1 : ℤ)
  have hsplit : x = (x - x₀) + x₀ := (sub_add_cancel x x₀).symm
  rw [hsplit]
  exact Valuation.map_add_le Valued.v (hx'.trans h1) hx₀

private theorem integerCoset_eq_of_mem {x₀ x₁ x : v.adicCompletion K} (h₀ : x ∈ integerCoset K v x₀)
    (h₁ : x ∈ integerCoset K v x₁) : integerCoset K v x₀ = integerCoset K v x₁ := by
  have h₀' : Valued.v (x - x₀) ≤ 1 := h₀
  have h₁' : Valued.v (x - x₁) ≤ 1 := h₁
  have h01 : Valued.v (x₀ - x₁) ≤ 1 := by
    have hs : x₀ - x₁ = (x - x₁) - (x - x₀) := by ring
    rw [hs]
    exact Valuation.map_sub_le Valued.v h₁' h₀'
  have h10 : Valued.v (x₁ - x₀) ≤ 1 := by
    have hs : x₁ - x₀ = (x - x₀) - (x - x₁) := by ring
    rw [hs]
    exact Valuation.map_sub_le Valued.v h₀' h₁'
  ext y
  rw [mem_integerCoset, mem_integerCoset]
  constructor
  · intro hy
    have hs : y - x₁ = (y - x₀) + (x₀ - x₁) := by ring
    rw [hs]
    exact Valuation.map_add_le Valued.v hy h01
  · intro hy
    have hs : y - x₀ = (y - x₁) + (x₁ - x₀) := by ring
    rw [hs]
    exact Valuation.map_add_le Valued.v hy h10

variable (K v)

private theorem exists_finset_integerCoset_cover :
    ∃ R : Finset (v.adicCompletion K), (∀ x₀ ∈ R, Valued.v x₀ ≤ WithZero.exp (1 : ℤ))
      ∧ (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (1 : ℤ) → ∃ x₀ ∈ R, x ∈ integerCoset K v x₀)
      ∧ ∀ x₀ ∈ R, ∀ x₁ ∈ R, x₀ ≠ x₁ → Disjoint (integerCoset K v x₀) (integerCoset K v x₁) := by
  classical
  obtain ⟨t, htball, htfin, hcover⟩ := (isCompact_setOf_valued_le_exp_one K v).elim_finite_subcover_image
    (b := {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (1 : ℤ)}) (c := integerCoset K v)
    (fun x _ => isOpen_integerCoset x) (fun x hx => Set.mem_biUnion hx (self_mem_integerCoset x))

  set C : Finset (Set (v.adicCompletion K)) := htfin.toFinset.image (integerCoset K v) with hC
  have hrep : ∀ c ∈ C, ∃ x₀ ∈ htfin.toFinset, integerCoset K v x₀ = c := by
    intro c hc
    rw [hC] at hc
    exact Finset.mem_image.mp hc
  let rep : {c // c ∈ C} → v.adicCompletion K := fun c => Classical.choose (hrep c.1 c.2)
  have hrep_mem : ∀ c : {c // c ∈ C}, rep c ∈ htfin.toFinset := fun c => (Classical.choose_spec (hrep c.1 c.2)).1
  have hrep_eq : ∀ c : {c // c ∈ C}, integerCoset K v (rep c) = c.1 :=
    fun c => (Classical.choose_spec (hrep c.1 c.2)).2
  refine ⟨C.attach.image rep, ?_, ?_, ?_⟩
  · intro x₀ hx₀
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx₀
    exact htball (htfin.mem_toFinset.mp (hrep_mem c))
  · intro x hx
    have hx' : x ∈ ⋃ i ∈ t, integerCoset K v i := hcover hx
    obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp hx'
    have hiC : integerCoset K v i ∈ C := by
      rw [hC]
      exact Finset.mem_image_of_mem (integerCoset K v) (htfin.mem_toFinset.mpr hit)
    refine ⟨rep ⟨_, hiC⟩, Finset.mem_image_of_mem rep (Finset.mem_attach _ _), ?_⟩
    rw [hrep_eq ⟨_, hiC⟩]
    exact hxi
  · intro x₀ hx₀ x₁ hx₁ hne
    obtain ⟨c₀, -, rfl⟩ := Finset.mem_image.mp hx₀
    obtain ⟨c₁, -, rfl⟩ := Finset.mem_image.mp hx₁
    rw [Set.disjoint_left]
    intro x hxc₀ hxc₁
    apply hne
    have hcc : c₀ = c₁ := Subtype.ext (by rw [← hrep_eq c₀, ← hrep_eq c₁]; exact integerCoset_eq_of_mem hxc₀ hxc₁)
    rw [hcc]

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

variable {K v} in
private theorem measurableSet_integerCoset (x₀ : v.adicCompletion K) : MeasurableSet (integerCoset K v x₀) :=
  (isOpen_integerCoset x₀).measurableSet

variable {K v} in

private theorem measure_integerCoset (x₀ : v.adicCompletion K) :
    μ (integerCoset K v x₀) = μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [integerCoset_eq_preimage]
  exact measure_preimage_add μ (-x₀) _

variable {K v} in
private theorem measureReal_integerCoset (x₀ : v.adicCompletion K) :
    μ.real (integerCoset K v x₀) = μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [measureReal_def, measureReal_def, measure_integerCoset]

variable {K v} in

private theorem setIntegral_indicator_integerCoset {x₀ : v.adicCompletion K} (hx₀ : Valued.v x₀ ≤ WithZero.exp (1 : ℤ))
    (c : ℂ) :
    ∫ x in {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (1 : ℤ)},
        (integerCoset K v x₀).indicator (fun _ => c) x ∂μ
      = ((μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) * c := by
  rw [integral_indicator (measurableSet_integerCoset x₀), Measure.restrict_restrict (measurableSet_integerCoset x₀),
    Set.inter_eq_left.mpr (integerCoset_subset_setOf_valued_le_exp_one hx₀), setIntegral_const,
    measureReal_integerCoset, Complex.real_smul]

private theorem exists_finset_setIntegral_setOf_valued_le_exp_one_eq :
    ∃ R : Finset (v.adicCompletion K), (∀ x₀ ∈ R, Valued.v x₀ ≤ WithZero.exp (1 : ℤ)) ∧
      ∀ f : v.adicCompletion K → ℂ,
        (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (1 : ℤ) →
          ∀ u : v.adicCompletion K, Valued.v u ≤ 1 → f (x + u) = f x) →
        ∫ x in {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (1 : ℤ)}, f x ∂μ
          = ((μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) * ∑ x₀ ∈ R, f x₀ := by
  obtain ⟨R, hRball, hRcover, hRdisj⟩ := exists_finset_integerCoset_cover K v
  refine ⟨R, hRball, ?_⟩
  intro f hf

  have hpt : ∀ x ∈ {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (1 : ℤ)},
      f x = ∑ x₀ ∈ R, (integerCoset K v x₀).indicator (fun _ => f x₀) x := by
    intro x hx
    have hx' : Valued.v x ≤ WithZero.exp (1 : ℤ) := hx
    obtain ⟨a, haR, hxa⟩ := hRcover x hx'
    rw [Finset.sum_eq_single a]
    · rw [Set.indicator_of_mem hxa]
      have hxa' : Valued.v (x - a) ≤ 1 := hxa
      have h := hf a (hRball a haR) (x - a) hxa'
      have hax : a + (x - a) = x := by ring
      rw [hax] at h
      exact h
    · intro b hbR hba
      exact Set.indicator_of_notMem (fun hxb => Set.disjoint_left.mp (hRdisj b hbR a haR hba) hxb hxa) _
    · intro haR'
      exact (haR' haR).elim
  have hint : ∀ x₀ ∈ R,
      Integrable (fun x => (integerCoset K v x₀).indicator (fun _ => f x₀) x)
        (μ.restrict {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (1 : ℤ)}) := by
    intro x₀ _
    have hI : IntegrableOn (fun _ => f x₀) (integerCoset K v x₀) μ := by
      refine integrableOn_const ?_
      rw [measure_integerCoset]
      exact measure_integers_ne_top (μ := μ)
    exact (hI.integrable_indicator (measurableSet_integerCoset x₀)).integrableOn
  rw [setIntegral_congr_fun (measurableSet_closedBall_valued (WithZero.exp (1 : ℤ))) (fun x hx => hpt x hx),
    integral_finsetSum R hint, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x₀ hx₀ => setIntegral_indicator_integerCoset μ (hRball x₀ hx₀) (f x₀)

end Cosets

section OneLegs

private theorem nnreal_smul_eq_coe_mul (c : NNReal) (z : ℂ) : c • z = ((c : ℝ) : ℂ) * z := by
  rw [NNReal.smul_def, Complex.real_smul]

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem exists_valued_eq_exp_int (n : ℤ) : ∃ a : v.adicCompletion K, Valued.v a = WithZero.exp n :=
  ⟨(((NumberField.AdelicLevel.uniformizerUnit K v) ^ (-n) : (v.adicCompletion K)ˣ) : v.adicCompletion K), by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zsmul]
    congr 1
    simp⟩

variable {K v}

private theorem ne_zero_of_valued_eq_exp {w : v.adicCompletion K} {n : ℤ} (hw : Valued.v w = WithZero.exp n) : w ≠ 0 := by
  rintro rfl
  rw [map_zero] at hw
  exact WithZero.exp_ne_zero hw.symm

private theorem charExt_inv_eq_inv_of_ne_zero (χ : (v.adicCompletion K)ˣ →* ℂˣ) {x : v.adicCompletion K} (hx : x ≠ 0) :
    charExt χ x⁻¹ = (charExt χ x)⁻¹ := by
  have h := charExt_mul_eq_mul_of_ne_zero χ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, charExt_of_ne_zero χ one_ne_zero, Units.mk0_one, map_one, Units.val_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

private theorem charExt_ne_zero_of_ne_zero (χ : (v.adicCompletion K)ˣ →* ℂˣ) {x : v.adicCompletion K} (hx : x ≠ 0) :
    charExt χ x ≠ 0 := by
  rw [charExt_of_ne_zero χ hx]
  exact Units.ne_zero _

private theorem modulus_eq_of_valued_eq {a w : v.adicCompletion K} (h : Valued.v w = Valued.v a) (ha : a ≠ 0) :
    modulus w = modulus a := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  haveI := isAddHaarMeasure_selfDualHaarAt K v
  haveI := regular_selfDualHaarAt K v
  have hu : Valued.v (a⁻¹ * w) = 1 := by
    rw [Valuation.map_mul, map_inv₀, h, inv_mul_cancel₀]
    exact (Valuation.ne_zero_iff _).mpr ha
  calc modulus w = modulus (a * (a⁻¹ * w)) := by rw [mul_inv_cancel_left₀ ha]
    _ = modulus a * modulus (a⁻¹ * w) := modulus_mul _ _
    _ = modulus a := by rw [modulus_eq_one_of_valued_eq_one (μ := selfDualHaarAt K v) hu, mul_one]

private theorem coe_modulus_eq_norm (x : v.adicCompletion K) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm]

variable (K v) in

private theorem exists_norm_eq_of_valued_eq_exp (n : ℤ) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : v.adicCompletion K, Valued.v w = WithZero.exp n → ‖w‖ = r := by
  obtain ⟨a, ha⟩ := exists_valued_eq_exp_int K v n
  have ha0 : a ≠ 0 := ne_zero_of_valued_eq_exp ha
  refine ⟨‖a‖, norm_pos_iff.mpr ha0, fun w hw => ?_⟩
  rw [← coe_modulus_eq_norm, ← coe_modulus_eq_norm, modulus_eq_of_valued_eq (hw.trans ha.symm) ha0]

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

private theorem measurableSet_setOf_valued_eq_exp (n : ℤ) :
    MeasurableSet {w : v.adicCompletion K | Valued.v w = WithZero.exp n} := by
  obtain ⟨a, ha⟩ := exists_valued_eq_exp_int K v n
  have ha0 : a ≠ 0 := ne_zero_of_valued_eq_exp ha
  have hset : {w : v.adicCompletion K | Valued.v w = WithZero.exp n}
      = (fun w : v.adicCompletion K => a⁻¹ * w) ⁻¹' {u : v.adicCompletion K | Valued.v u = 1} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.map_mul, map_inv₀, ha]
    constructor
    · intro h
      rw [h, inv_mul_cancel₀ WithZero.exp_ne_zero]
    · intro h
      calc Valued.v w = WithZero.exp n * ((WithZero.exp n)⁻¹ * Valued.v w) :=
            (mul_inv_cancel_left₀ WithZero.exp_ne_zero _).symm
        _ = WithZero.exp n := by rw [h, mul_one]
  rw [hset]
  exact (by fun_prop : Continuous fun w : v.adicCompletion K => a⁻¹ * w).measurable measurableSet_unitShell

variable (K v)
variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ)

private def gaussShellAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (n : ℤ) (t : v.adicCompletion K) : ℂ :=
  ∫ w in {w : v.adicCompletion K | Valued.v w = WithZero.exp n}, ψ (t * w) * charExt χ w ∂μ

variable {K v μ ψ}

omit [BorelSpace (v.adicCompletion K)] [μ.IsAddHaarMeasure] in
private theorem gaussShellAt_def (χ : (v.adicCompletion K)ˣ →* ℂˣ) (n : ℤ) (t : v.adicCompletion K) :
    gaussShellAt K v μ ψ χ n t
      = ∫ w in {w : v.adicCompletion K | Valued.v w = WithZero.exp n}, ψ (t * w) * charExt χ w ∂μ :=
  rfl

private theorem gaussShellAt_eq_modulus_mul (χ : (v.adicCompletion K)ˣ →* ℂˣ) {n : ℤ} {a : v.adicCompletion K}
    (ha : Valued.v a = WithZero.exp n) (t : v.adicCompletion K) :
    gaussShellAt K v μ ψ χ n t = ((modulus a : ℝ) : ℂ) * (charExt χ a * gaussShell K v μ ψ χ (t * a)) := by
  have ha0 : a ≠ 0 := ne_zero_of_valued_eq_exp ha
  have hpre : (fun x : v.adicCompletion K => a * x) ⁻¹' {w : v.adicCompletion K | Valued.v w = WithZero.exp n}
      = {u : v.adicCompletion K | Valued.v u = 1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Valuation.map_mul, ha]
    constructor
    · intro h
      exact mul_left_cancel₀ WithZero.exp_ne_zero (h.trans (mul_one _).symm)
    · intro h
      rw [h, mul_one]
  have hlaw : ∫ x in {u : v.adicCompletion K | Valued.v u = 1}, ψ (t * (a * x)) * charExt χ (a * x) ∂μ
      = (modulus a)⁻¹ • gaussShellAt K v μ ψ χ n t := by
    have h := setIntegral_comp_mul_left_eq_modulus_inv_smul (μ := μ) ha0 (measurableSet_setOf_valued_eq_exp n)
      (fun w => ψ (t * w) * charExt χ w)
    rw [hpre] at h
    exact h
  have hunit : ∫ x in {u : v.adicCompletion K | Valued.v u = 1}, ψ (t * (a * x)) * charExt χ (a * x) ∂μ
      = charExt χ a * gaussShell K v μ ψ χ (t * a) := by
    rw [gaussShell_def, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_unitShell fun x hx => ?_
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    rw [charExt_mul_eq_mul_of_ne_zero χ ha0 hx0, ← mul_assoc t a x]
    ring
  calc gaussShellAt K v μ ψ χ n t = modulus a • ((modulus a)⁻¹ • gaussShellAt K v μ ψ χ n t) :=
        (smul_inv_smul₀ (modulus_ne_zero ha0) _).symm
    _ = ((modulus a : ℝ) : ℂ) * (charExt χ a * gaussShell K v μ ψ χ (t * a)) := by
        rw [← hlaw, hunit, nnreal_smul_eq_coe_mul]

private theorem exists_gaussShellAt_eq_ite [μ.Regular] {m : ℤ}
    (hψm : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp m → ψ x = 1)
    (hψm' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (m + 1) ∧ ψ x ≠ 1)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {f : ℕ} (hf : 1 ≤ f) (hχ : HasConductorExponentAt K v χ f) (n : ℤ) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ t : v.adicCompletion K,
      gaussShellAt K v μ ψ χ n t
        = if Valued.v t * WithZero.exp n = WithZero.exp (m + f) then (charExt χ t)⁻¹ * C else 0 := by
  obtain ⟨a, ha⟩ := exists_valued_eq_exp_int K v n
  have ha0 : a ≠ 0 := ne_zero_of_valued_eq_exp ha
  obtain ⟨c₀, hc₀⟩ := exists_valued_eq_exp_int K v (m + f)
  have hc₀0 : c₀ ≠ 0 := ne_zero_of_valued_eq_exp hc₀
  have hG₀ : gaussShell K v μ ψ χ c₀ ≠ 0 := gaussShell_ne_zero (μ := μ) hψm hψm' hf hχ hc₀
  refine ⟨((modulus a : ℝ) : ℂ) * charExt χ c₀ * gaussShell K v μ ψ χ c₀, ?_, fun t => ?_⟩
  · refine mul_ne_zero (mul_ne_zero ?_ (charExt_ne_zero_of_ne_zero χ hc₀0)) hG₀
    exact Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (modulus_ne_zero ha0))
  rw [gaussShellAt_eq_modulus_mul χ ha t]
  have hvta : Valued.v (t * a) = Valued.v t * WithZero.exp n := by rw [Valuation.map_mul, ha]
  split_ifs with hrad
  ·
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hrad
      exact WithZero.exp_ne_zero hrad.symm
    set u : v.adicCompletion K := c₀⁻¹ * (t * a) with hu_def
    have hu : Valued.v u = 1 := by
      rw [hu_def, Valuation.map_mul, map_inv₀, hc₀, hvta, hrad, inv_mul_cancel₀ WithZero.exp_ne_zero]
    have hta : t * a = c₀ * u := by rw [hu_def, mul_inv_cancel_left₀ hc₀0]
    have hlaw := charExt_mul_gaussShell_mul (μ := μ) ψ χ c₀ hu
    have hχu : charExt χ u = (charExt χ c₀)⁻¹ * (charExt χ t * charExt χ a) := by
      rw [hu_def, charExt_mul_eq_mul_of_ne_zero χ (inv_ne_zero hc₀0) (mul_ne_zero ht0 ha0),
        charExt_inv_eq_inv_of_ne_zero χ hc₀0, charExt_mul_eq_mul_of_ne_zero χ ht0 ha0]
    have hχc₀ : charExt χ c₀ ≠ 0 := charExt_ne_zero_of_ne_zero χ hc₀0
    have hχt : charExt χ t ≠ 0 := charExt_ne_zero_of_ne_zero χ ht0
    rw [hχu] at hlaw

    have e₁ : charExt χ c₀ * (charExt χ c₀)⁻¹ = 1 := mul_inv_cancel₀ hχc₀
    have e₂ : (charExt χ t)⁻¹ * charExt χ t = 1 := inv_mul_cancel₀ hχt
    rw [hta, ← hlaw]
    linear_combination (-(((modulus a : ℝ) : ℂ) * charExt χ a * gaussShell K v μ ψ χ (c₀ * u))) * e₁
      + (-(((modulus a : ℝ) : ℂ) * charExt χ a * gaussShell K v μ ψ χ (c₀ * u) * charExt χ c₀
          * (charExt χ c₀)⁻¹)) * e₂
  ·
    have hne : Valued.v (t * a) ≠ WithZero.exp (m + f) := by
      rw [hvta]
      exact hrad
    rw [gaussShell_eq_zero_of_valued_ne (μ := μ) hψm hψm' hf hχ hne, mul_zero, mul_zero]

private theorem setIntegral_addChar_neg_mul_charExt_sub_div_eq (χ : (v.adicCompletion K)ˣ →* ℂˣ) (n : ℤ)
    {x : v.adicCompletion K} (hx : x ≠ 0) (z : v.adicCompletion K) :
    ∫ y in {y : v.adicCompletion K | Valued.v (x * y - z) = WithZero.exp n},
        ψ (-y) * charExt χ ((x * y - z) / x) ∂μ
      = ((‖x‖⁻¹ : ℝ) : ℂ) * ψ (-(z / x)) * (charExt χ x)⁻¹ * gaussShellAt K v μ ψ χ n (-(1 / x)) := by

  set H : v.adicCompletion K → ℂ := fun s => ψ (-(x⁻¹ * s)) * charExt χ ((s - z) / x) with hH
  have hT : MeasurableSet {s : v.adicCompletion K | Valued.v (s - z) = WithZero.exp n} := by
    have : {s : v.adicCompletion K | Valued.v (s - z) = WithZero.exp n}
        = (fun s : v.adicCompletion K => s - z) ⁻¹' {w : v.adicCompletion K | Valued.v w = WithZero.exp n} := rfl
    rw [this]
    exact (by fun_prop : Continuous fun s : v.adicCompletion K => s - z).measurable
      (measurableSet_setOf_valued_eq_exp n)
  have hstep1 : ∫ y in {y : v.adicCompletion K | Valued.v (x * y - z) = WithZero.exp n},
        ψ (-y) * charExt χ ((x * y - z) / x) ∂μ
      = ∫ y in (fun y : v.adicCompletion K => x * y) ⁻¹'
          {s : v.adicCompletion K | Valued.v (s - z) = WithZero.exp n}, H (x * y) ∂μ := by
    refine setIntegral_congr_fun ((by fun_prop : Continuous fun y : v.adicCompletion K => x * y - z).measurable
      (measurableSet_setOf_valued_eq_exp n)) fun y _ => ?_
    simp only [hH, inv_mul_cancel_left₀ hx]
  rw [hstep1, setIntegral_comp_mul_left_eq_modulus_inv_smul (μ := μ) hx hT H]

  have hstep2 : ∫ s in {s : v.adicCompletion K | Valued.v (s - z) = WithZero.exp n}, H s ∂μ
      = ∫ w in {w : v.adicCompletion K | Valued.v w = WithZero.exp n}, H (z + w) ∂μ := by
    have hpres := measurePreserving_add_left μ z
    have hemb : MeasurableEmbedding (fun w : v.adicCompletion K => z + w) :=
      (Homeomorph.addLeft z).measurableEmbedding
    have hAB : (fun w : v.adicCompletion K => z + w) ⁻¹' {s : v.adicCompletion K | Valued.v (s - z) = WithZero.exp n}
        = {w : v.adicCompletion K | Valued.v w = WithZero.exp n} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_setOf_eq, add_sub_cancel_left]
    rw [← hpres.setIntegral_preimage_emb hemb H, hAB]
  rw [hstep2]

  have hstep3 : ∫ w in {w : v.adicCompletion K | Valued.v w = WithZero.exp n}, H (z + w) ∂μ
      = ψ (-(z / x)) * (charExt χ x)⁻¹ * gaussShellAt K v μ ψ χ n (-(1 / x)) := by
    rw [gaussShellAt_def, mul_assoc, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_setOf_valued_eq_exp n) fun w hw => ?_
    have hw0 : w ≠ 0 := ne_zero_of_valued_eq_exp hw
    have harg : -(x⁻¹ * (z + w)) = -(1 / x) * w + -(z / x) := by
      simp only [div_eq_mul_inv]
      ring
    simp only [hH, add_sub_cancel_left]
    rw [harg, AddChar.map_add_eq_mul, div_eq_mul_inv w x, charExt_mul_eq_mul_of_ne_zero χ hw0 (inv_ne_zero hx),
      charExt_inv_eq_inv_of_ne_zero χ hx]
    ring
  rw [hstep3, nnreal_smul_eq_coe_mul, NNReal.coe_inv, coe_modulus_eq_norm]
  ring

end OneLegs

section OneLegsRat

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem psiLocal_rat_level_zero :
    (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (0 : ℤ) → NumberField.StandardAddChar.psiLocal ℚ v x = 1) ∧
      ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧
        NumberField.StandardAddChar.psiLocal ℚ v x ≠ 1 := by
  have h := forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v (NumberField.StandardAddChar.psiLocal ℚ v)
    ⟨0, fun x hx => psiLocal_eq_one_of_mem_integers ℚ v x
      (by simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using hx)⟩
    (psiLocal_ne_one ℚ v)
  rwa [addCharLevel_psiLocal_rat v] at h

variable {v} [MeasurableSpace (v.adicCompletion ℚ)] [BorelSpace (v.adicCompletion ℚ)]
  {μ : Measure (v.adicCompletion ℚ)} [μ.IsAddHaarMeasure] [μ.Regular]

private theorem exists_gaussShellAt_psiLocal_rat_eq_ite {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ}
    (hχ : HasConductorExponentAt ℚ v χ a) (ha : 1 ≤ a) (n : ℤ) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ t : v.adicCompletion ℚ,
      gaussShellAt ℚ v μ (NumberField.StandardAddChar.psiLocal ℚ v) χ n t
        = if Valued.v t * WithZero.exp n = WithZero.exp (a : ℤ) then (charExt χ t)⁻¹ * C else 0 := by
  obtain ⟨h0, h1⟩ := psiLocal_rat_level_zero v
  obtain ⟨C, hC, hCt⟩ := exists_gaussShellAt_eq_ite (μ := μ) h0 h1 ha hχ n
  refine ⟨C, hC, fun t => ?_⟩
  rw [hCt t, zero_add]

end OneLegsRat

end LanglandsTunnell.TateLocal

end

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def shellWeight (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (e : ℤ) (t : v.adicCompletion ℚ) : ℂ :=
  if Valued.v t = WithZero.exp e then charExt ξ t else 0

private theorem shellWeight_of_valued_eq (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {e : ℤ} {t : v.adicCompletion ℚ}
    (ht : Valued.v t = WithZero.exp e) : shellWeight v ξ e t = charExt ξ t := by
  simp [shellWeight, ht]

private theorem shellWeight_of_valued_ne (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {e : ℤ} {t : v.adicCompletion ℚ}
    (ht : Valued.v t ≠ WithZero.exp e) : shellWeight v ξ e t = 0 := by
  simp [shellWeight, ht]

private theorem shellWeight_units_mul (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (e : ℤ) {u : (v.adicCompletion ℚ)ˣ}
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) (t : v.adicCompletion ℚ) :
    shellWeight v ξ e ((u : v.adicCompletion ℚ) * t) = (ξ u : ℂ) * shellWeight v ξ e t := by
  have hv : Valued.v ((u : v.adicCompletion ℚ) * t) = Valued.v t := by rw [map_mul, hu, one_mul]
  by_cases ht : Valued.v t = WithZero.exp e
  · rw [shellWeight_of_valued_eq v ξ (hv.trans ht), shellWeight_of_valued_eq v ξ ht, charExt_units_mul]
  · rw [shellWeight_of_valued_ne v ξ (hv.symm ▸ ht), shellWeight_of_valued_ne v ξ ht, mul_zero]

private theorem shellWeight_higherUnits_mul (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c) (e : ℤ) {u : (v.adicCompletion ℚ)ˣ} (hu : u ∈ higherUnitsAt ℚ v c)
    (t : v.adicCompletion ℚ) :
    shellWeight v ξ e ((u : v.adicCompletion ℚ) * t) = shellWeight v ξ e t := by
  rw [shellWeight_units_mul v ξ e ((mem_higherUnitsAt_iff ℚ v).mp hu).1, hξ.1 u hu, Units.val_one, one_mul]

private theorem shellWeight_add_of_valued_le (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c) (hc : 1 ≤ c) {e : ℤ} {t s : v.adicCompletion ℚ}
    (ht : Valued.v t = WithZero.exp e) (hs : Valued.v s ≤ WithZero.exp (e - c)) :
    shellWeight v ξ e (t + s) = shellWeight v ξ e t := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    exact WithZero.exp_ne_zero ht.symm
  have hw : Valued.v (s / t) ≤ WithZero.exp (-(c : ℤ)) := by
    rw [map_div₀, ht, div_le_iff₀ (by simp), ← WithZero.exp_add]
    simpa [sub_eq_add_neg, add_comm] using hs
  have hw1 : Valued.v (s / t) < 1 := by
    refine lt_of_le_of_lt hw ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hu1 : Valued.v (1 + s / t) = 1 := Valuation.map_one_add_of_lt _ hw1
  have hne : (1 + s / t) ≠ 0 := by
    intro h
    rw [h, map_zero] at hu1
    exact zero_ne_one hu1
  set u : (v.adicCompletion ℚ)ˣ := Units.mk0 _ hne with hu_def
  have hu : u ∈ higherUnitsAt ℚ v c := by
    refine (mem_higherUnitsAt_iff ℚ v).mpr ⟨hu1, Or.inr ?_⟩
    simpa [hu_def] using hw
  have hts : t + s = (u : v.adicCompletion ℚ) * t := by
    simp only [hu_def, Units.val_mk0]
    field_simp
  rw [hts, shellWeight_higherUnits_mul v ξ hξ e hu]

private theorem valued_det_le_one_of_entries {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)}
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) : Valued.v M.det ≤ 1 := by
  rw [Matrix.det_fin_three]
  have h3 : ∀ i j k l m n : Fin 3, Valued.v (M i j * M k l * M m n) ≤ 1 := fun i j k l m n => by
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' (hM i j) (hM k l)) (hM m n)

  exact Valuation.map_sub_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sub_le _
    (Valuation.map_sub_le _ (h3 0 0 1 1 2 2) (h3 0 0 1 2 2 1)) (h3 0 1 1 0 2 2)) (h3 0 1 1 2 2 0))
    (h3 0 2 1 0 2 1)) (h3 0 2 1 1 2 0)

private theorem valued_det_eq_one_of_mem_localMaximalCompact3 {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) = 1 := by
  obtain ⟨hk₁, hk₂⟩ := (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk
  have hd : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) ≤ 1 :=
    valued_det_le_one_of_entries v hk₁
  have hd' : Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) ≤ 1 :=
    valued_det_le_one_of_entries v hk₂
  have hprod : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) *
      Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm hd ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ * _ := hprod.symm
    _ ≤ Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) * 1 := mul_le_mul' le_rfl hd'
    _ = _ := mul_one _

private theorem converseCongruenceSet3_mul_mem {a : ℕ} {k k' : LocalGL3 v} (hk : k ∈ converseCongruenceSet3 v a)
    (hk' : k' ∈ converseCongruenceSet3 v a) : k * k' ∈ converseCongruenceSet3 v a := by
  obtain ⟨hkK, h01, h20, h21⟩ := hk
  obtain ⟨hkK', h01', h20', h21'⟩ := hk'
  have hi := ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hkK).1
  have hi' := ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hkK').1
  have h2a : WithZero.exp (-(2 * (a : ℤ))) ≤ WithZero.exp (-(a : ℤ)) := by
    rw [WithZero.exp_le_exp]
    omega

  have hL : ∀ {x y : v.adicCompletion ℚ} {d : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ 1 → Valued.v y ≤ d → Valued.v (x * y) ≤ d :=
    fun hx hy => by rw [map_mul]; simpa using mul_le_mul' hx hy
  have hR : ∀ {x y : v.adicCompletion ℚ} {d : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ d → Valued.v y ≤ 1 → Valued.v (x * y) ≤ d :=
    fun hx hy => by rw [map_mul]; simpa using mul_le_mul' hx hy
  refine ⟨mul_mem hkK hkK', ?_, ?_, ?_⟩ <;>
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  · exact Valuation.map_add_le _ (Valuation.map_add_le _ (hL (hi 0 0) h01') (hR h01 (hi' 1 1)))
      (le_trans (hL (hi 0 2) h21') h2a)
  · exact Valuation.map_add_le _ (Valuation.map_add_le _ (hR h20 (hi' 0 0)) (le_trans (hR h21 (hi' 1 0)) h2a))
      (hL (hi 2 2) h20')
  · refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (hR h21 (hi' 1 1))) (hL (hi 2 2) h21')
    rw [map_mul]
    calc Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0) *
          Valued.v ((k' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1)
        ≤ WithZero.exp (-(a : ℤ)) * WithZero.exp (-(a : ℤ)) := mul_le_mul' h20 h01'
      _ = WithZero.exp (-(2 * (a : ℤ))) := by rw [← WithZero.exp_add]; ring_nf

private theorem converseCongruenceSet3_inv_mem {a : ℕ} {k : LocalGL3 v} (hk : k ∈ converseCongruenceSet3 v a) :
    k⁻¹ ∈ converseCongruenceSet3 v a := by
  obtain ⟨hkK, h01, h20, h21⟩ := hk
  have hi := ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hkK).1
  have hdet := valued_det_eq_one_of_mem_localMaximalCompact3 v hkK
  have h2a : WithZero.exp (-(2 * (a : ℤ))) ≤ WithZero.exp (-(a : ℤ)) := by
    rw [WithZero.exp_le_exp]
    omega
  have hL : ∀ {x y : v.adicCompletion ℚ} {d : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ 1 → Valued.v y ≤ d → Valued.v (x * y) ≤ d :=
    fun hx hy => by rw [map_mul]; simpa using mul_le_mul' hx hy
  have hR : ∀ {x y : v.adicCompletion ℚ} {d : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ d → Valued.v y ≤ 1 → Valued.v (x * y) ≤ d :=
    fun hx hy => by rw [map_mul]; simpa using mul_le_mul' hx hy

  have hinv : ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det)⁻¹ •
        (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  have hdinv : Valued.v (((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det)⁻¹) ≤ 1 := by
    rw [map_inv₀, hdet, inv_one]
  refine ⟨inv_mem hkK, ?_, ?_, ?_⟩ <;>
    rw [hinv, Matrix.smul_apply, smul_eq_mul] <;> refine hL hdinv ?_ <;>
    simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one]
  ·
    refine Valuation.map_add_le _ ?_ (le_trans (hL (hi 0 2) h21) h2a)
    rw [Valuation.map_neg]
    exact hR h01 (hi 2 2)
  ·
    exact Valuation.map_sub_le _ (le_trans (hL (hi 1 0) h21) h2a) (hL (hi 1 1) h20)
  ·
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Valuation.map_neg]
      exact hL (hi 0 0) h21
    · rw [map_mul]
      calc Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1) *
            Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0)
          ≤ WithZero.exp (-(a : ℤ)) * WithZero.exp (-(a : ℤ)) := mul_le_mul' h01 h20
        _ = WithZero.exp (-(2 * (a : ℤ))) := by rw [← WithZero.exp_add]; ring_nf

private def converseCongruenceSubgroup3 (a : ℕ) : Subgroup (LocalGL3 v) where
  carrier := converseCongruenceSet3 v a
  one_mem' := one_mem_converseCongruenceSet3 v a
  mul_mem' := converseCongruenceSet3_mul_mem v
  inv_mem' := converseCongruenceSet3_inv_mem v

private theorem mem_converseCongruenceSubgroup3_iff (a : ℕ) (k : LocalGL3 v) :
    k ∈ converseCongruenceSubgroup3 v a ↔ k ∈ converseCongruenceSet3 v a :=
  Iff.rfl

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem rightMinor_mul (g k : LocalGL3 v) :
    rightMinor v (g * k) =
      lowerMinor v g * (gl3Entry v k 0 1 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 1) +
        outerMinor v g * (gl3Entry v k 0 1 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 1) +
          rightMinor v g * (gl3Entry v k 1 1 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 1) := by
  simp only [rightMinor, lowerMinor, outerMinor, gl3Entry_mul]
  ring

private def cellInvariant (g : LocalGL3 v) : v.adicCompletion ℚ :=
  cellRatio v g 1 - cellRatio v g 0 * cellRatio v g 2

private theorem cellRatio_zero (g : LocalGL3 v) : cellRatio v g 0 = gl3Entry v g 2 1 / cornerEntry v g := rfl

private theorem cellRatio_one (g : LocalGL3 v) : cellRatio v g 1 = gl3Entry v g 2 2 / cornerEntry v g := rfl

private theorem cellRatio_two (g : LocalGL3 v) : cellRatio v g 2 = outerMinor v g / lowerMinor v g := rfl

private theorem cellInvariant_eq_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) :
    cellInvariant v g = -(rightMinor v g / lowerMinor v g) := by
  have h := cornerEntry_mul_rightMinor v g
  unfold cellInvariant
  rw [cellRatio_zero, cellRatio_one, cellRatio_two]
  field_simp
  linear_combination h

private theorem charExt_mul_of_ne_zero (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x y : v.adicCompletion ℚ} (hx : x ≠ 0)
    (_hy : y ≠ 0) : charExt ξ (x * y) = charExt ξ x * charExt ξ y := by
  have hxy : x * y = ((Units.mk0 x hx : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y := by simp
  rw [hxy, charExt_units_mul, charExt_of_ne_zero ξ hx]

private theorem charExt_one_add_of_valued_le (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c) (hc : 1 ≤ c) {w : v.adicCompletion ℚ}
    (hw : Valued.v w ≤ WithZero.exp (-(c : ℤ))) : charExt ξ (1 + w) = 1 := by
  have hw1 : Valued.v w < 1 := by
    refine lt_of_le_of_lt hw ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hu1 : Valued.v (1 + w) = 1 := Valuation.map_one_add_of_lt _ hw1
  have hne : (1 + w) ≠ 0 := by
    intro h
    rw [h, map_zero] at hu1
    exact zero_ne_one hu1
  have hu : Units.mk0 (1 + w) hne ∈ higherUnitsAt ℚ v c :=
    (mem_higherUnitsAt_iff ℚ v).mpr ⟨hu1, Or.inr (by simpa using hw)⟩
  rw [charExt_of_ne_zero ξ hne, hξ.1 _ hu, Units.val_one]

private theorem hasConductorExponentAt_inv' {ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c) : HasConductorExponentAt ℚ v ξ⁻¹ c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · show (ξ u)⁻¹ = 1
    rw [hξ.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := hξ.2 m hm
    refine ⟨u, hu, ?_⟩
    show (ξ u)⁻¹ ≠ 1
    exact fun h => hne (inv_eq_one.mp h)

private theorem norm_eq_one_of_valued_eq_one {x : v.adicCompletion ℚ} (hx : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, hx, map_one, NNReal.coe_one]

private def conductorDatum (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ) (r : Fin 3 → v.adicCompletion ℚ) :
    ℂ :=
  (if Valued.v (r 2) ≤ 1 then (1 : ℂ) else 0) *
    (if Valued.v (r 1) ≤ WithZero.exp (-(a₂ : ℤ)) then (1 : ℂ) else 0) *
      shellWeight v (ν 0)⁻¹ (-((a₁ : ℤ) + a₂)) (r 1 - r 0 * r 2) * shellWeight v (ν 1)⁻¹ (-(a₂ : ℤ)) (r 0)

private theorem conductorDatum_support (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)
    {r : Fin 3 → v.adicCompletion ℚ} (hr : conductorDatum v ν a₁ a₂ r ≠ 0) :
    Valued.v (r 2) ≤ 1 ∧ Valued.v (r 1) ≤ WithZero.exp (-(a₂ : ℤ)) ∧
      Valued.v (r 1 - r 0 * r 2) = WithZero.exp (-((a₁ : ℤ) + a₂)) ∧ Valued.v (r 0) = WithZero.exp (-(a₂ : ℤ)) := by
  unfold conductorDatum at hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    rw [if_neg h] at hr
    simp at hr
  · by_contra h
    rw [if_neg h] at hr
    simp at hr
  · by_contra h
    rw [shellWeight_of_valued_ne v _ h] at hr
    simp at hr
  · by_contra h
    rw [shellWeight_of_valued_ne v _ h] at hr
    simp at hr

private theorem conductorDatum_apply_of_support (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)
    {r : Fin 3 → v.adicCompletion ℚ} (h2 : Valued.v (r 2) ≤ 1) (h1 : Valued.v (r 1) ≤ WithZero.exp (-(a₂ : ℤ)))
    (hQ : Valued.v (r 1 - r 0 * r 2) = WithZero.exp (-((a₁ : ℤ) + a₂)))
    (h0 : Valued.v (r 0) = WithZero.exp (-(a₂ : ℤ))) :
    conductorDatum v ν a₁ a₂ r = charExt (ν 0)⁻¹ (r 1 - r 0 * r 2) * charExt (ν 1)⁻¹ (r 0) := by
  unfold conductorDatum
  rw [if_pos h2, if_pos h1, shellWeight_of_valued_eq v _ hQ, shellWeight_of_valued_eq v _ h0]
  ring

private def cellSupport (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ) : Set (LocalGL3 v) :=
  {y | y ∈ bigCell3 v ∧ conductorDatum v ν a₁ a₂ (cellRatio v y) ≠ 0}

private theorem cellSectionOf_conductorDatum_eq_zero_of_notMem (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)
    {y : LocalGL3 v} (hy : y ∉ cellSupport v ν a₁ a₂) : cellSectionOf v ν (conductorDatum v ν a₁ a₂) y = 0 := by
  by_cases hc : y ∈ bigCell3 v
  · have hΦ : conductorDatum v ν a₁ a₂ (cellRatio v y) = 0 := by
      by_contra h
      exact hy ⟨hc, h⟩
    rw [cellSectionOf_apply_of_mem v _ _ hc, hΦ, mul_zero]
  · exact cellSectionOf_apply_of_notMem v _ _ hc

private theorem cellSectionOf_conductorDatum_apply_of_mem (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)
    {y : LocalGL3 v} (hy : y ∈ cellSupport v ν a₁ a₂) :
    cellSectionOf v ν (conductorDatum v ν a₁ a₂) y = cellValue v ν y * conductorDatum v ν a₁ a₂ (cellRatio v y) :=
  cellSectionOf_apply_of_mem v _ _ hy.1

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_eq_mul_one_add_of_valued_sub_le {M E : v.adicCompletion ℚ} (hM : M ≠ 0) {c : ℕ}
    (h : Valued.v (E - M) ≤ Valued.v M * WithZero.exp (-(c : ℤ))) :
    ∃ w : v.adicCompletion ℚ, E = M * (1 + w) ∧ Valued.v w ≤ WithZero.exp (-(c : ℤ)) := by
  refine ⟨(E - M) / M, by field_simp; ring, ?_⟩
  rw [map_div₀, div_le_iff₀ ((Valuation.pos_iff _).mpr hM)]
  simpa [mul_comm] using h

private theorem charExt_ne_zero (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    charExt ξ x ≠ 0 := by
  rw [charExt_of_ne_zero ξ hx]
  exact Units.ne_zero _

private theorem charExt_inv_apply (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (x : v.adicCompletion ℚ) :
    charExt ξ⁻¹ x = (charExt ξ x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero ξ hx]
    show (((ξ (Units.mk0 x hx))⁻¹ : ℂˣ) : ℂ) = _
    rw [Units.val_inv_eq_inv_val]

private theorem charExt_mul_one_add (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ} (hξ : HasConductorExponentAt ℚ v ξ c)
    (hc : 1 ≤ c) {M w : v.adicCompletion ℚ} (hM : M ≠ 0) (hw : Valued.v w ≤ WithZero.exp (-(c : ℤ))) :
    charExt ξ (M * (1 + w)) = charExt ξ M := by
  have h1 : (1 + w) ≠ 0 := by
    intro h
    have := charExt_one_add_of_valued_le v ξ hξ hc hw
    rw [h, charExt_zero] at this
    exact zero_ne_one this
  rw [charExt_mul_of_ne_zero v ξ hM h1, charExt_one_add_of_valued_le v ξ hξ hc hw, mul_one]

private theorem charExt_mul_one_add_of_le (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c' c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c') (hc' : 1 ≤ c') (hcc : c' ≤ c) {M w : v.adicCompletion ℚ} (hM : M ≠ 0)
    (hw : Valued.v w ≤ WithZero.exp (-(c : ℤ))) : charExt ξ (M * (1 + w)) = charExt ξ M :=
  charExt_mul_one_add v ξ hξ hc' hM (hw.trans (by rw [WithZero.exp_le_exp]; omega))

private theorem valued_one_add_eq_one {w : v.adicCompletion ℚ} {c : ℕ} (hc : 1 ≤ c)
    (hw : Valued.v w ≤ WithZero.exp (-(c : ℤ))) : Valued.v (1 + w) = 1 := by
  refine Valuation.map_one_add_of_lt _ (lt_of_le_of_lt hw ?_)
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private structure IsOppositeCongruence (a : ℕ) (k : LocalGL3 v) : Prop where
  mem : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v
  h21 : Valued.v (gl3Entry v k 2 1) ≤ WithZero.exp (-(a : ℤ))
  h02 : Valued.v (gl3Entry v k 0 2) ≤ WithZero.exp (-(a : ℤ))
  h01 : Valued.v (gl3Entry v k 0 1) ≤ WithZero.exp (-(2 * (a : ℤ)))

private theorem antidiagonal3_mul_antidiagonal3 : antidiagonal3 v * antidiagonal3 v = 1 := by
  ext i j
  rw [Units.val_mul, antidiagonal3_coe, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem antidiagonal3_mem_localMaximalCompact3 : antidiagonal3 v ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hinv : (antidiagonal3 v)⁻¹ = antidiagonal3 v := inv_eq_of_mul_eq_one_right (antidiagonal3_mul_antidiagonal3 v)
  refine (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [antidiagonal3_coe]
    fin_cases i <;> fin_cases j <;> simp
  · rw [hinv, antidiagonal3_coe]
    fin_cases i <;> fin_cases j <;> simp

private theorem gl3Entry_antidiagonal3_mul_mul_antidiagonal3 (k : LocalGL3 v) (i j : Fin 3) :
    gl3Entry v (antidiagonal3 v * k * antidiagonal3 v) i j = gl3Entry v k (Fin.rev i) (Fin.rev j) := by
  simp only [gl3Entry, Units.val_mul, antidiagonal3_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

private theorem isOppositeCongruence_conj {a : ℕ} {k : LocalGL3 v} (hk : k ∈ converseCongruenceSet3 v a) :
    IsOppositeCongruence v a (antidiagonal3 v * k * antidiagonal3 v) := by
  obtain ⟨hkK, h01, h20, h21⟩ := hk
  have hw := antidiagonal3_mem_localMaximalCompact3 v
  refine ⟨mul_mem (mul_mem hw hkK) hw, ?_, ?_, ?_⟩ <;> rw [gl3Entry_antidiagonal3_mul_mul_antidiagonal3]
  · exact h01
  · exact h20
  · exact h21

private theorem gl3Entry_conj_zero_zero (k : LocalGL3 v) :
    gl3Entry v (antidiagonal3 v * k * antidiagonal3 v) 0 0 = gl3Entry v k 2 2 := by
  rw [gl3Entry_antidiagonal3_mul_mul_antidiagonal3]
  rfl

private theorem IsOppositeCongruence.diag_valued {a : ℕ} (ha : 1 ≤ a) {k : LocalGL3 v} (hk : IsOppositeCongruence v a k) :
    Valued.v (gl3Entry v k 0 0) = 1 ∧ Valued.v (gl3Entry v k 1 1) = 1 ∧ Valued.v (gl3Entry v k 2 2) = 1 := by
  have hi := ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk.mem).1
  have hdet : Valued.v (gl3Det v k) = 1 := valued_det_eq_one_of_mem_localMaximalCompact3 v hk.mem
  have ha' : WithZero.exp (-(a : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have h2a : WithZero.exp (-(2 * (a : ℤ))) ≤ WithZero.exp (-(a : ℤ)) := by
    rw [WithZero.exp_le_exp]
    omega

  have hL : ∀ {x y : v.adicCompletion ℚ} {d : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ 1 → Valued.v y ≤ d → Valued.v (x * y) ≤ d :=
    fun hx hy => by rw [map_mul]; simpa using mul_le_mul' hx hy
  have hrest : Valued.v (gl3Det v k - gl3Entry v k 0 0 * gl3Entry v k 1 1 * gl3Entry v k 2 2) ≤
      WithZero.exp (-(a : ℤ)) := by
    have hexp : gl3Det v k - gl3Entry v k 0 0 * gl3Entry v k 1 1 * gl3Entry v k 2 2 =
        -(gl3Entry v k 0 0 * (gl3Entry v k 1 2 * gl3Entry v k 2 1)) -
          gl3Entry v k 1 0 * (gl3Entry v k 2 2 * gl3Entry v k 0 1) +
            gl3Entry v k 1 2 * (gl3Entry v k 2 0 * gl3Entry v k 0 1) +
              gl3Entry v k 1 0 * (gl3Entry v k 2 1 * gl3Entry v k 0 2) -
                gl3Entry v k 1 1 * (gl3Entry v k 2 0 * gl3Entry v k 0 2) := by
      simp only [gl3Det, gl3Entry, Matrix.det_fin_three]
      ring
    rw [hexp]
    refine Valuation.map_sub_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sub_le _ ?_ ?_) ?_)
      ?_) ?_
    · rw [Valuation.map_neg]
      exact hL (hi 0 0) (hL (hi 1 2) hk.h21)
    · exact hL (hi 1 0) (le_trans (hL (hi 2 2) hk.h01) h2a)
    · exact hL (hi 1 2) (le_trans (hL (hi 2 0) hk.h01) h2a)
    · exact hL (hi 1 0) (hL (hi 2 1) hk.h02)
    · exact hL (hi 1 1) (hL (hi 2 0) hk.h02)
  have hlead : Valued.v (gl3Entry v k 0 0 * gl3Entry v k 1 1 * gl3Entry v k 2 2) = 1 := by
    have hrest' : Valued.v (gl3Det v k - gl3Entry v k 0 0 * gl3Entry v k 1 1 * gl3Entry v k 2 2) <
        Valued.v (gl3Det v k) := by
      rw [hdet]
      exact lt_of_le_of_lt hrest ha'
    have := Valuation.map_sub_eq_of_lt_left _ hrest'
    rw [hdet] at this

    simpa using this
  rw [map_mul, map_mul] at hlead
  have h00 := hi 0 0
  have h11 := hi 1 1
  have h22 := hi 2 2
  refine ⟨le_antisymm h00 ?_, le_antisymm h11 ?_, le_antisymm h22 ?_⟩
  · calc (1 : WithZero (Multiplicative ℤ)) = _ := hlead.symm
      _ ≤ Valued.v (gl3Entry v k 0 0) * 1 * 1 := mul_le_mul' (mul_le_mul' le_rfl h11) h22
      _ = _ := by simp
  · calc (1 : WithZero (Multiplicative ℤ)) = _ := hlead.symm
      _ ≤ 1 * Valued.v (gl3Entry v k 1 1) * 1 := mul_le_mul' (mul_le_mul' h00 le_rfl) h22
      _ = _ := by simp
  · calc (1 : WithZero (Multiplicative ℤ)) = _ := hlead.symm
      _ ≤ 1 * 1 * Valued.v (gl3Entry v k 2 2) := mul_le_mul' (mul_le_mul' h00 h11) le_rfl
      _ = _ := by simp

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section DatumRegularity

private theorem eventually_valued_sub_le (t : v.adicCompletion ℚ) (k : ℤ) :
    ∀ᶠ t' in nhds t, Valued.v (t' - t) ≤ WithZero.exp (-k) :=
  (isClopen_setOf_valued_sub_le v t k).isOpen.mem_nhds (by simp)

private theorem isLocallyConstant_shellWeight (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c) (hc : 1 ≤ c) (e : ℤ) : IsLocallyConstant (shellWeight v ξ e) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun t => ?_
  by_cases ht0 : t = 0
  · subst ht0
    filter_upwards [eventually_valued_sub_le v 0 (1 - e)] with t' ht'
    rw [sub_zero] at ht'
    have h0 : shellWeight v ξ e (0 : v.adicCompletion ℚ) = 0 :=
      shellWeight_of_valued_ne v ξ (by rw [map_zero]; exact fun h => WithZero.exp_ne_zero h.symm)
    rw [h0]
    refine shellWeight_of_valued_ne v ξ fun h => ?_
    rw [h, WithZero.exp_le_exp] at ht'
    omega
  · have hvt : Valued.v t = WithZero.exp (WithZero.log (Valued.v t)) :=
      (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr ht0)).symm
    filter_upwards [eventually_valued_sub_le v t ((c : ℤ) - WithZero.log (Valued.v t))] with t' ht'
    have ht'' : Valued.v (t' - t) ≤ Valued.v t * WithZero.exp (-(c : ℤ)) := by
      rw [hvt, ← WithZero.exp_add]
      refine ht'.trans (le_of_eq ?_)
      congr 1
      ring
    obtain ⟨w, rfl, hw⟩ := exists_eq_mul_one_add_of_valued_sub_le v ht0 ht''
    have hv : Valued.v (t * (1 + w)) = Valued.v t := by
      rw [map_mul, valued_one_add_eq_one v hc hw, mul_one]
    by_cases hte : Valued.v t = WithZero.exp e
    · rw [shellWeight_of_valued_eq v ξ (hv.trans hte), shellWeight_of_valued_eq v ξ hte,
        charExt_mul_one_add v ξ hξ hc ht0 hw]
    · rw [shellWeight_of_valued_ne v ξ (hv.trans_ne hte), shellWeight_of_valued_ne v ξ hte]

private theorem isLocallyConstant_ballIndicator (k : ℤ) :
    IsLocallyConstant fun t : v.adicCompletion ℚ => if Valued.v t ≤ WithZero.exp (-k) then (1 : ℂ) else 0 := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun t => ?_
  have hB := isClopen_setOf_valued_sub_le v 0 k
  by_cases ht : Valued.v t ≤ WithZero.exp (-k)
  · have hmem : t ∈ {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-k)} := by simpa using ht
    filter_upwards [hB.isOpen.mem_nhds hmem] with t' ht'
    simp only [sub_zero] at ht'
    rw [if_pos ht', if_pos ht]
  · have hmem : t ∈ {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-k)}ᶜ := by simpa using ht
    filter_upwards [hB.compl.isOpen.mem_nhds hmem] with t' ht'
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, sub_zero] at ht'
    rw [if_neg ht', if_neg ht]

private theorem isLocallyConstant_unitBallIndicator :
    IsLocallyConstant fun t : v.adicCompletion ℚ => if Valued.v t ≤ 1 then (1 : ℂ) else 0 := by
  have h := isLocallyConstant_ballIndicator v 0
  simpa only [neg_zero, WithZero.exp_zero] using h

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)

private theorem isLocallyConstant_conductorDatum {c₀ c₁ : ℕ} (hν₀ : HasConductorExponentAt ℚ v (ν 0) c₀) (h₀ : 1 ≤ c₀)
    (hν₁ : HasConductorExponentAt ℚ v (ν 1) c₁) (h₁ : 1 ≤ c₁) : IsLocallyConstant (conductorDatum v ν a₁ a₂) := by
  have hproj : ∀ i : Fin 3, Continuous fun r : Fin 3 → v.adicCompletion ℚ => r i := fun i => continuous_apply i
  have hQ : Continuous fun r : Fin 3 → v.adicCompletion ℚ => r 1 - r 0 * r 2 :=
    (hproj 1).sub ((hproj 0).mul (hproj 2))
  have h2 : IsLocallyConstant fun r : Fin 3 → v.adicCompletion ℚ =>
      if Valued.v (r 2) ≤ 1 then (1 : ℂ) else 0 :=
    (isLocallyConstant_unitBallIndicator v).comp_continuous (hproj 2)
  have h1 : IsLocallyConstant fun r : Fin 3 → v.adicCompletion ℚ =>
      if Valued.v (r 1) ≤ WithZero.exp (-(a₂ : ℤ)) then (1 : ℂ) else 0 :=
    (isLocallyConstant_ballIndicator v a₂).comp_continuous (hproj 1)
  have hw0 : IsLocallyConstant fun r : Fin 3 → v.adicCompletion ℚ =>
      shellWeight v (ν 0)⁻¹ (-((a₁ : ℤ) + a₂)) (r 1 - r 0 * r 2) :=
    (isLocallyConstant_shellWeight v _ (hasConductorExponentAt_inv' v hν₀) h₀ _).comp_continuous hQ
  have hw1 : IsLocallyConstant fun r : Fin 3 → v.adicCompletion ℚ => shellWeight v (ν 1)⁻¹ (-(a₂ : ℤ)) (r 0) :=
    (isLocallyConstant_shellWeight v _ (hasConductorExponentAt_inv' v hν₁) h₁ _).comp_continuous (hproj 0)
  exact ((h2.mul h1).mul hw0).mul hw1

private theorem hasCompactSupport_conductorDatum : HasCompactSupport (conductorDatum v ν a₁ a₂) := by
  refine HasCompactSupport.intro (K := Set.pi Set.univ
    ![{t : v.adicCompletion ℚ | Valued.v (t - 0) ≤ WithZero.exp (-(a₂ : ℤ))},
      {t : v.adicCompletion ℚ | Valued.v (t - 0) ≤ WithZero.exp (-(a₂ : ℤ))},
      {t : v.adicCompletion ℚ | Valued.v t ≤ 1}]) (isCompact_univ_pi fun i => ?_) fun r hr => ?_
  · fin_cases i
    · exact isCompact_setOf_valued_sub_le v 0 a₂
    · exact isCompact_setOf_valued_sub_le v 0 a₂
    · exact isCompact_setOf_valued_le_one v
  · by_contra hne
    obtain ⟨h2, h1, -, h0⟩ := conductorDatum_support v ν a₁ a₂ hne
    refine hr ((Set.mem_univ_pi).mpr fun i => ?_)
    fin_cases i
    · show Valued.v (r 0 - 0) ≤ WithZero.exp (-(a₂ : ℤ))
      rw [sub_zero]
      exact h0.le
    · show Valued.v (r 1 - 0) ≤ WithZero.exp (-(a₂ : ℤ))
      rwa [sub_zero]
    · exact h2

end DatumRegularity

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section OneValue

private def lowerConj (x y z : v.adicCompletion ℚ) : LocalGL3 v :=
  antidiagonal3 v * upperUnipotent3 x y z * antidiagonal3 v

private theorem gl3Entry_lowerConj (x y z : v.adicCompletion ℚ) (i j : Fin 3) :
    gl3Entry v (lowerConj v x y z) i j = !![(1 : v.adicCompletion ℚ), 0, 0; y, 1, 0; z, x, 1] i j := by
  unfold lowerConj
  rw [gl3Entry_antidiagonal3_mul_mul_antidiagonal3]
  simp only [gl3Entry, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem rightTranslate_antidiagonal3_apply_antidiagonal3_mul (u : LocalGL3 v → ℂ) (x y z : v.adicCompletion ℚ) :
    gl3AmbientRightTranslate (R := ℂ) (antidiagonal3 v) u (antidiagonal3 v * upperUnipotent3 x y z) =
      u (lowerConj v x y z) :=
  rfl

private theorem cornerEntry_lowerConj (x y z : v.adicCompletion ℚ) : cornerEntry v (lowerConj v x y z) = z := by
  simp [cornerEntry, gl3Entry_lowerConj]

private theorem outerMinor_lowerConj (x y z : v.adicCompletion ℚ) : outerMinor v (lowerConj v x y z) = y := by
  simp [outerMinor, gl3Entry_lowerConj]

private theorem lowerMinor_lowerConj (x y z : v.adicCompletion ℚ) : lowerMinor v (lowerConj v x y z) = x * y - z := by
  have e10 : gl3Entry v (lowerConj v x y z) 1 0 = y := by simp [gl3Entry_lowerConj]
  have e11 : gl3Entry v (lowerConj v x y z) 1 1 = 1 := by simp [gl3Entry_lowerConj]
  have e20 : gl3Entry v (lowerConj v x y z) 2 0 = z := by simp [gl3Entry_lowerConj]
  have e21 : gl3Entry v (lowerConj v x y z) 2 1 = x := by simp [gl3Entry_lowerConj]
  simp only [lowerMinor, e10, e11, e20, e21]
  ring

private theorem gl3Entry_two_one_lowerConj (x y z : v.adicCompletion ℚ) : gl3Entry v (lowerConj v x y z) 2 1 = x := by
  simp [gl3Entry_lowerConj]

private theorem gl3Entry_two_two_lowerConj (x y z : v.adicCompletion ℚ) : gl3Entry v (lowerConj v x y z) 2 2 = 1 := by
  simp [gl3Entry_lowerConj]

private theorem gl3Det_lowerConj (x y z : v.adicCompletion ℚ) : gl3Det v (lowerConj v x y z) = 1 := by
  have e' : ∀ i j, (lowerConj v x y z : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
      gl3Entry v (lowerConj v x y z) i j := fun _ _ => rfl
  have e00 : gl3Entry v (lowerConj v x y z) 0 0 = 1 := by simp [gl3Entry_lowerConj]
  have e01 : gl3Entry v (lowerConj v x y z) 0 1 = 0 := by simp [gl3Entry_lowerConj]
  have e02 : gl3Entry v (lowerConj v x y z) 0 2 = 0 := by simp [gl3Entry_lowerConj]
  have e10 : gl3Entry v (lowerConj v x y z) 1 0 = y := by simp [gl3Entry_lowerConj]
  have e11 : gl3Entry v (lowerConj v x y z) 1 1 = 1 := by simp [gl3Entry_lowerConj]
  have e12 : gl3Entry v (lowerConj v x y z) 1 2 = 0 := by simp [gl3Entry_lowerConj]
  have e20 : gl3Entry v (lowerConj v x y z) 2 0 = z := by simp [gl3Entry_lowerConj]
  have e21 : gl3Entry v (lowerConj v x y z) 2 1 = x := by simp [gl3Entry_lowerConj]
  have e22 : gl3Entry v (lowerConj v x y z) 2 2 = 1 := by simp [gl3Entry_lowerConj]
  simp only [gl3Det, Matrix.det_fin_three, e', e00, e01, e02, e10, e11, e12, e20, e21, e22]
  ring

private theorem mem_bigCell3_lowerConj (x y z : v.adicCompletion ℚ) :
    lowerConj v x y z ∈ bigCell3 v ↔ z ≠ 0 ∧ x * y - z ≠ 0 := by
  rw [mem_bigCell3_iff, cornerEntry_lowerConj, lowerMinor_lowerConj]

private theorem cellRatio_lowerConj (x y z : v.adicCompletion ℚ) :
    cellRatio v (lowerConj v x y z) = ![x / z, 1 / z, y / (x * y - z)] := by
  simp only [cellRatio, cornerEntry_lowerConj, lowerMinor_lowerConj, outerMinor_lowerConj, gl3Entry_two_one_lowerConj,
    gl3Entry_two_two_lowerConj]

private theorem cellValue_lowerConj (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (x y z : v.adicCompletion ℚ) :
    cellValue v ν (lowerConj v x y z) =
      charExt (ν 0) (1 / (x * y - z)) * charExt (ν 1) ((x * y - z) / z) * charExt (ν 2) z *
        ((‖(1 : v.adicCompletion ℚ) / (x * y - z)‖ / ‖z‖ : ℝ) : ℂ) := by
  simp only [cellValue, gl3Det_lowerConj, lowerMinor_lowerConj, cornerEntry_lowerConj]

private theorem conductorDatum_cellRatio_lowerConj (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)
    (x y z : v.adicCompletion ℚ) :
    conductorDatum v ν a₁ a₂ (cellRatio v (lowerConj v x y z)) =
      conductorDatum v ν a₁ a₂ ![x / z, 1 / z, y / (x * y - z)] := by
  rw [cellRatio_lowerConj]

private theorem cellInvariant_lowerConj {x y z : v.adicCompletion ℚ} (hz : z ≠ 0) (hw : x * y - z ≠ 0) :
    (1 : v.adicCompletion ℚ) / z - x / z * (y / (x * y - z)) = -(1 / (x * y - z)) := by
  field_simp
  ring

private theorem cellSectionOf_conductorDatum_lowerConj (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)
    (x y z : v.adicCompletion ℚ) :
    cellSectionOf v ν (conductorDatum v ν a₁ a₂) (lowerConj v x y z) =
      (charExt (ν 0) (1 / (x * y - z)) * charExt (ν 1) ((x * y - z) / z) * charExt (ν 2) z *
          ((‖(1 : v.adicCompletion ℚ) / (x * y - z)‖ / ‖z‖ : ℝ) : ℂ)) *
        conductorDatum v ν a₁ a₂ ![x / z, 1 / z, y / (x * y - z)] := by
  by_cases hcell : z ≠ 0 ∧ x * y - z ≠ 0
  · rw [cellSectionOf_apply_of_mem v ν _ ((mem_bigCell3_lowerConj v x y z).mpr hcell), cellValue_lowerConj,
      cellRatio_lowerConj]
  · rw [cellSectionOf_apply_of_notMem v ν _ fun h => hcell ((mem_bigCell3_lowerConj v x y z).mp h)]
    rcases not_and_or.mp hcell with hz | hw
    · rw [not_not.mp hz, charExt_zero, mul_zero, zero_mul, zero_mul]
    · rw [not_not.mp hw, div_zero, charExt_zero, zero_mul, zero_mul, zero_mul, zero_mul]

end OneValue

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_one_add_mul_one_add {c : ℕ} (hc : 1 ≤ c) {w w' : v.adicCompletion ℚ}
    (hw : Valued.v w ≤ WithZero.exp (-(c : ℤ))) (hw' : Valued.v w' ≤ WithZero.exp (-(c : ℤ))) :
    ∃ w'' : v.adicCompletion ℚ, (1 + w) * (1 + w') = 1 + w'' ∧ Valued.v w'' ≤ WithZero.exp (-(c : ℤ)) := by
  refine ⟨w + w' + w * w', by ring, ?_⟩
  refine Valuation.map_add_le _ (Valuation.map_add_le _ hw hw') ?_
  rw [map_mul]
  calc Valued.v w * Valued.v w' ≤ WithZero.exp (-(c : ℤ)) * 1 :=
        mul_le_mul' hw (hw'.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
    _ = _ := mul_one _

private theorem exists_one_add_mul_one_add_inv {c : ℕ} (hc : 1 ≤ c) {w w' : v.adicCompletion ℚ}
    (hw : Valued.v w ≤ WithZero.exp (-(c : ℤ))) (hw' : Valued.v w' ≤ WithZero.exp (-(c : ℤ))) :
    ∃ w'' : v.adicCompletion ℚ, (1 + w) * (1 + w')⁻¹ = 1 + w'' ∧ Valued.v w'' ≤ WithZero.exp (-(c : ℤ)) := by
  have hu : Valued.v (1 + w') = 1 := valued_one_add_eq_one v hc hw'
  have hne : (1 + w') ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  refine ⟨(w - w') / (1 + w'), by field_simp; ring, ?_⟩
  rw [map_div₀, hu, div_one]
  exact Valuation.map_sub_le _ hw hw'

private theorem charExt_one' (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) : charExt ξ (1 : v.adicCompletion ℚ) = 1 := by
  rw [charExt_of_ne_zero ξ one_ne_zero]
  have : (Units.mk0 (1 : v.adicCompletion ℚ) one_ne_zero) = 1 := Units.ext rfl
  rw [this, map_one, Units.val_one]

private theorem charExt_inv_of_ne_zero (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    charExt ξ x⁻¹ = (charExt ξ x)⁻¹ := by
  have h := charExt_mul_of_ne_zero v ξ (inv_ne_zero hx) hx
  rw [inv_mul_cancel₀ hx, charExt_one' v ξ] at h
  exact eq_inv_of_mul_eq_one_left h.symm

private theorem charExt_div_of_ne_zero (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x y : v.adicCompletion ℚ} (hx : x ≠ 0)
    (hy : y ≠ 0) : charExt ξ (x / y) = charExt ξ x / charExt ξ y := by
  rw [div_eq_mul_inv, charExt_mul_of_ne_zero v ξ hx (inv_ne_zero hy), charExt_inv_of_ne_zero v ξ hy, div_eq_mul_inv]

private theorem charExt_units_val (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (u : (v.adicCompletion ℚ)ˣ) :
    charExt ξ (u : v.adicCompletion ℚ) = (ξ u : ℂ) := by
  rw [charExt_of_ne_zero ξ u.ne_zero, Units.mk0_val]

private theorem ne_zero_of_valued_eq_one {x : v.adicCompletion ℚ} (hx : Valued.v x = 1) : x ≠ 0 := by
  intro h
  rw [h, map_zero] at hx
  exact zero_ne_one hx

section Table

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {a₀ a₁ a₂ : ℕ}
  (hν₀ : HasConductorExponentAt ℚ v (ν 0) a₀) (hν₁ : HasConductorExponentAt ℚ v (ν 1) a₁)
  (hν₂ : HasConductorExponentAt ℚ v (ν 2) a₂) (h₀ : 1 ≤ a₀) (h₁ : 1 ≤ a₁) (h₂ : 1 ≤ a₂) (h₀₂ : a₀ ≤ a₂)
  (h₁₂ : a₁ ≤ a₂)

include hν₀ hν₁ hν₂ h₀ h₁ h₂ h₀₂ h₁₂ in

private theorem cellSectionOf_conductorDatum_mul_of_isOppositeCongruence {a : ℕ} (ha : a₀ + a₁ + a₂ ≤ a) {k : LocalGL3 v}
    (hk : IsOppositeCongruence v a k) {y : LocalGL3 v} (hy : y ∈ cellSupport v ν a₁ a₂) :
    y * k ∈ cellSupport v ν a₁ a₂ ∧
      ∀ u : (v.adicCompletion ℚ)ˣ, (u : v.adicCompletion ℚ) = gl3Entry v k 0 0 →
        cellSectionOf v ν (conductorDatum v ν a₁ a₂) (y * k) =
          ((ν 0 u : ℂ) * (ν 1 u : ℂ) * (ν 2 u : ℂ)) * cellSectionOf v ν (conductorDatum v ν a₁ a₂) y := by
  obtain ⟨hcell, hΦ⟩ := hy
  obtain ⟨hc, hl⟩ := (mem_bigCell3_iff v y).mp hcell
  obtain ⟨hr2, hr1, hQ, hr0⟩ := conductorDatum_support v ν a₁ a₂ hΦ
  have ha1 : 1 ≤ a := by omega
  obtain ⟨hk00, hk11, hk22⟩ := hk.diag_valued v ha1
  have hi := ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk.mem).1
  have hdetk : Valued.v (gl3Det v k) = 1 := valued_det_eq_one_of_mem_localMaximalCompact3 v hk.mem
  have hk00' := ne_zero_of_valued_eq_one v hk00
  have hk11' := ne_zero_of_valued_eq_one v hk11
  have hk22' := ne_zero_of_valued_eq_one v hk22
  have hdetk' := ne_zero_of_valued_eq_one v hdetk
  have hr0' : cellRatio v y 0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hr0
    exact WithZero.exp_ne_zero hr0.symm
  have hQ' : cellInvariant v y ≠ 0 := by
    intro h
    have hQ0 : Valued.v (cellInvariant v y) = WithZero.exp (-((a₁ : ℤ) + a₂)) := hQ
    rw [h, map_zero] at hQ0
    exact WithZero.exp_ne_zero hQ0.symm

  have hL : ∀ {x z : v.adicCompletion ℚ} {d : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ 1 → Valued.v z ≤ d → Valued.v (x * z) ≤ d :=
    fun hx hz => by rw [map_mul]; simpa using mul_le_mul' hx hz
  have hR : ∀ {x z : v.adicCompletion ℚ} {d : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ d → Valued.v z ≤ 1 → Valued.v (x * z) ≤ d :=
    fun hx hz => by rw [map_mul]; simpa using mul_le_mul' hx hz
  have hmono : ∀ {m n : ℕ}, m ≤ n → WithZero.exp (-(n : ℤ)) ≤ WithZero.exp (-(m : ℤ)) := fun hmn => by
    rw [WithZero.exp_le_exp]; omega
  have hexp_a : WithZero.exp (-(a : ℤ)) ≤ WithZero.exp (-((a₁ + a₂ : ℕ) : ℤ)) := hmono (by omega)
  have hexp_2a : WithZero.exp (-(2 * (a : ℤ))) ≤ WithZero.exp (-(a : ℤ)) := by
    rw [WithZero.exp_le_exp]; omega
  have hexp_a2 : Valued.v (cellRatio v y 0) ≤ WithZero.exp (-(a₂ : ℤ)) := hr0.le
  have hQle : Valued.v (cellInvariant v y) ≤ WithZero.exp (-((a₁ + a₂ : ℕ) : ℤ)) := by
    show Valued.v (cellRatio v y 1 - cellRatio v y 0 * cellRatio v y 2) ≤ _
    rw [hQ]; push_cast; exact le_rfl
  have hnegQ : cellRatio v y 0 * cellRatio v y 2 - cellRatio v y 1 = -cellInvariant v y := by
    unfold cellInvariant; ring

  obtain ⟨w₀, hF₀, hw₀⟩ := exists_eq_mul_one_add_of_valued_sub_le v (E := gl3Entry v k 0 0 +
      cellRatio v y 0 * gl3Entry v k 1 0 + cellRatio v y 1 * gl3Entry v k 2 0) hk00' (c := a₂) (by
    rw [hk00, one_mul, show gl3Entry v k 0 0 + cellRatio v y 0 * gl3Entry v k 1 0 + cellRatio v y 1 * gl3Entry v k 2 0
        - gl3Entry v k 0 0 = cellRatio v y 0 * gl3Entry v k 1 0 + cellRatio v y 1 * gl3Entry v k 2 0 by ring]
    exact Valuation.map_add_le _ (hR hexp_a2 (hi 1 0)) (hR hr1 (hi 2 0)))

  obtain ⟨w₁, hF₁, hw₁⟩ := exists_eq_mul_one_add_of_valued_sub_le v (E :=
      (gl3Entry v k 0 0 * gl3Entry v k 1 1 - gl3Entry v k 0 1 * gl3Entry v k 1 0) +
        cellRatio v y 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) +
          (cellRatio v y 0 * cellRatio v y 2 - cellRatio v y 1) *
            (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0))
      (mul_ne_zero hk00' hk11') (c := a₁ + a₂) (by
    rw [map_mul, hk00, hk11, one_mul, one_mul, hnegQ]
    have hrest : (gl3Entry v k 0 0 * gl3Entry v k 1 1 - gl3Entry v k 0 1 * gl3Entry v k 1 0) +
        cellRatio v y 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) +
          -cellInvariant v y * (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0) -
            gl3Entry v k 0 0 * gl3Entry v k 1 1 =
        -(gl3Entry v k 1 0 * gl3Entry v k 0 1) +
          cellRatio v y 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) -
            cellInvariant v y * (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0) := by
      ring
    rw [hrest]
    refine Valuation.map_sub_le _ (Valuation.map_add_le _ ?_ ?_) ?_
    · rw [Valuation.map_neg]
      exact le_trans (hL (hi 1 0) hk.h01) (hexp_2a.trans hexp_a)
    · refine hL hr2 (le_trans (Valuation.map_sub_le _ (hL (hi 0 0) hk.h21) (le_trans (hR hk.h01 (hi 2 0)) hexp_2a))
        hexp_a)
    · exact hR hQle (Valuation.map_sub_le _ (hL (hi 1 0) (hi 2 1)) (hL (hi 1 1) (hi 2 0))))

  obtain ⟨wd, hdk, hwd⟩ := exists_eq_mul_one_add_of_valued_sub_le v (E := gl3Det v k)
      (mul_ne_zero (mul_ne_zero hk00' hk11') hk22') (c := a) (by
    rw [map_mul, map_mul, hk00, hk11, hk22, one_mul, one_mul, one_mul]
    have hexpand : gl3Det v k - gl3Entry v k 0 0 * gl3Entry v k 1 1 * gl3Entry v k 2 2 =
        -(gl3Entry v k 0 0 * (gl3Entry v k 1 2 * gl3Entry v k 2 1)) -
          gl3Entry v k 1 0 * (gl3Entry v k 2 2 * gl3Entry v k 0 1) +
            gl3Entry v k 1 2 * (gl3Entry v k 2 0 * gl3Entry v k 0 1) +
              gl3Entry v k 1 0 * (gl3Entry v k 2 1 * gl3Entry v k 0 2) -
                gl3Entry v k 1 1 * (gl3Entry v k 2 0 * gl3Entry v k 0 2) := by
      simp only [gl3Det, gl3Entry, Matrix.det_fin_three]
      ring
    rw [hexpand]
    refine Valuation.map_sub_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sub_le _ ?_ ?_) ?_)
      ?_) ?_
    · rw [Valuation.map_neg]; exact hL (hi 0 0) (hL (hi 1 2) hk.h21)
    · exact hL (hi 1 0) (le_trans (hL (hi 2 2) hk.h01) hexp_2a)
    · exact hL (hi 1 2) (le_trans (hL (hi 2 0) hk.h01) hexp_2a)
    · exact hL (hi 1 0) (hL (hi 2 1) hk.h02)
    · exact hL (hi 1 1) (hL (hi 2 0) hk.h02))

  have hcorner : cornerEntry v (y * k) = cornerEntry v y * (gl3Entry v k 0 0 * (1 + w₀)) := by
    rw [cornerEntry_mul_of_ne_zero v hc, ← hF₀]
  have hlower : lowerMinor v (y * k) = lowerMinor v y * (gl3Entry v k 0 0 * gl3Entry v k 1 1 * (1 + w₁)) := by
    rw [lowerMinor_mul_of_ne_zero v hc hl, ← hF₁]
  have hdet : gl3Det v (y * k) = gl3Det v y * (gl3Entry v k 0 0 * gl3Entry v k 1 1 * gl3Entry v k 2 2 * (1 + wd)) := by
    rw [gl3Det_mul, ← hdk]
  have hw₀1 : (1 + w₀) ≠ 0 := ne_zero_of_valued_eq_one v (valued_one_add_eq_one v h₂ hw₀)
  have hw₁1 : (1 + w₁) ≠ 0 := ne_zero_of_valued_eq_one v (valued_one_add_eq_one v (by omega) hw₁)
  have hwd1 : (1 + wd) ≠ 0 := ne_zero_of_valued_eq_one v (valued_one_add_eq_one v ha1 hwd)
  have hc' : cornerEntry v (y * k) ≠ 0 := by
    rw [hcorner]; exact mul_ne_zero hc (mul_ne_zero hk00' hw₀1)
  have hl' : lowerMinor v (y * k) ≠ 0 := by
    rw [hlower]; exact mul_ne_zero hl (mul_ne_zero (mul_ne_zero hk00' hk11') hw₁1)
  have hcell' : y * k ∈ bigCell3 v := (mem_bigCell3_iff v _).mpr ⟨hc', hl'⟩

  have hw₀_a₁ : Valued.v w₀ ≤ WithZero.exp (-(a₁ : ℤ)) := hw₀.trans (hmono h₁₂)
  have hw₁_a₀ : Valued.v w₁ ≤ WithZero.exp (-(a₀ : ℤ)) := hw₁.trans (hmono (by omega))
  have hw₁_a₁ : Valued.v w₁ ≤ WithZero.exp (-(a₁ : ℤ)) := hw₁.trans (hmono (by omega))
  have hwd_a₀ : Valued.v wd ≤ WithZero.exp (-(a₀ : ℤ)) := hwd.trans (hmono (by omega))
  obtain ⟨wA, hwA, hwA'⟩ := exists_one_add_mul_one_add_inv v h₀ hwd_a₀ hw₁_a₀
  obtain ⟨wB, hwB, hwB'⟩ := exists_one_add_mul_one_add_inv v h₁ hw₁_a₁ hw₀_a₁

  obtain ⟨w₂, hn₀, hw₂⟩ := exists_eq_mul_one_add_of_valued_sub_le v (E := gl3Entry v k 0 1 +
      cellRatio v y 0 * gl3Entry v k 1 1 + cellRatio v y 1 * gl3Entry v k 2 1) (mul_ne_zero hr0' hk11') (c := a₁) (by
    rw [map_mul, hr0, hk11, mul_one, ← WithZero.exp_add, show gl3Entry v k 0 1 + cellRatio v y 0 * gl3Entry v k 1 1 +
        cellRatio v y 1 * gl3Entry v k 2 1 - cellRatio v y 0 * gl3Entry v k 1 1 =
        gl3Entry v k 0 1 + cellRatio v y 1 * gl3Entry v k 2 1 by ring]
    refine Valuation.map_add_le _ (hk.h01.trans ?_) ?_
    · rw [WithZero.exp_le_exp]; omega
    · rw [map_mul]
      calc Valued.v (cellRatio v y 1) * Valued.v (gl3Entry v k 2 1)
          ≤ WithZero.exp (-(a₂ : ℤ)) * WithZero.exp (-(a : ℤ)) := mul_le_mul' hr1 hk.h21
        _ ≤ WithZero.exp (-(a₂ : ℤ) + -(a₁ : ℤ)) := by rw [← WithZero.exp_add, WithZero.exp_le_exp]; omega)
  obtain ⟨wC, hwC, hwC'⟩ := exists_one_add_mul_one_add_inv v h₁ hw₂ hw₀_a₁
  have hratio0 : cellRatio v (y * k) 0 =
      cellRatio v y 0 * (gl3Entry v k 1 1 / gl3Entry v k 0 0) * (1 + wC) := by
    rw [cellRatio_zero, gl3Entry_two_one_mul_of_ne_zero v hc, hcorner, hn₀, ← hwC]
    field_simp

  have hratio1 : Valued.v (cellRatio v (y * k) 1) ≤ WithZero.exp (-(a₂ : ℤ)) := by
    rw [cellRatio_one, gl3Entry_two_two_mul_of_ne_zero v hc, hcorner, mul_div_mul_left _ _ hc, map_div₀, map_mul,
      hk00, valued_one_add_eq_one v h₂ hw₀, one_mul, div_one]
    refine Valuation.map_add_le _ (Valuation.map_add_le _ (hk.h02.trans (hmono (by omega))) (hR hexp_a2 (hi 1 2)))
      (hR hr1 (hi 2 2))

  have hratio2 : Valued.v (cellRatio v (y * k) 2) ≤ 1 := by
    rw [cellRatio_two, outerMinor_mul_of_ne_zero v hc hl, hlower, mul_div_mul_left _ _ hl, map_div₀, map_mul, map_mul,
      hk00, hk11, valued_one_add_eq_one v (by omega) hw₁, mul_one, mul_one, div_one, hnegQ]
    have hQ1 : Valued.v (-cellInvariant v y) ≤ 1 := by
      rw [Valuation.map_neg]
      exact hQle.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
    refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
    · exact Valuation.map_sub_le _ (hL (hi 0 0) (hi 1 2)) (hL (hi 0 2) (hi 1 0))
    · exact hL hr2 (Valuation.map_sub_le _ (hL (hi 0 0) (hi 2 2)) (hL (hi 0 2) (hi 2 0)))
    · exact hL hQ1 (Valuation.map_sub_le _ (hL (hi 1 0) (hi 2 2)) (hL (hi 1 2) (hi 2 0)))

  have hright : rightMinor v (y * k) = lowerMinor v y *
      ((gl3Entry v k 0 1 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 1) +
        cellRatio v y 2 * (gl3Entry v k 0 1 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 1) -
          cellInvariant v y * (gl3Entry v k 1 1 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 1)) := by
    rw [rightMinor_mul, ← cellRatio_two_mul_lowerMinor v hl, rightMinor_eq_of_ne_zero v hc hl, hnegQ]
    ring
  obtain ⟨wQ, hnQ, hwQ⟩ := exists_eq_mul_one_add_of_valued_sub_le v (E :=
      cellInvariant v y * (gl3Entry v k 1 1 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 1) -
        (gl3Entry v k 0 1 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 1) -
          cellRatio v y 2 * (gl3Entry v k 0 1 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 1))
      (mul_ne_zero (mul_ne_zero hQ' hk11') hk22') (c := a₀) (by
    rw [map_mul, map_mul, hk11, hk22, mul_one, mul_one]
    have hQv : Valued.v (cellInvariant v y) = WithZero.exp (-((a₁ + a₂ : ℕ) : ℤ)) := by
      show Valued.v (cellRatio v y 1 - cellRatio v y 0 * cellRatio v y 2) = _
      rw [hQ]; push_cast; rfl
    rw [hQv, ← WithZero.exp_add]
    have hsmall : WithZero.exp (-(a : ℤ)) ≤ WithZero.exp (-((a₁ + a₂ : ℕ) : ℤ) + -(a₀ : ℤ)) := by
      rw [WithZero.exp_le_exp]; push_cast; omega
    have hexpand : cellInvariant v y * (gl3Entry v k 1 1 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 1) -
        (gl3Entry v k 0 1 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 1) -
          cellRatio v y 2 * (gl3Entry v k 0 1 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 1) -
            cellInvariant v y * gl3Entry v k 1 1 * gl3Entry v k 2 2 =
        -(cellInvariant v y * (gl3Entry v k 1 2 * gl3Entry v k 2 1)) -
          (gl3Entry v k 1 2 * gl3Entry v k 0 1 - gl3Entry v k 1 1 * gl3Entry v k 0 2) -
            cellRatio v y 2 * (gl3Entry v k 2 2 * gl3Entry v k 0 1 - gl3Entry v k 2 1 * gl3Entry v k 0 2) := by
      ring
    rw [hexpand]
    refine Valuation.map_sub_le _ (Valuation.map_sub_le _ ?_ ?_) ?_
    · rw [Valuation.map_neg]
      rw [map_mul]
      refine le_trans (mul_le_mul' hQle (hL (hi 1 2) hk.h21)) ?_
      rw [← WithZero.exp_add, WithZero.exp_le_exp]; push_cast; omega
    · refine le_trans (Valuation.map_sub_le _ (le_trans (hL (hi 1 2) hk.h01) hexp_2a) (hL (hi 1 1) hk.h02)) hsmall
    · refine le_trans (hL hr2 (Valuation.map_sub_le _ (le_trans (hL (hi 2 2) hk.h01) hexp_2a)
        (le_trans (hL (hi 2 1) hk.h02) le_rfl))) hsmall)
  obtain ⟨wD, hwD, hwD'⟩ := exists_one_add_mul_one_add_inv v h₀ hwQ hw₁_a₀
  have hinvariant : cellInvariant v (y * k) =
      cellInvariant v y * (gl3Entry v k 2 2 / gl3Entry v k 0 0) * (1 + wD) := by
    rw [cellInvariant_eq_of_ne_zero v hc' hl', hright, hlower, ← hwD]
    have hE : (gl3Entry v k 0 1 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 1) +
        cellRatio v y 2 * (gl3Entry v k 0 1 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 1) -
          cellInvariant v y * (gl3Entry v k 1 1 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 1) =
        -(cellInvariant v y * gl3Entry v k 1 1 * gl3Entry v k 2 2 * (1 + wQ)) := by
      rw [← hnQ]; ring
    rw [hE]
    field_simp

  have hunit0 : Valued.v (gl3Entry v k 1 1 / gl3Entry v k 0 0 * (1 + wC)) = 1 := by
    rw [map_mul, map_div₀, hk11, hk00, valued_one_add_eq_one v h₁ hwC', div_one, one_mul]
  have hunitQ : Valued.v (gl3Entry v k 2 2 / gl3Entry v k 0 0 * (1 + wD)) = 1 := by
    rw [map_mul, map_div₀, hk22, hk00, valued_one_add_eq_one v h₀ hwD', div_one, one_mul]
  have hr0new : Valued.v (cellRatio v (y * k) 0) = WithZero.exp (-(a₂ : ℤ)) := by
    rw [hratio0, mul_assoc, map_mul, hunit0, mul_one, hr0]
  have hQnew : Valued.v (cellRatio v (y * k) 1 - cellRatio v (y * k) 0 * cellRatio v (y * k) 2) =
      WithZero.exp (-((a₁ : ℤ) + a₂)) := by
    show Valued.v (cellInvariant v (y * k)) = _
    rw [hinvariant, mul_assoc, map_mul, hunitQ, mul_one]
    exact hQ
  have hQnew' : cellRatio v (y * k) 1 - cellRatio v (y * k) 0 * cellRatio v (y * k) 2 ≠ 0 := by
    intro h
    rw [h, map_zero] at hQnew
    exact WithZero.exp_ne_zero hQnew.symm
  have hr0new' : cellRatio v (y * k) 0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hr0new
    exact WithZero.exp_ne_zero hr0new.symm
  have hmem' : y * k ∈ cellSupport v ν a₁ a₂ := by
    refine ⟨hcell', ?_⟩
    rw [conductorDatum_apply_of_support v ν a₁ a₂ hratio2 hratio1 hQnew hr0new]
    exact mul_ne_zero (charExt_ne_zero v _ hQnew') (charExt_ne_zero v _ hr0new')
  refine ⟨hmem', fun u hu => ?_⟩

  have hν₀' := hasConductorExponentAt_inv' v hν₀
  have hν₁' := hasConductorExponentAt_inv' v hν₁
  rw [cellSectionOf_conductorDatum_apply_of_mem v ν a₁ a₂ hmem', cellSectionOf_conductorDatum_apply_of_mem v ν a₁ a₂
    ⟨hcell, hΦ⟩, conductorDatum_apply_of_support v ν a₁ a₂ hratio2 hratio1 hQnew hr0new,
    conductorDatum_apply_of_support v ν a₁ a₂ hr2 hr1 hQ hr0]

  have hD0 : charExt (ν 0)⁻¹ (cellRatio v (y * k) 1 - cellRatio v (y * k) 0 * cellRatio v (y * k) 2) =
      charExt (ν 0)⁻¹ (cellRatio v y 1 - cellRatio v y 0 * cellRatio v y 2) *
        (charExt (ν 0) (gl3Entry v k 2 2) / charExt (ν 0) (gl3Entry v k 0 0))⁻¹ := by
    show charExt (ν 0)⁻¹ (cellInvariant v (y * k)) = charExt (ν 0)⁻¹ (cellInvariant v y) * _
    rw [hinvariant, charExt_mul_one_add v _ hν₀' h₀ (mul_ne_zero hQ' (div_ne_zero hk22' hk00')) hwD',
      charExt_mul_of_ne_zero v _ hQ' (div_ne_zero hk22' hk00'), charExt_inv_apply v (ν 0) (_ / _),
      charExt_div_of_ne_zero v _ hk22' hk00']
  have hD1 : charExt (ν 1)⁻¹ (cellRatio v (y * k) 0) =
      charExt (ν 1)⁻¹ (cellRatio v y 0) * (charExt (ν 1) (gl3Entry v k 1 1) / charExt (ν 1) (gl3Entry v k 0 0))⁻¹ := by
    rw [hratio0, charExt_mul_one_add v _ hν₁' h₁ (mul_ne_zero hr0' (div_ne_zero hk11' hk00')) hwC',
      charExt_mul_of_ne_zero v _ hr0' (div_ne_zero hk11' hk00'), charExt_inv_apply v (ν 1) (_ / _),
      charExt_div_of_ne_zero v _ hk11' hk00']

  have hV : cellValue v ν (y * k) =
      charExt (ν 0) (gl3Entry v k 2 2) * charExt (ν 1) (gl3Entry v k 1 1) * charExt (ν 2) (gl3Entry v k 0 0) *
        cellValue v ν y := by
    unfold cellValue
    have e0 : gl3Det v (y * k) / lowerMinor v (y * k) =
        gl3Det v y / lowerMinor v y * (gl3Entry v k 2 2 * (1 + wA)) := by
      rw [hdet, hlower, ← hwA]; field_simp
    have e1 : lowerMinor v (y * k) / cornerEntry v (y * k) =
        lowerMinor v y / cornerEntry v y * (gl3Entry v k 1 1 * (1 + wB)) := by
      rw [hlower, hcorner, ← hwB]; field_simp
    have hdl : gl3Det v y / lowerMinor v y ≠ 0 := div_ne_zero (gl3Det_ne_zero v y) hl
    have hlc : lowerMinor v y / cornerEntry v y ≠ 0 := div_ne_zero hl hc
    have nA : ‖gl3Entry v k 2 2 * (1 + wA)‖ = 1 := norm_eq_one_of_valued_eq_one v (by
      rw [map_mul, hk22, valued_one_add_eq_one v h₀ hwA', mul_one])
    have n0 : ‖gl3Entry v k 0 0 * (1 + w₀)‖ = 1 := norm_eq_one_of_valued_eq_one v (by
      rw [map_mul, hk00, valued_one_add_eq_one v h₂ hw₀, mul_one])
    rw [e0, e1, hcorner, charExt_mul_of_ne_zero v _ hdl (mul_ne_zero hk22' (ne_zero_of_valued_eq_one v
        (valued_one_add_eq_one v h₀ hwA'))), charExt_mul_one_add v _ hν₀ h₀ hk22' hwA',
      charExt_mul_of_ne_zero v _ hlc (mul_ne_zero hk11'
        (ne_zero_of_valued_eq_one v (valued_one_add_eq_one v h₁ hwB'))),
      charExt_mul_one_add v _ hν₁ h₁ hk11' hwB',
      charExt_mul_of_ne_zero v _ hc (mul_ne_zero hk00' hw₀1), charExt_mul_one_add v _ hν₂ h₂ hk00' hw₀,
      norm_mul (gl3Det v y / lowerMinor v y) (gl3Entry v k 2 2 * (1 + wA)), nA,
      norm_mul (cornerEntry v y) (gl3Entry v k 0 0 * (1 + w₀)), n0]
    push_cast
    ring
  rw [hV, hD0, hD1]

  have hu0 : charExt (ν 0) (gl3Entry v k 0 0) = (ν 0 u : ℂ) := by rw [← hu, charExt_units_val]
  have hu1 : charExt (ν 1) (gl3Entry v k 0 0) = (ν 1 u : ℂ) := by rw [← hu, charExt_units_val]
  have hu2 : charExt (ν 2) (gl3Entry v k 0 0) = (ν 2 u : ℂ) := by rw [← hu, charExt_units_val]
  have n22 := charExt_ne_zero v (ν 0) hk22'
  have n11 := charExt_ne_zero v (ν 1) hk11'
  have n00 := charExt_ne_zero v (ν 0) hk00'
  have n00' := charExt_ne_zero v (ν 1) hk00'
  rw [← hu0, ← hu1, ← hu2]
  field_simp

end Table

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section Equivariance

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {a₀ a₁ a₂ : ℕ}
  (hν₀ : HasConductorExponentAt ℚ v (ν 0) a₀) (hν₁ : HasConductorExponentAt ℚ v (ν 1) a₁)
  (hν₂ : HasConductorExponentAt ℚ v (ν 2) a₂) (h₀ : 1 ≤ a₀) (h₁ : 1 ≤ a₁) (h₂ : 1 ≤ a₂) (h₀₂ : a₀ ≤ a₂)
  (h₁₂ : a₁ ≤ a₂)

private theorem conj_mul_conj_inv (k : LocalGL3 v) :
    antidiagonal3 v * k * antidiagonal3 v * (antidiagonal3 v * k⁻¹ * antidiagonal3 v) = 1 := by
  have hww := antidiagonal3_mul_antidiagonal3 v
  calc antidiagonal3 v * k * antidiagonal3 v * (antidiagonal3 v * k⁻¹ * antidiagonal3 v)
      = antidiagonal3 v * k * (antidiagonal3 v * antidiagonal3 v) * k⁻¹ * antidiagonal3 v := by
        simp only [mul_assoc]
    _ = antidiagonal3 v * antidiagonal3 v := by rw [hww, mul_one, mul_inv_cancel_right]; exact hww
    _ = 1 := hww

private theorem mul_mul_antidiagonal3_eq (g k : LocalGL3 v) :
    g * k * antidiagonal3 v = g * antidiagonal3 v * (antidiagonal3 v * k * antidiagonal3 v) := by
  have hww := antidiagonal3_mul_antidiagonal3 v
  calc g * k * antidiagonal3 v = g * (antidiagonal3 v * antidiagonal3 v) * k * antidiagonal3 v := by
        rw [hww, mul_one]
    _ = _ := by simp only [mul_assoc]

include hν₀ hν₁ hν₂ h₀ h₁ h₂ h₀₂ h₁₂ in

private theorem cellSectionOf_conductorDatum_mul_conj {a : ℕ} (ha : a₀ + a₁ + a₂ ≤ a) {k : LocalGL3 v}
    (hk : k ∈ converseCongruenceSet3 v a) {u : (v.adicCompletion ℚ)ˣ}
    (hu : (u : v.adicCompletion ℚ) = gl3Entry v k 2 2)
    (y : LocalGL3 v) :
    cellSectionOf v ν (conductorDatum v ν a₁ a₂) (y * (antidiagonal3 v * k * antidiagonal3 v)) =
      ((ν 0 u : ℂ) * (ν 1 u : ℂ) * (ν 2 u : ℂ)) * cellSectionOf v ν (conductorDatum v ν a₁ a₂) y := by
  have hk' := isOppositeCongruence_conj v hk
  have hu' : (u : v.adicCompletion ℚ) = gl3Entry v (antidiagonal3 v * k * antidiagonal3 v) 0 0 := by
    rw [gl3Entry_conj_zero_zero, hu]
  by_cases hy : y ∈ cellSupport v ν a₁ a₂
  · exact (cellSectionOf_conductorDatum_mul_of_isOppositeCongruence v ν hν₀ hν₁ hν₂ h₀ h₁ h₂ h₀₂ h₁₂ ha hk' hy).2 u hu'
  · rw [cellSectionOf_conductorDatum_eq_zero_of_notMem v ν a₁ a₂ hy, mul_zero]
    refine cellSectionOf_conductorDatum_eq_zero_of_notMem v ν a₁ a₂ fun hyk => hy ?_
    have hkinv := isOppositeCongruence_conj v (converseCongruenceSet3_inv_mem v hk)
    have hback := (cellSectionOf_conductorDatum_mul_of_isOppositeCongruence v ν hν₀ hν₁ hν₂ h₀ h₁ h₂ h₀₂ h₁₂ ha hkinv
      hyk).1
    rwa [mul_assoc, conj_mul_conj_inv, mul_one] at hback

include hν₀ hν₁ hν₂ h₀ h₁ h₂ h₀₂ h₁₂ in

private theorem isCongruenceEquivariantAt_jacquetWhittaker3_conductorDatum (ω : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ u : (v.adicCompletion ℚ)ˣ, (ω u : ℂ) = (ν 0 u : ℂ) * (ν 1 u : ℂ) * (ν 2 u : ℂ))
    (hhom : ∀ (c : ℂ) (f : LocalGL3 v → ℂ), jacquetValue v (fun y => c * f y) = c * jacquetValue v f) {a : ℕ}
    (ha : a₀ + a₁ + a₂ ≤ a) :
    IsCongruenceEquivariantAt v a ω
      (fun h => jacquetWhittaker3 v ν (conductorDatum v ν a₁ a₂) (h * antidiagonal3 v)) := by
  intro k hk u hu g
  have hfun : (gl3AmbientRightTranslate (R := ℂ) (g * k * antidiagonal3 v)
        (cellSectionOf v ν (conductorDatum v ν a₁ a₂)) : LocalGL3 v → ℂ) =
      fun y => (ω u : ℂ) * gl3AmbientRightTranslate (R := ℂ) (g * antidiagonal3 v)
        (cellSectionOf v ν (conductorDatum v ν a₁ a₂)) y := by
    funext y
    show cellSectionOf v ν (conductorDatum v ν a₁ a₂) (y * (g * k * antidiagonal3 v)) =
      (ω u : ℂ) * cellSectionOf v ν (conductorDatum v ν a₁ a₂) (y * (g * antidiagonal3 v))
    rw [mul_mul_antidiagonal3_eq, ← mul_assoc, hω]
    exact cellSectionOf_conductorDatum_mul_conj v ν hν₀ hν₁ hν₂ h₀ h₁ h₂ h₀₂ h₁₂ ha hk hu _
  show jacquetWhittaker3 v ν (conductorDatum v ν a₁ a₂) (g * k * antidiagonal3 v) =
    (ω u : ℂ) * jacquetWhittaker3 v ν (conductorDatum v ν a₁ a₂) (g * antidiagonal3 v)
  rw [jacquetWhittaker3_apply, jacquetWhittaker3_apply, hfun, hhom]

end Equivariance

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def lowerUnipotent10 (x : v.adicCompletion ℚ) : LocalGL3 v :=
  antidiagonal3 v * upperUnipotent3 0 x 0 * antidiagonal3 v

private theorem mul_upperUnipotent3_mul_antidiagonal3 (g : LocalGL3 v) (x : v.adicCompletion ℚ) :
    g * upperUnipotent3 0 x 0 * antidiagonal3 v = g * antidiagonal3 v * lowerUnipotent10 v x :=
  mul_mul_antidiagonal3_eq v g _

private theorem lowerUnipotent10_mul_lowerUnipotent10 (x x' : v.adicCompletion ℚ) :
    lowerUnipotent10 v x * lowerUnipotent10 v x' = lowerUnipotent10 v (x + x') := by
  unfold lowerUnipotent10
  have hww := antidiagonal3_mul_antidiagonal3 v
  have hn : (upperUnipotent3 0 x 0 : LocalGL3 v) * upperUnipotent3 0 x' 0 = upperUnipotent3 0 (x + x') 0 := by
    ext i j
    simp only [Units.val_mul, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]
  calc antidiagonal3 v * upperUnipotent3 0 x 0 * antidiagonal3 v *
        (antidiagonal3 v * upperUnipotent3 0 x' 0 * antidiagonal3 v)
      = antidiagonal3 v * upperUnipotent3 0 x 0 * (antidiagonal3 v * antidiagonal3 v) * upperUnipotent3 0 x' 0 *
          antidiagonal3 v := by simp only [mul_assoc]
    _ = _ := by rw [hww, mul_one, mul_assoc (antidiagonal3 v), hn]

private theorem gl3Entry_lowerUnipotent10 (x : v.adicCompletion ℚ) (i j : Fin 3) :
    gl3Entry v (lowerUnipotent10 v x) i j = !![(1 : v.adicCompletion ℚ), 0, 0; x, 1, 0; 0, 0, 1] i j := by
  unfold lowerUnipotent10
  rw [gl3Entry_antidiagonal3_mul_mul_antidiagonal3]
  simp only [gl3Entry, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> rfl

section Law

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {a₁ a₂ : ℕ}

private theorem cellSectionOf_conductorDatum_mul_lowerUnipotent10 (h₂ : 2 ≤ a₂) (h₁ : 1 ≤ a₁) {y : LocalGL3 v}
    (hy : y ∈ cellSupport v ν a₁ a₂) {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp (1 : ℤ)) :
    y * lowerUnipotent10 v x ∈ cellSupport v ν a₁ a₂ ∧
      cellSectionOf v ν (conductorDatum v ν a₁ a₂) (y * lowerUnipotent10 v x) =
        charExt (ν 2) (1 + cellRatio v y 0 * x) * cellSectionOf v ν (conductorDatum v ν a₁ a₂) y := by
  obtain ⟨hcell, hΦ⟩ := hy
  obtain ⟨hc, hl⟩ := (mem_bigCell3_iff v y).mp hcell
  obtain ⟨hr2, hr1, hQ, hr0⟩ := conductorDatum_support v ν a₁ a₂ hΦ
  have e00 : gl3Entry v (lowerUnipotent10 v x) 0 0 = 1 := by simp [gl3Entry_lowerUnipotent10]
  have e01 : gl3Entry v (lowerUnipotent10 v x) 0 1 = 0 := by simp [gl3Entry_lowerUnipotent10]
  have e02 : gl3Entry v (lowerUnipotent10 v x) 0 2 = 0 := by simp [gl3Entry_lowerUnipotent10]
  have e10 : gl3Entry v (lowerUnipotent10 v x) 1 0 = x := by simp [gl3Entry_lowerUnipotent10]
  have e11 : gl3Entry v (lowerUnipotent10 v x) 1 1 = 1 := by simp [gl3Entry_lowerUnipotent10]
  have e12 : gl3Entry v (lowerUnipotent10 v x) 1 2 = 0 := by simp [gl3Entry_lowerUnipotent10]
  have e20 : gl3Entry v (lowerUnipotent10 v x) 2 0 = 0 := by simp [gl3Entry_lowerUnipotent10]
  have e21 : gl3Entry v (lowerUnipotent10 v x) 2 1 = 0 := by simp [gl3Entry_lowerUnipotent10]
  have e22 : gl3Entry v (lowerUnipotent10 v x) 2 2 = 1 := by simp [gl3Entry_lowerUnipotent10]

  have hw : Valued.v (cellRatio v y 0 * x) ≤ WithZero.exp (-((a₂ - 1 : ℕ) : ℤ)) := by
    rw [map_mul, hr0]
    calc WithZero.exp (-(a₂ : ℤ)) * Valued.v x ≤ WithZero.exp (-(a₂ : ℤ)) * WithZero.exp (1 : ℤ) :=
          mul_le_mul' le_rfl hx
      _ = _ := by rw [← WithZero.exp_add]; congr 1; push_cast [Nat.cast_sub (by omega : 1 ≤ a₂)]; ring
  have hu : Valued.v (1 + cellRatio v y 0 * x) = 1 := valued_one_add_eq_one v (by omega) hw
  have hu' : (1 + cellRatio v y 0 * x) ≠ 0 := ne_zero_of_valued_eq_one v hu
  have hr0' : cellRatio v y 0 ≠ 0 := by
    intro h; rw [h, map_zero] at hr0; exact WithZero.exp_ne_zero hr0.symm
  have hQ' : cellRatio v y 1 - cellRatio v y 0 * cellRatio v y 2 ≠ 0 := by
    intro h; rw [h, map_zero] at hQ; exact WithZero.exp_ne_zero hQ.symm

  have hcorner : cornerEntry v (y * lowerUnipotent10 v x) = cornerEntry v y * (1 + cellRatio v y 0 * x) := by
    rw [cornerEntry_mul_of_ne_zero v hc]
    simp only [e00, e10, e20]; ring
  have hlower : lowerMinor v (y * lowerUnipotent10 v x) = lowerMinor v y := by
    rw [lowerMinor_mul_of_ne_zero v hc hl]
    simp only [e00, e01, e10, e11, e20, e21]; ring
  have hdet : gl3Det v (y * lowerUnipotent10 v x) = gl3Det v y := by
    rw [gl3Det_mul]
    have : gl3Det v (lowerUnipotent10 v x) = 1 := by
      simp only [gl3Det, Matrix.det_fin_three]
      have e' : ∀ i j, (lowerUnipotent10 v x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
          gl3Entry v (lowerUnipotent10 v x) i j := fun _ _ => rfl
      simp only [e', e00, e01, e02, e10, e11, e12, e20, e21, e22]; ring
    rw [this, mul_one]
  have hc' : cornerEntry v (y * lowerUnipotent10 v x) ≠ 0 := by rw [hcorner]; exact mul_ne_zero hc hu'
  have hl' : lowerMinor v (y * lowerUnipotent10 v x) ≠ 0 := by rwa [hlower]
  have hcell' : y * lowerUnipotent10 v x ∈ bigCell3 v := (mem_bigCell3_iff v _).mpr ⟨hc', hl'⟩
  have hratio0 : cellRatio v (y * lowerUnipotent10 v x) 0 = cellRatio v y 0 * (1 + cellRatio v y 0 * x)⁻¹ := by
    rw [cellRatio_zero, gl3Entry_two_one_mul_of_ne_zero v hc, hcorner]
    simp only [e01, e11, e21]; field_simp; ring
  have hratio1 : cellRatio v (y * lowerUnipotent10 v x) 1 = cellRatio v y 1 * (1 + cellRatio v y 0 * x)⁻¹ := by
    rw [cellRatio_one, gl3Entry_two_two_mul_of_ne_zero v hc, hcorner]
    simp only [e02, e12, e22]; field_simp; ring
  have hratio2 : cellRatio v (y * lowerUnipotent10 v x) 2 =
      cellRatio v y 2 - (cellRatio v y 1 - cellRatio v y 0 * cellRatio v y 2) * x := by
    rw [cellRatio_two, outerMinor_mul_of_ne_zero v hc hl, hlower]
    simp only [e00, e02, e10, e12, e20, e22]; field_simp; ring
  have hinv : cellRatio v (y * lowerUnipotent10 v x) 1 -
      cellRatio v (y * lowerUnipotent10 v x) 0 * cellRatio v (y * lowerUnipotent10 v x) 2 =
        cellRatio v y 1 - cellRatio v y 0 * cellRatio v y 2 := by
    have h1 := cellInvariant_eq_of_ne_zero v hc' hl'
    have h2 := cellInvariant_eq_of_ne_zero v hc hl
    unfold cellInvariant at h1 h2
    rw [h1, h2, hlower, rightMinor_mul]
    simp only [e01, e02, e11, e12, e21, e22]; ring

  have hv0 : Valued.v (cellRatio v (y * lowerUnipotent10 v x) 0) = WithZero.exp (-(a₂ : ℤ)) := by
    rw [hratio0, map_mul, map_inv₀, hu, inv_one, mul_one, hr0]
  have hv1 : Valued.v (cellRatio v (y * lowerUnipotent10 v x) 1) ≤ WithZero.exp (-(a₂ : ℤ)) := by
    rw [hratio1, map_mul, map_inv₀, hu, inv_one, mul_one]; exact hr1
  have hv2 : Valued.v (cellRatio v (y * lowerUnipotent10 v x) 2) ≤ 1 := by
    rw [hratio2]
    refine Valuation.map_sub_le _ hr2 ?_
    rw [map_mul, hQ]
    calc WithZero.exp (-((a₁ : ℤ) + a₂)) * Valued.v x ≤ WithZero.exp (-((a₁ : ℤ) + a₂)) * WithZero.exp (1 : ℤ) :=
          mul_le_mul' le_rfl hx
      _ ≤ 1 := by rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hvQ : Valued.v (cellRatio v (y * lowerUnipotent10 v x) 1 -
      cellRatio v (y * lowerUnipotent10 v x) 0 * cellRatio v (y * lowerUnipotent10 v x) 2) =
        WithZero.exp (-((a₁ : ℤ) + a₂)) := by rw [hinv]; exact hQ
  have hmem' : y * lowerUnipotent10 v x ∈ cellSupport v ν a₁ a₂ := by
    refine ⟨hcell', ?_⟩
    rw [conductorDatum_apply_of_support v ν a₁ a₂ hv2 hv1 hvQ hv0, hinv, hratio0]
    exact mul_ne_zero (charExt_ne_zero v _ hQ') (charExt_ne_zero v _ (mul_ne_zero hr0' (inv_ne_zero hu')))
  refine ⟨hmem', ?_⟩
  rw [cellSectionOf_conductorDatum_apply_of_mem v ν a₁ a₂ hmem', cellSectionOf_conductorDatum_apply_of_mem v ν a₁ a₂
    ⟨hcell, hΦ⟩, conductorDatum_apply_of_support v ν a₁ a₂ hv2 hv1 hvQ hv0,
    conductorDatum_apply_of_support v ν a₁ a₂ hr2 hr1 hQ hr0, hinv, hratio0]
  unfold cellValue
  rw [hdet, hlower, hcorner, charExt_mul_of_ne_zero v _ hc hu',
    charExt_mul_of_ne_zero v _ hr0' (inv_ne_zero hu'), charExt_inv_apply v (ν 1) (1 + cellRatio v y 0 * x)⁻¹,
    charExt_inv_of_ne_zero v (ν 1) hu', inv_inv, norm_mul, norm_eq_one_of_valued_eq_one v hu, mul_one]

  have hsplit : charExt (ν 1) (lowerMinor v y / (cornerEntry v y * (1 + cellRatio v y 0 * x))) =
      charExt (ν 1) (lowerMinor v y / cornerEntry v y) * (charExt (ν 1) (1 + cellRatio v y 0 * x))⁻¹ := by
    rw [div_mul_eq_div_div, div_eq_mul_inv _ (1 + _), charExt_mul_of_ne_zero v _ (div_ne_zero hl hc) (inv_ne_zero hu'),
      charExt_inv_of_ne_zero v _ hu']
  rw [hsplit]
  have hn := charExt_ne_zero v (ν 1) hu'
  push_cast
  field_simp

end Law

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField Matrix

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section CentralLaw

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem diagonal3_const_mul_comm (z : (v.adicCompletion ℚ)ˣ) (m : LocalGL3 v) :
    diagonal3 v (fun _ => z) * m = m * diagonal3 v (fun _ => z) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have hd : ((diagonal3 v (fun _ => z) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
      = diagonal fun _ => (z : v.adicCompletion ℚ) := rfl
  rw [hd, ← Matrix.scalar_apply]
  exact (Matrix.scalar_commute (n := Fin 3) (z : v.adicCompletion ℚ) (Commute.all _) _).eq

private theorem halfModulus3_const (z : (v.adicCompletion ℚ)ˣ) : halfModulus3 v (fun _ => z) = 1 := by
  unfold halfModulus3
  rw [div_self (norm_ne_zero_iff.mpr z.ne_zero)]
  exact Complex.ofReal_one

private theorem torusChar3_ne_zero (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ a ≠ 0 := by
  unfold torusChar3
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero _

private theorem jacquetLevel_smul {c : ℂ} (hc : c ≠ 0) (u : LocalGL3 v → ℂ) : jacquetLevel v (c • u) = jacquetLevel v u := by
  unfold jacquetLevel
  congr 1
  ext c₀
  simp only [Set.mem_setOf_eq, jacquetTruncated3_smul, mul_right_inj' hc]

private theorem jacquetValue_smul {c : ℂ} (hc : c ≠ 0) (u : LocalGL3 v → ℂ) :
    jacquetValue v (c • u) = c * jacquetValue v u := by
  unfold jacquetValue
  rw [jacquetLevel_smul v hc, jacquetTruncated3_smul]

private theorem jacquetValue_const_mul (c : ℂ) (u : LocalGL3 v → ℂ) :
    jacquetValue v (fun y => c * u y) = c * jacquetValue v u := by
  show jacquetValue v (c • u) = c * jacquetValue v u
  by_cases hc : c = 0
  · subst hc
    unfold jacquetValue
    rw [jacquetTruncated3_smul, zero_mul, zero_mul]
  · exact jacquetValue_smul v hc u

private theorem gl3AmbientRightTranslate_mul_diagonal3_const_cellSectionOf (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (g : LocalGL3 v) (z : (v.adicCompletion ℚ)ˣ) :
    gl3AmbientRightTranslate (R := ℂ) (g * diagonal3 v (fun _ => z)) (cellSectionOf v χ Φ)
      = torusChar3 v χ (fun _ => z) • gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ) := by
  funext h
  simp only [gl3AmbientRightTranslate_apply, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← diagonal3_const_mul_comm v z (h * g), cellSectionOf_diagonal3_mul, halfModulus3_const, mul_one]

private theorem jacquetValue_translate_mul_diagonal3_const (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (g : LocalGL3 v) (z : (v.adicCompletion ℚ)ˣ) :
    jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (g * diagonal3 v (fun _ => z)) (cellSectionOf v χ Φ))
      = torusChar3 v χ (fun _ => z)
          * jacquetValue v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ)) := by
  rw [gl3AmbientRightTranslate_mul_diagonal3_const_cellSectionOf, jacquetValue_smul v (torusChar3_ne_zero v χ _)]

private theorem jacquetWhittaker3_mul_diagonal3_const (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (g : LocalGL3 v) (z : (v.adicCompletion ℚ)ˣ) :
    jacquetWhittaker3 v χ Φ (g * diagonal3 v (fun _ => z))
      = torusChar3 v χ (fun _ => z) * jacquetWhittaker3 v χ Φ g := by
  rw [jacquetWhittaker3_apply, jacquetWhittaker3_apply, jacquetValue_translate_mul_diagonal3_const]

private theorem torusChar3_const (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (z : (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ (fun _ => z) = ∏ i : Fin 3, ((χ i z : ℂˣ) : ℂ) := rfl

end CentralLaw

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

noncomputable section

p2m_open "IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal Matrix"
open MeasureTheory

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section BasicStabilisation

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl3Entry_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) (i j : Fin 3) :
    gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) i j =
      !![(0 : v.adicCompletion ℚ), 0, 1; 0, 1, y; 1, x, z] i j := by
  rw [gl3Entry, Units.val_mul, antidiagonal3_coe, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem cornerEntry_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    cornerEntry v (antidiagonal3 v * upperUnipotent3 x y z) = 1 := by
  simp [cornerEntry, gl3Entry_antidiagonal3_mul_upperUnipotent3]

private theorem lowerMinor_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    lowerMinor v (antidiagonal3 v * upperUnipotent3 x y z) = -1 := by
  simp [lowerMinor, gl3Entry_antidiagonal3_mul_upperUnipotent3]

private theorem outerMinor_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    outerMinor v (antidiagonal3 v * upperUnipotent3 x y z) = -y := by
  simp [outerMinor, gl3Entry_antidiagonal3_mul_upperUnipotent3]

private theorem antidiagonal3_mul_upperUnipotent3_mem_bigCell3 (x y z : v.adicCompletion ℚ) :
    antidiagonal3 v * upperUnipotent3 x y z ∈ bigCell3 v := by
  rw [mem_bigCell3_iff, cornerEntry_antidiagonal3_mul_upperUnipotent3, lowerMinor_antidiagonal3_mul_upperUnipotent3]
  exact ⟨one_ne_zero, neg_ne_zero.mpr one_ne_zero⟩

private theorem cellRatio_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    cellRatio v (antidiagonal3 v * upperUnipotent3 x y z) = ![x, z, y] := by
  funext i
  fin_cases i <;>
    simp [cellRatio, gl3Entry_antidiagonal3_mul_upperUnipotent3, lowerMinor_antidiagonal3_mul_upperUnipotent3,
      outerMinor_antidiagonal3_mul_upperUnipotent3, cornerEntry]

private theorem cellValue_antidiagonal3_mul_upperUnipotent3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (x y z : v.adicCompletion ℚ) :
    cellValue v χ (antidiagonal3 v * upperUnipotent3 x y z) = cellValue v χ (antidiagonal3 v) := by
  have hdet : gl3Det v (antidiagonal3 v * upperUnipotent3 x y z) = gl3Det v (antidiagonal3 v) := by
    have h1 : Matrix.det !![(1 : v.adicCompletion ℚ), x, z; 0, 1, y; 0, 0, 1] = 1 := by
      simp [Matrix.det_fin_three]
    rw [gl3Det, gl3Det, Units.val_mul, Matrix.det_mul, upperUnipotent3_coe, h1, mul_one]
  unfold cellValue
  rw [hdet, lowerMinor_antidiagonal3_mul_upperUnipotent3, cornerEntry_antidiagonal3_mul_upperUnipotent3,
    lowerMinor_antidiagonal3, cornerEntry_antidiagonal3]

private theorem cellSectionOf_antidiagonal3_mul_upperUnipotent3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (x y z : v.adicCompletion ℚ) :
    cellSectionOf v χ Φ (antidiagonal3 v * upperUnipotent3 x y z) =
      cellValue v χ (antidiagonal3 v) * Φ ![x, z, y] := by
  rw [cellSectionOf_apply_of_mem v χ Φ (antidiagonal3_mul_upperUnipotent3_mem_bigCell3 v x y z),
    cellValue_antidiagonal3_mul_upperUnipotent3, cellRatio_antidiagonal3_mul_upperUnipotent3]

private def unipotentBox3 (R : ℤ) : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  {p | Valued.v p.1 ≤ WithZero.exp R ∧ Valued.v p.2.1 ≤ WithZero.exp R ∧ Valued.v p.2.2 ≤ WithZero.exp R}

private theorem mem_unipotentBox3_iff (R : ℤ) (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    p ∈ unipotentBox3 v R ↔
      Valued.v p.1 ≤ WithZero.exp R ∧ Valued.v p.2.1 ≤ WithZero.exp R ∧ Valued.v p.2.2 ≤ WithZero.exp R :=
  Iff.rfl

private theorem unipotentBox3_subset_unipotentBall3 {R c : ℤ} (hR : 0 ≤ R) (hRc : R ≤ c) :
    unipotentBox3 v R ⊆ unipotentBall3 v c := by
  intro p hp
  rw [mem_unipotentBox3_iff] at hp
  rw [mem_unipotentBall3_iff]
  have h1 : WithZero.exp R ≤ WithZero.exp c := WithZero.exp_le_exp.mpr hRc
  have h2 : WithZero.exp R ≤ WithZero.exp (2 * c) := WithZero.exp_le_exp.mpr (by omega)
  exact ⟨hp.1.trans h1, hp.2.1.trans h1, hp.2.2.trans h2⟩

private theorem isClopen_valued_le (c : ℤ) : IsClopen {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} := by
  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective ℚ (WithZero.exp c)
  have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v a := by
    rw [ha]
    exact zero_lt_iff.mpr WithZero.exp_ne_zero
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} =
      (fun x => a⁻¹ * x) ⁻¹' {y : v.adicCompletion ℚ | Valued.v y ≤ 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.map_mul, map_inv₀, ← ha]
    rw [inv_mul_le_iff₀ hpos, mul_one]
  rw [hset]
  exact (isClopen_valued_le_one v).preimage (continuous_const.mul continuous_id)

private theorem measurableSet_unipotentBall3 (c : ℤ) :
    @MeasurableSet _ (@Prod.instMeasurableSpace _ _ (localBorel ℚ v)
      (@Prod.instMeasurableSpace _ _ (localBorel ℚ v) (localBorel ℚ v))) (unipotentBall3 v c) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hA : MeasurableSet {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} :=
    (isClopen_valued_le v c).isOpen.measurableSet
  have hB : MeasurableSet {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (2 * c)} :=
    (isClopen_valued_le v (2 * c)).isOpen.measurableSet
  exact (hA.preimage measurable_fst).inter
    ((hA.preimage (measurable_fst.comp measurable_snd)).inter (hB.preimage (measurable_snd.comp measurable_snd)))

private theorem jacquetTruncated3_cellSectionOf_eq_setIntegral_box (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {R : ℤ} (hR : 0 ≤ R)
    (hΦ : ∀ r : Fin 3 → v.adicCompletion ℚ, (∃ i, WithZero.exp R < Valued.v (r i)) → Φ r = 0)
    {c : ℤ} (hRc : R ≤ c) :
    jacquetTruncated3 v c (cellSectionOf v χ Φ) =
      @MeasureTheory.integral _ ℂ _ _
        (@Prod.instMeasurableSpace _ _ (localBorel ℚ v)
          (@Prod.instMeasurableSpace _ _ (localBorel ℚ v) (localBorel ℚ v)))
        ((jacquetHaar3 v).restrict (unipotentBox3 v R))
        (fun p => psiLocal ℚ v (-(p.1 + p.2.1)) * (cellValue v χ (antidiagonal3 v) * Φ ![p.1, p.2.2, p.2.1])) := by
  letI := localBorel ℚ v
  unfold jacquetTruncated3
  simp only [cellSectionOf_antidiagonal3_mul_upperUnipotent3]
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero (measurableSet_unipotentBall3 v c)
    (unipotentBox3_subset_unipotentBall3 v hR hRc) ?_
  intro p hp
  have hp' : ¬ (Valued.v p.1 ≤ WithZero.exp R ∧ Valued.v p.2.1 ≤ WithZero.exp R ∧
      Valued.v p.2.2 ≤ WithZero.exp R) := fun h => hp.2 ((mem_unipotentBox3_iff v R p).mpr h)
  have hex : ∃ i, WithZero.exp R < Valued.v ((![p.1, p.2.2, p.2.1] : Fin 3 → v.adicCompletion ℚ) i) := by
    by_cases h1 : Valued.v p.1 ≤ WithZero.exp R
    · by_cases h2 : Valued.v p.2.1 ≤ WithZero.exp R
      · have h3 : ¬ Valued.v p.2.2 ≤ WithZero.exp R := fun h3 => hp' ⟨h1, h2, h3⟩
        exact ⟨1, by simpa using not_le.mp h3⟩
      · exact ⟨2, by simpa using not_le.mp h2⟩
    · exact ⟨0, by simpa using not_le.mp h1⟩
  rw [hΦ _ hex, mul_zero, mul_zero]

private theorem jacquetTruncated3_cellSectionOf_eq_of_le (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {R : ℤ} (hR : 0 ≤ R)
    (hΦ : ∀ r : Fin 3 → v.adicCompletion ℚ, (∃ i, WithZero.exp R < Valued.v (r i)) → Φ r = 0)
    {c c' : ℤ} (hRc : R ≤ c) (hRc' : R ≤ c') :
    jacquetTruncated3 v c (cellSectionOf v χ Φ) = jacquetTruncated3 v c' (cellSectionOf v χ Φ) := by
  rw [jacquetTruncated3_cellSectionOf_eq_setIntegral_box v χ Φ hR hΦ hRc,
    jacquetTruncated3_cellSectionOf_eq_setIntegral_box v χ Φ hR hΦ hRc']

private theorem exists_jacquetTruncated3_cellSectionOf_const (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {R : ℤ} (hR : 0 ≤ R)
    (hΦ : ∀ r : Fin 3 → v.adicCompletion ℚ, (∃ i, WithZero.exp R < Valued.v (r i)) → Φ r = 0) :
    ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      jacquetTruncated3 v c (cellSectionOf v χ Φ) = jacquetTruncated3 v c₀ (cellSectionOf v χ Φ) := by
  refine ⟨R.toNat, fun c hc => ?_⟩
  rw [Int.toNat_of_nonneg hR] at hc ⊢
  exact jacquetTruncated3_cellSectionOf_eq_of_le v χ Φ hR hΦ hc le_rfl

private theorem jacquetLevel_cellSectionOf_le (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {R : ℤ} (hR : 0 ≤ R)
    (hΦ : ∀ r : Fin 3 → v.adicCompletion ℚ, (∃ i, WithZero.exp R < Valued.v (r i)) → Φ r = 0) :
    (jacquetLevel v (cellSectionOf v χ Φ) : ℤ) ≤ R := by
  have h : jacquetLevel v (cellSectionOf v χ Φ) ≤ R.toNat := by
    refine jacquetLevel_le v (cellSectionOf v χ Φ) (c₀ := R.toNat) fun c hc => ?_
    rw [Int.toNat_of_nonneg hR] at hc ⊢
    exact jacquetTruncated3_cellSectionOf_eq_of_le v χ Φ hR hΦ hc le_rfl
  calc (jacquetLevel v (cellSectionOf v χ Φ) : ℤ) ≤ (R.toNat : ℤ) := by exact_mod_cast h
    _ = R := Int.toNat_of_nonneg hR

private theorem jacquetValue_cellSectionOf_eq_setIntegral_box (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {R : ℤ} (hR : 0 ≤ R)
    (hΦ : ∀ r : Fin 3 → v.adicCompletion ℚ, (∃ i, WithZero.exp R < Valued.v (r i)) → Φ r = 0) :
    jacquetValue v (cellSectionOf v χ Φ) =
      @MeasureTheory.integral _ ℂ _ _
        (@Prod.instMeasurableSpace _ _ (localBorel ℚ v)
          (@Prod.instMeasurableSpace _ _ (localBorel ℚ v) (localBorel ℚ v)))
        ((jacquetHaar3 v).restrict (unipotentBox3 v R))
        (fun p => psiLocal ℚ v (-(p.1 + p.2.1)) * (cellValue v χ (antidiagonal3 v) * Φ ![p.1, p.2.2, p.2.1])) := by
  rw [← jacquetTruncated3_eq_jacquetValue v (cellSectionOf v χ Φ)
      (exists_jacquetTruncated3_cellSectionOf_const v χ Φ hR hΦ) (jacquetLevel_cellSectionOf_le v χ Φ hR hΦ),
    jacquetTruncated3_cellSectionOf_eq_setIntegral_box v χ Φ hR hΦ le_rfl]

end BasicStabilisation

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section PsiLaw

variable (v : HeightOneSpectrum (𝓞 ℚ))

private abbrev Unip3 : Type := v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ

private noncomputable def unipotentShift (p₀ : Unip3 v) : Unip3 v ≃ₜ Unip3 v where
  toFun p := (p.1 + p₀.1, p.2.1 + p₀.2.1, p.2.2 + p₀.2.2 + p.1 * p₀.2.1)
  invFun p := (p.1 - p₀.1, p.2.1 - p₀.2.1, p.2.2 - p₀.2.2 - (p.1 - p₀.1) * p₀.2.1)
  left_inv p := by
    obtain ⟨a, b, d⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  right_inv p := by
    obtain ⟨a, b, d⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  continuous_toFun :=
    (continuous_fst.add continuous_const).prodMk
      (((continuous_fst.comp continuous_snd).add continuous_const).prodMk
        (((continuous_snd.comp continuous_snd).add continuous_const).add (continuous_fst.mul continuous_const)))
  continuous_invFun :=
    (continuous_fst.sub continuous_const).prodMk
      (((continuous_fst.comp continuous_snd).sub continuous_const).prodMk
        (((continuous_snd.comp continuous_snd).sub continuous_const).sub
          ((continuous_fst.sub continuous_const).mul continuous_const)))

private theorem unipotentShift_apply (p₀ p : Unip3 v) :
    unipotentShift v p₀ p = (p.1 + p₀.1, p.2.1 + p₀.2.1, p.2.2 + p₀.2.2 + p.1 * p₀.2.1) :=
  rfl

private theorem preimage_unipotentBall3_unipotentShift {c : ℤ} {p₀ : Unip3 v} (hp₀ : p₀ ∈ unipotentBall3 v c) :
    unipotentShift v p₀ ⁻¹' unipotentBall3 v c = unipotentBall3 v c := by
  ext p
  constructor
  · intro hp
    have hmem := unipotentBall3_mul_mem v (c := c) (p := unipotentShift v p₀ p)
      (p' := (-p₀.1, -p₀.2.1, p₀.1 * p₀.2.1 - p₀.2.2)) hp (unipotentBall3_inv_mem v hp₀)
    convert hmem using 1
    obtain ⟨a, b, d⟩ := p
    simp only [unipotentShift_apply, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  · intro hp
    exact unipotentBall3_mul_mem v hp hp₀

private theorem isAddHaarMeasure_selfDualHaarAt_rat :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  have hN : (0 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h0
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos hN).ne'

private theorem measurePreserving_unipotentShift (p₀ : Unip3 v) :
    letI := localBorel ℚ v
    MeasurePreserving (unipotentShift v p₀) (jacquetHaar3 v) (jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  have hshape : (unipotentShift v p₀ : Unip3 v → Unip3 v)
      = fun p : Unip3 v => (p₀.1 + p.1, (p₀.2.1, p₀.2.2 + p.1 * p₀.2.1) + p.2) := by
    funext p
    obtain ⟨a, b, d⟩ := p
    simp only [unipotentShift_apply, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  show MeasurePreserving (unipotentShift v p₀)
    ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
    ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
  rw [hshape]
  refine MeasurePreserving.skew_product
    (g := fun (a : v.adicCompletion ℚ) (q : v.adicCompletion ℚ × v.adicCompletion ℚ) =>
      (p₀.2.1, p₀.2.2 + a * p₀.2.1) + q)
    (measurePreserving_add_left (selfDualHaarAt ℚ v) p₀.1) ?_ ?_
  · exact (((continuous_const.prodMk (continuous_const.add (continuous_fst.mul continuous_const))).add
      continuous_snd) : Continuous fun q : v.adicCompletion ℚ × (v.adicCompletion ℚ × v.adicCompletion ℚ) =>
        (p₀.2.1, p₀.2.2 + q.1 * p₀.2.1) + q.2).measurable
  · exact Filter.Eventually.of_forall fun a =>
      map_add_left_eq_self ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) (p₀.2.1, p₀.2.2 + a * p₀.2.1)

private theorem jacquetTruncated3_rightTranslate_upperUnipotent3 (c : ℤ) (F : LocalGL3 v → ℂ) {p₀ : Unip3 v}
    (hp₀ : p₀ ∈ unipotentBall3 v c) :
    jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F)
      = psiLocal ℚ v (p₀.1 + p₀.2.1) * jacquetTruncated3 v c F := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  set G : Unip3 v → ℂ := fun p =>
    psiLocal ℚ v (-(p.1 + p.2.1)) * F (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) with hG
  have hint : ∀ p : Unip3 v,
      psiLocal ℚ v (-(p.1 + p.2.1))
          * gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F
              (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)
        = psiLocal ℚ v (p₀.1 + p₀.2.1) * G (unipotentShift v p₀ p) := by
    intro p
    simp only [hG, gl3AmbientRightTranslate_apply, unipotentShift_apply, mul_assoc,
      upperUnipotent3_mul_upperUnipotent3]
    rw [← mul_assoc (psiLocal ℚ v (p₀.1 + p₀.2.1)), ← AddChar.map_add_eq_mul]
    congr 2
    ring
  have hleft : jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F)
      = ∫ p in unipotentBall3 v c, psiLocal ℚ v (p₀.1 + p₀.2.1) * G (unipotentShift v p₀ p) ∂(jacquetHaar3 v) := by
    unfold jacquetTruncated3
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => hint p)
  have hright : jacquetTruncated3 v c F = ∫ p in unipotentBall3 v c, G p ∂(jacquetHaar3 v) := by
    unfold jacquetTruncated3
    rfl
  rw [hleft, hright, integral_const_mul]
  congr 1
  have hpre := (measurePreserving_unipotentShift v p₀).setIntegral_preimage_emb
    (unipotentShift v p₀).measurableEmbedding G (unipotentBall3 v c)
  rw [preimage_unipotentBall3_unipotentShift v hp₀] at hpre
  exact hpre

private theorem exists_mem_unipotentBall3 (p₀ : Unip3 v) : ∃ k : ℕ, p₀ ∈ unipotentBall3 v k := by
  have hbound : ∀ x : v.adicCompletion ℚ, ∃ n : ℕ, Valued.v x ≤ WithZero.exp (n : ℤ) := by
    intro x
    by_cases hx : Valued.v x = 0
    · exact ⟨0, by rw [hx]; exact zero_le'⟩
    · refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      calc Valued.v x = WithZero.exp (WithZero.log (Valued.v x)) := (WithZero.exp_log hx).symm
        _ ≤ WithZero.exp ((WithZero.log (Valued.v x)).toNat : ℤ) :=
          WithZero.exp_le_exp.mpr (Int.self_le_toNat _)
  obtain ⟨n₁, h₁⟩ := hbound p₀.1
  obtain ⟨n₂, h₂⟩ := hbound p₀.2.1
  obtain ⟨n₃, h₃⟩ := hbound p₀.2.2
  refine ⟨max n₁ (max n₂ n₃), ?_⟩
  simp only [mem_unipotentBall3_iff]
  refine ⟨h₁.trans (WithZero.exp_le_exp.mpr (by omega)), h₂.trans (WithZero.exp_le_exp.mpr (by omega)),
    h₃.trans (WithZero.exp_le_exp.mpr (by omega))⟩

private def Stabilises (u : LocalGL3 v → ℂ) : Prop :=
  ∃ L : ℕ, ∀ c : ℤ, (L : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v L u

private theorem jacquetValue_rightTranslate_upperUnipotent3 {F : LocalGL3 v → ℂ} (hF : Stabilises v F) (p₀ : Unip3 v) :
    jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F)
      = psiLocal ℚ v (p₀.1 + p₀.2.1) * jacquetValue v F := by
  obtain ⟨L, hL⟩ := hF
  obtain ⟨k, hk⟩ := exists_mem_unipotentBall3 v p₀
  set c : ℕ := max L k with hc
  have hkc : ∀ c' : ℤ, (c : ℤ) ≤ c' → p₀ ∈ unipotentBall3 v c' := fun c' hc' =>
    unipotentBall3_mono v (by omega) hk
  have hconst : ∀ c' : ℤ, (c : ℤ) ≤ c' →
      jacquetTruncated3 v c' (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F)
        = psiLocal ℚ v (p₀.1 + p₀.2.1) * jacquetTruncated3 v L F := by
    intro c' hc'
    rw [jacquetTruncated3_rightTranslate_upperUnipotent3 v c' F (hkc c' hc'), hL c' (by omega)]
  have hstab' : ∀ c' : ℤ, (c : ℤ) ≤ c' →
      jacquetTruncated3 v c' (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F)
        = jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F) := by
    intro c' hc'
    rw [hconst c' hc', hconst c le_rfl]
  have h1 := jacquetTruncated3_eq_jacquetValue v
    (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F) ⟨c, hstab'⟩
    (c := (c : ℤ)) (by exact_mod_cast jacquetLevel_le v _ hstab')
  have h2 := jacquetTruncated3_eq_jacquetValue v F ⟨L, hL⟩ (c := (c : ℤ))
    (by exact_mod_cast (jacquetLevel_le v F hL).trans (le_max_left L k))
  rw [← h1, hconst c le_rfl, ← h2, hL c (by omega)]

private theorem gl3AmbientRightTranslate_mul (a b : LocalGL3 v) (u : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) (a * b) u
      = gl3AmbientRightTranslate (R := ℂ) a (gl3AmbientRightTranslate (R := ℂ) b u) := by
  funext h
  simp only [gl3AmbientRightTranslate_apply, mul_assoc]

private theorem isGL3PsiWhittakerFn_jacquetValue_translate (u : LocalGL3 v → ℂ)
    (hstab : ∀ g : LocalGL3 v, Stabilises v (gl3AmbientRightTranslate (R := ℂ) g u)) (w : LocalGL3 v) :
    IsGL3PsiWhittakerFn (psiLocal ℚ v)
      fun g : LocalGL3 v => jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (g * w) u) := by
  intro x y z g
  show jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z * g * w) u)
    = psiLocal ℚ v (x + y) * jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (g * w) u)
  have h := jacquetValue_rightTranslate_upperUnipotent3 v (hstab (g * w)) (x, y, z)
  simp only at h
  rw [mul_assoc, gl3AmbientRightTranslate_mul v (upperUnipotent3 x y z) (g * w) u, h]

private theorem isGL3PsiWhittakerFn_jacquetWhittaker3_mul_antidiagonal3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hstab : ∀ g : LocalGL3 v, Stabilises v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ))) :
    IsGL3PsiWhittakerFn (psiLocal ℚ v) fun h : LocalGL3 v => jacquetWhittaker3 v χ Φ (h * antidiagonal3 v) :=
  isGL3PsiWhittakerFn_jacquetValue_translate v (cellSectionOf v χ Φ) hstab (antidiagonal3 v)

private theorem isGL3PsiWhittakerFn_jacquetWhittaker3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hstab : ∀ g : LocalGL3 v, Stabilises v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ))) :
    IsGL3PsiWhittakerFn (psiLocal ℚ v) (jacquetWhittaker3 v χ Φ) := by
  intro x y z g
  have h := jacquetValue_rightTranslate_upperUnipotent3 v (hstab g) (x, y, z)
  simp only at h
  rw [jacquetWhittaker3_apply, jacquetWhittaker3_apply,
    gl3AmbientRightTranslate_mul v (upperUnipotent3 x y z) g (cellSectionOf v χ Φ), h]

private def JacquetIntegrable (u : LocalGL3 v → ℂ) : Prop :=
  ∀ c : ℤ,
    letI := localBorel ℚ v
    IntegrableOn
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2))
      (unipotentBall3 v c) (jacquetHaar3 v)

private theorem jacquetIntegrable_zero : JacquetIntegrable v 0 := by
  intro c
  letI := localBorel ℚ v
  simp only [Pi.zero_apply, mul_zero]
  exact integrableOn_zero

private theorem jacquetIntegrable_add {u u' : LocalGL3 v → ℂ} (hu : JacquetIntegrable v u) (hu' : JacquetIntegrable v u') :
    JacquetIntegrable v (u + u') := by
  intro c
  letI := localBorel ℚ v
  simp only [Pi.add_apply, mul_add]
  exact (hu c).add (hu' c)

private theorem jacquetTruncated3_add_of_jacquetIntegrable {u u' : LocalGL3 v → ℂ} (hu : JacquetIntegrable v u)
    (hu' : JacquetIntegrable v u') (c : ℤ) :
    jacquetTruncated3 v c (u + u') = jacquetTruncated3 v c u + jacquetTruncated3 v c u' :=
  jacquetTruncated3_add v c u u' (hu c) (hu' c)

private theorem jacquetTruncated3_zero (c : ℤ) : jacquetTruncated3 v c 0 = 0 := by
  simpa using jacquetTruncated3_smul v c (0 : ℂ) (0 : LocalGL3 v → ℂ)

private theorem stabilises_zero : Stabilises v 0 :=
  ⟨0, fun c _ => by rw [jacquetTruncated3_zero, jacquetTruncated3_zero]⟩

private theorem stabilises_add {u u' : LocalGL3 v → ℂ} (hu : JacquetIntegrable v u) (hu' : JacquetIntegrable v u')
    (hs : Stabilises v u) (hs' : Stabilises v u') : Stabilises v (u + u') := by
  obtain ⟨L, hL⟩ := hs
  obtain ⟨L', hL'⟩ := hs'
  refine ⟨max L L', fun c hc => ?_⟩
  rw [jacquetTruncated3_add_of_jacquetIntegrable v hu hu' c,
    jacquetTruncated3_add_of_jacquetIntegrable v hu hu' (max L L' : ℕ), hL c (by omega), hL' c (by omega),
    hL (max L L' : ℕ) (by omega), hL' (max L L' : ℕ) (by omega)]

private theorem jacquetValue_zero : jacquetValue v 0 = 0 := by
  unfold jacquetValue
  exact jacquetTruncated3_zero v _

private theorem jacquetValue_add {u u' : LocalGL3 v → ℂ} (hu : JacquetIntegrable v u) (hu' : JacquetIntegrable v u')
    (hs : Stabilises v u) (hs' : Stabilises v u') :
    jacquetValue v (u + u') = jacquetValue v u + jacquetValue v u' := by
  have hsum : Stabilises v (u + u') := stabilises_add v hu hu' hs hs'
  obtain ⟨L, hL⟩ := hs
  obtain ⟨L', hL'⟩ := hs'
  set c : ℕ := max (max L L') (jacquetLevel v (u + u')) with hc
  have h1 := jacquetTruncated3_eq_jacquetValue v (u + u') hsum (c := (c : ℤ))
    (by exact_mod_cast le_max_right (max L L') (jacquetLevel v (u + u')))
  have h2 := jacquetTruncated3_eq_jacquetValue v u ⟨L, hL⟩ (c := (c : ℤ))
    (by exact_mod_cast (jacquetLevel_le v u hL).trans ((le_max_left L L').trans (le_max_left _ _)))
  have h3 := jacquetTruncated3_eq_jacquetValue v u' ⟨L', hL'⟩ (c := (c : ℤ))
    (by exact_mod_cast (jacquetLevel_le v u' hL').trans ((le_max_right L L').trans (le_max_left _ _)))
  rw [← h1, ← h2, ← h3]
  exact jacquetTruncated3_add_of_jacquetIntegrable v hu hu' c

private theorem jacquetIntegrable_sum {ι : Type*} (s : Finset ι) (f : ι → LocalGL3 v → ℂ)
    (hf : ∀ i ∈ s, JacquetIntegrable v (f i)) : JacquetIntegrable v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jacquetIntegrable_zero v
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact jacquetIntegrable_add v (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem stabilises_sum {ι : Type*} (s : Finset ι) (f : ι → LocalGL3 v → ℂ)
    (hf : ∀ i ∈ s, JacquetIntegrable v (f i)) (hs : ∀ i ∈ s, Stabilises v (f i)) :
    Stabilises v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using stabilises_zero v
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact stabilises_add v (hf a (Finset.mem_insert_self a s))
      (jacquetIntegrable_sum v s f fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (hs a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) fun i hi => hs i (Finset.mem_insert_of_mem hi))

private theorem jacquetValue_sum {ι : Type*} (s : Finset ι) (f : ι → LocalGL3 v → ℂ)
    (hf : ∀ i ∈ s, JacquetIntegrable v (f i)) (hs : ∀ i ∈ s, Stabilises v (f i)) :
    jacquetValue v (∑ i ∈ s, f i) = ∑ i ∈ s, jacquetValue v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jacquetValue_zero v
  | @insert a s ha ih =>
    have hf' : ∀ i ∈ s, JacquetIntegrable v (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hs' : ∀ i ∈ s, Stabilises v (f i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      jacquetValue_add v (hf a (Finset.mem_insert_self a s)) (jacquetIntegrable_sum v s f hf')
        (hs a (Finset.mem_insert_self a s)) (stabilises_sum v s f hf' hs'),
      ih hf' hs']

private theorem jacquetIntegrable_and_stabilises_of_exists_forall_le (u : LocalGL3 v → ℂ)
    (h : letI := localBorel ℚ v
      ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
        IntegrableOn
          (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
            psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2))
          (unipotentBall3 v c) (jacquetHaar3 v) ∧
        jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u) :
    JacquetIntegrable v u ∧ Stabilises v u := by
  obtain ⟨c₀, hc₀⟩ := h
  refine ⟨fun c => ?_, ⟨c₀, fun c hc => (hc₀ c hc).2⟩⟩
  by_cases hc : (c₀ : ℤ) ≤ c
  · exact (hc₀ c hc).1
  · exact (hc₀ c₀ le_rfl).1.mono_set (unipotentBall3_mono v (le_of_lt (not_le.mp hc)))

end PsiLaw

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section OneReduction

private def cornerPairs (a₂ : ℕ) : Set (v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  {q | Valued.v q.1 * WithZero.exp (a₂ : ℤ) = Valued.v q.2 ∧ WithZero.exp (a₂ : ℤ) ≤ Valued.v q.2}

private theorem mem_cornerPairs_iff (a₂ : ℕ) (x z : v.adicCompletion ℚ) :
    (x, z) ∈ cornerPairs v a₂ ↔
      Valued.v x * WithZero.exp (a₂ : ℤ) = Valued.v z ∧ WithZero.exp (a₂ : ℤ) ≤ Valued.v z :=
  Iff.rfl

private theorem ne_zero_of_mem_cornerPairs {a₂ : ℕ} {x z : v.adicCompletion ℚ} (h : (x, z) ∈ cornerPairs v a₂) :
    z ≠ 0 ∧ x ≠ 0 := by
  obtain ⟨hxz, hz⟩ := h
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hz
    exact WithZero.exp_ne_zero (le_antisymm hz zero_le')
  refine ⟨hz0, fun h0 => hz0 ?_⟩
  rw [h0, map_zero, zero_mul] at hxz
  exact (Valuation.zero_iff _).mp hxz.symm

private theorem one_le_valued_of_mem_cornerPairs {a₂ : ℕ} {x z : v.adicCompletion ℚ} (h : (x, z) ∈ cornerPairs v a₂) :
    1 ≤ Valued.v x := by
  obtain ⟨hxz, hz⟩ := h
  rw [← hxz] at hz
  by_contra hlt
  rw [not_le] at hlt
  have h1 : Valued.v x * WithZero.exp (a₂ : ℤ) < 1 * WithZero.exp (a₂ : ℤ) :=
    mul_lt_mul_of_pos_right hlt (lt_of_le_of_ne zero_le' WithZero.exp_ne_zero.symm)
  rw [one_mul] at h1
  exact lt_irrefl _ (lt_of_le_of_lt hz h1)

private theorem mem_cornerPairs_of_valued {a₂ : ℕ} {x z : v.adicCompletion ℚ}
    (hx : Valued.v x = WithZero.exp (a₂ : ℤ)) (hz : Valued.v z = WithZero.exp (2 * (a₂ : ℤ))) :
    (x, z) ∈ cornerPairs v a₂ := by
  refine ⟨?_, ?_⟩
  · rw [hx, hz, ← WithZero.exp_add]
    have e : (a₂ : ℤ) + a₂ = 2 * (a₂ : ℤ) := by ring
    rw [e]
  · rw [hz, WithZero.exp_le_exp]
    omega

private theorem valued_eq_of_mem_cornerPairs {a₂ : ℕ} {x z : v.adicCompletion ℚ} (h : (x, z) ∈ cornerPairs v a₂)
    (hx : Valued.v x = WithZero.exp (a₂ : ℤ)) : Valued.v z = WithZero.exp (2 * (a₂ : ℤ)) := by
  rw [← h.1, hx, ← WithZero.exp_add]
  have e : (a₂ : ℤ) + a₂ = 2 * (a₂ : ℤ) := by ring
  rw [e]

private theorem valued_corner_le_of_mem_cornerPairs {a₁ a₂ : ℕ} {x z : v.adicCompletion ℚ}
    (h : (x, z) ∈ cornerPairs v a₂) {y : v.adicCompletion ℚ}
    (hy : Valued.v (x * y - z) = WithZero.exp ((a₁ : ℤ) + a₂)) :
    Valued.v y ≤ WithZero.exp ((a₁ : ℤ) + a₂) := by
  by_contra hlt
  rw [not_le] at hlt
  have hx1 := one_le_valued_of_mem_cornerPairs v h
  have hx0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr (ne_zero_of_mem_cornerPairs v h).2
  have hzlt : Valued.v z < Valued.v (x * y) := by
    rw [map_mul, ← h.1]
    refine mul_lt_mul_of_pos_left (lt_of_le_of_lt ?_ hlt) (lt_of_le_of_ne zero_le' hx0.symm)
    rw [WithZero.exp_le_exp]
    omega
  have hbig : WithZero.exp ((a₁ : ℤ) + a₂) < Valued.v (x * y) := by
    rw [map_mul]
    calc WithZero.exp ((a₁ : ℤ) + a₂) < Valued.v y := hlt
      _ = 1 * Valued.v y := (one_mul _).symm
      _ ≤ Valued.v x * Valued.v y := mul_le_mul' hx1 le_rfl
  rw [Valuation.map_sub_eq_of_lt_left _ hzlt] at hy
  rw [hy] at hbig
  exact lt_irrefl _ hbig

private theorem corner_ratio_conditions {a₁ a₂ : ℕ} {x z : v.adicCompletion ℚ} (h : (x, z) ∈ cornerPairs v a₂)
    {y : v.adicCompletion ℚ} (hy : Valued.v (x * y - z) = WithZero.exp ((a₁ : ℤ) + a₂)) :
    Valued.v (y / (x * y - z)) ≤ 1 ∧ Valued.v (1 / z) ≤ WithZero.exp (-(a₂ : ℤ)) ∧
      Valued.v (-(1 / (x * y - z))) = WithZero.exp (-((a₁ : ℤ) + a₂)) ∧
        Valued.v (x / z) = WithZero.exp (-(a₂ : ℤ)) := by
  have hvz : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr (ne_zero_of_mem_cornerPairs v h).1
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr (ne_zero_of_mem_cornerPairs v h).2
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v z = WithZero.exp m := ⟨_, (WithZero.exp_log hvz).symm⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v x = WithZero.exp k := ⟨_, (WithZero.exp_log hvx).symm⟩
  obtain ⟨hxz, hz⟩ := h
  have ham : (a₂ : ℤ) ≤ m := by rwa [hm, WithZero.exp_le_exp] at hz
  have hkm : k + a₂ = m := by
    rw [hk, hm, ← WithZero.exp_add] at hxz
    exact WithZero.exp_inj.mp hxz
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_div₀, hy, div_le_one₀ (lt_of_le_of_ne zero_le' WithZero.exp_ne_zero.symm)]
    exact valued_corner_le_of_mem_cornerPairs v ⟨hxz, hz⟩ hy
  · rw [map_div₀, map_one, one_div, hm, ← WithZero.exp_neg, WithZero.exp_le_exp]
    omega
  · rw [Valuation.map_neg, map_div₀, map_one, one_div, hy, ← WithZero.exp_neg]
  · rw [map_div₀, hk, hm, ← WithZero.exp_sub, ← hkm]
    have e : k - (k + (a₂ : ℤ)) = -(a₂ : ℤ) := by ring
    rw [e]

private theorem conductorDatum_corner_of_mem (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)
    {x z : v.adicCompletion ℚ} (h : (x, z) ∈ cornerPairs v a₂) {y : v.adicCompletion ℚ}
    (hy : Valued.v (x * y - z) = WithZero.exp ((a₁ : ℤ) + a₂)) :
    conductorDatum v ν a₁ a₂ ![x / z, 1 / z, y / (x * y - z)] =
      (charExt (ν 0) (-(1 / (x * y - z))))⁻¹ * (charExt (ν 1) (x / z))⁻¹ := by
  obtain ⟨hz0, -⟩ := ne_zero_of_mem_cornerPairs v h
  have hw0 : x * y - z ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  obtain ⟨c2, c1, cQ, c0⟩ := corner_ratio_conditions v h hy
  have c2' : Valued.v ((![x / z, 1 / z, y / (x * y - z)] : Fin 3 → v.adicCompletion ℚ) 2) ≤ 1 := c2
  have c1' : Valued.v ((![x / z, 1 / z, y / (x * y - z)] : Fin 3 → v.adicCompletion ℚ) 1) ≤
      WithZero.exp (-(a₂ : ℤ)) := c1
  have c0' : Valued.v ((![x / z, 1 / z, y / (x * y - z)] : Fin 3 → v.adicCompletion ℚ) 0) =
      WithZero.exp (-(a₂ : ℤ)) := c0
  have cQ' : Valued.v ((![x / z, 1 / z, y / (x * y - z)] : Fin 3 → v.adicCompletion ℚ) 1 -
      (![x / z, 1 / z, y / (x * y - z)] : Fin 3 → v.adicCompletion ℚ) 0 *
        (![x / z, 1 / z, y / (x * y - z)] : Fin 3 → v.adicCompletion ℚ) 2) =
      WithZero.exp (-((a₁ : ℤ) + a₂)) := by
    show Valued.v (1 / z - x / z * (y / (x * y - z))) = WithZero.exp (-((a₁ : ℤ) + a₂))
    rw [cellInvariant_lowerConj v hz0 hw0]
    exact cQ
  rw [conductorDatum_apply_of_support v ν a₁ a₂ c2' c1' cQ' c0']
  show charExt (ν 0)⁻¹ (1 / z - x / z * (y / (x * y - z))) * charExt (ν 1)⁻¹ (x / z) = _
  rw [cellInvariant_lowerConj v hz0 hw0, charExt_inv_apply, charExt_inv_apply]

private theorem conductorDatum_corner_eq_zero (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)
    {x y z : v.adicCompletion ℚ} (hz0 : z ≠ 0) (hw0 : x * y - z ≠ 0)
    (h : ¬ ((x, z) ∈ cornerPairs v a₂ ∧ Valued.v (x * y - z) = WithZero.exp ((a₁ : ℤ) + a₂))) :
    conductorDatum v ν a₁ a₂ ![x / z, 1 / z, y / (x * y - z)] = 0 := by
  by_contra hne
  obtain ⟨-, h1, hQ, h0⟩ := conductorDatum_support v ν a₁ a₂ hne
  have h1' : Valued.v (1 / z) ≤ WithZero.exp (-(a₂ : ℤ)) := h1
  have h0' : Valued.v (x / z) = WithZero.exp (-(a₂ : ℤ)) := h0
  have hQ' : Valued.v (1 / z - x / z * (y / (x * y - z))) = WithZero.exp (-((a₁ : ℤ) + a₂)) := hQ
  rw [cellInvariant_lowerConj v hz0 hw0, Valuation.map_neg, map_div₀, map_one, one_div] at hQ'
  have hvz : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
  have hvw : Valued.v (x * y - z) ≠ 0 := (Valuation.ne_zero_iff _).mpr hw0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v z = WithZero.exp m := ⟨_, (WithZero.exp_log hvz).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (x * y - z) = WithZero.exp n := ⟨_, (WithZero.exp_log hvw).symm⟩
  rw [hn, ← WithZero.exp_neg, WithZero.exp_inj] at hQ'
  rw [map_div₀, map_one, one_div, hm, ← WithZero.exp_neg, WithZero.exp_le_exp] at h1'
  rw [map_div₀, div_eq_iff hvz, hm, ← WithZero.exp_add] at h0'
  refine h ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h0', hm, ← WithZero.exp_add]
    have e : -(a₂ : ℤ) + m + a₂ = m := by ring
    rw [e]
  · rw [hm, WithZero.exp_le_exp]
    omega
  · rw [hn, WithZero.exp_inj]
    omega

private def cornerShell (n : ℤ) (x z : v.adicCompletion ℚ) : Set (v.adicCompletion ℚ) :=
  {y | Valued.v (x * y - z) = WithZero.exp n}

private def cornerIntegrand (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (x z y : v.adicCompletion ℚ) : ℂ :=
  psiLocal ℚ v (-y) * charExt ξ ((x * y - z) / x)

private def outerWeight (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (r : ℝ) (q : v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ℂ :=
  (charExt (ν 0) (-1))⁻¹ * psiLocal ℚ v (-q.1) * charExt (ν 2) q.2 * ((r⁻¹ / ‖q.2‖ : ℝ) : ℂ)

private theorem psiLocal_mul_cellSectionOf_lowerConj_eq (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {a₁ a₂ : ℕ} {r : ℝ}
    (hr : ∀ w : v.adicCompletion ℚ, Valued.v w = WithZero.exp ((a₁ : ℤ) + a₂) → ‖w‖ = r)
    (x y z : v.adicCompletion ℚ) :
    psiLocal ℚ v (-(x + y)) * cellSectionOf v ν (conductorDatum v ν a₁ a₂) (lowerConj v x y z) =
      (cornerPairs v a₂).indicator (outerWeight v ν r) (x, z) *
        (cornerShell v ((a₁ : ℤ) + a₂) x z).indicator (cornerIntegrand v (ν 1) x z) y := by
  rw [cellSectionOf_conductorDatum_lowerConj]
  by_cases hS : (x, z) ∈ cornerPairs v a₂ ∧ Valued.v (x * y - z) = WithZero.exp ((a₁ : ℤ) + a₂)
  · obtain ⟨hz0, hx0⟩ := ne_zero_of_mem_cornerPairs v hS.1
    have hw0 : x * y - z ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hS
      exact WithZero.exp_ne_zero hS.2.symm
    have hyS : y ∈ cornerShell v ((a₁ : ℤ) + a₂) x z := hS.2
    rw [Set.indicator_of_mem hS.1, Set.indicator_of_mem hyS, conductorDatum_corner_of_mem v ν a₁ a₂ hS.1 hS.2]
    dsimp only [outerWeight, cornerIntegrand]
    have hA0 : charExt (ν 0) (x * y - z)⁻¹ ≠ 0 := charExt_ne_zero v (ν 0) (inv_ne_zero hw0)
    have hB1 : charExt (ν 1) z ≠ 0 := charExt_ne_zero v (ν 1) hz0
    rw [neg_add, AddChar.map_add_eq_mul, one_div, neg_eq_neg_one_mul (x * y - z)⁻¹,
      charExt_mul_of_ne_zero v (ν 0) (neg_ne_zero.mpr one_ne_zero) (inv_ne_zero hw0),
      charExt_div_of_ne_zero v (ν 1) hw0 hz0, charExt_div_of_ne_zero v (ν 1) hx0 hz0,
      charExt_div_of_ne_zero v (ν 1) hw0 hx0, norm_inv, hr _ hS.2]
    generalize ((r⁻¹ / ‖z‖ : ℝ) : ℂ) = N
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    linear_combination
      (psiLocal ℚ v (-x) * psiLocal ℚ v (-y) * charExt (ν 1) (x * y - z) * charExt (ν 2) z * N *
          (charExt (ν 0) (-1))⁻¹ * (charExt (ν 1) x)⁻¹ * ((charExt (ν 1) z)⁻¹ * charExt (ν 1) z)) *
          mul_inv_cancel₀ hA0 +
        (psiLocal ℚ v (-x) * psiLocal ℚ v (-y) * charExt (ν 1) (x * y - z) * charExt (ν 2) z * N *
          (charExt (ν 0) (-1))⁻¹ * (charExt (ν 1) x)⁻¹) * inv_mul_cancel₀ hB1
  · have hR : (cornerPairs v a₂).indicator (outerWeight v ν r) (x, z) *
        (cornerShell v ((a₁ : ℤ) + a₂) x z).indicator (cornerIntegrand v (ν 1) x z) y = 0 := by
      by_cases hp : (x, z) ∈ cornerPairs v a₂
      · have hy : y ∉ cornerShell v ((a₁ : ℤ) + a₂) x z := fun hy => hS ⟨hp, hy⟩
        rw [Set.indicator_of_notMem hy, mul_zero]
      · rw [Set.indicator_of_notMem hp, zero_mul]
    rw [hR]
    by_cases hz0 : z = 0
    · rw [hz0, charExt_zero]
      simp only [mul_zero, zero_mul]
    by_cases hw0 : x * y - z = 0
    · rw [hw0, div_zero, charExt_zero]
      simp only [mul_zero, zero_mul]
    simp only [conductorDatum_corner_eq_zero v ν a₁ a₂ hz0 hw0 hS, mul_zero]

private theorem cornerShell_subset_ball {a₁ a₂ : ℕ} {x z : v.adicCompletion ℚ} (h : (x, z) ∈ cornerPairs v a₂) {c : ℤ}
    (hc : (a₁ : ℤ) + a₂ ≤ c) :
    cornerShell v ((a₁ : ℤ) + a₂) x z ⊆ {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp c} := by
  intro y hy
  exact (valued_corner_le_of_mem_cornerPairs v h hy).trans (by rw [WithZero.exp_le_exp]; exact hc)

private theorem unipotentBall3_eq_prod (c : ℤ) :
    unipotentBall3 v c =
      {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} ×ˢ
        ({y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp c} ×ˢ
          {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)}) := by
  ext p
  simp only [mem_unipotentBall3_iff, Set.mem_prod, Set.mem_setOf_eq]

private theorem jacquetTruncated3_translate_eq_iterated (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {a₁ a₂ : ℕ} {r : ℝ}
    (hr : ∀ w : v.adicCompletion ℚ, Valued.v w = WithZero.exp ((a₁ : ℤ) + a₂) → ‖w‖ = r)
    (hint : JacquetIntegrable v
      (gl3AmbientRightTranslate (R := ℂ) (antidiagonal3 v) (cellSectionOf v ν (conductorDatum v ν a₁ a₂))))
    {c : ℤ} (hc : (a₁ : ℤ) + a₂ ≤ c) :
    letI := localBorel ℚ v
    jacquetTruncated3 v c
        (gl3AmbientRightTranslate (R := ℂ) (antidiagonal3 v) (cellSectionOf v ν (conductorDatum v ν a₁ a₂))) =
      ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c},
        ∫ z in {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)},
          (cornerPairs v a₂).indicator (outerWeight v ν r) (x, z) *
            ∫ y in cornerShell v ((a₁ : ℤ) + a₂) x z, cornerIntegrand v (ν 1) x z y ∂selfDualHaarAt ℚ v
        ∂selfDualHaarAt ℚ v ∂selfDualHaarAt ℚ v := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  have hBc : MeasurableSet {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} :=
    measurableSet_closedBall_valued (WithZero.exp c)
  have hB2c : MeasurableSet {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)} :=
    measurableSet_closedBall_valued (WithZero.exp (2 * c))
  have hshell : ∀ x z : v.adicCompletion ℚ, MeasurableSet (cornerShell v ((a₁ : ℤ) + a₂) x z) := by
    intro x z
    have e : cornerShell v ((a₁ : ℤ) + a₂) x z =
        (fun y : v.adicCompletion ℚ => x * y - z) ⁻¹'
          {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp ((a₁ : ℤ) + a₂)} := rfl
    rw [e]
    exact ((continuous_const.mul continuous_id).sub continuous_const :
      Continuous fun y : v.adicCompletion ℚ => x * y - z).measurable
        (measurableSet_setOf_valued_eq_exp ((a₁ : ℤ) + a₂))
  have hpt : ∀ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
      psiLocal ℚ v (-(p.1 + p.2.1)) *
          gl3AmbientRightTranslate (R := ℂ) (antidiagonal3 v) (cellSectionOf v ν (conductorDatum v ν a₁ a₂))
            (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) =
        (cornerPairs v a₂).indicator (outerWeight v ν r) (p.1, p.2.2) *
          (cornerShell v ((a₁ : ℤ) + a₂) p.1 p.2.2).indicator (cornerIntegrand v (ν 1) p.1 p.2.2) p.2.1 := by
    intro p
    rw [rightTranslate_antidiagonal3_apply_antidiagonal3_mul]
    exact psiLocal_mul_cellSectionOf_lowerConj_eq v ν hr p.1 p.2.1 p.2.2
  have hE : IntegrableOn
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        (cornerPairs v a₂).indicator (outerWeight v ν r) (p.1, p.2.2) *
          (cornerShell v ((a₁ : ℤ) + a₂) p.1 p.2.2).indicator (cornerIntegrand v (ν 1) p.1 p.2.2) p.2.1)
      (unipotentBall3 v c) (jacquetHaar3 v) :=
    (hint c).congr_fun (fun p _ => hpt p) (by rw [unipotentBall3_eq_prod]; exact hBc.prod (hBc.prod hB2c))
  have hJ : jacquetHaar3 v = (selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) := rfl
  rw [unipotentBall3_eq_prod, hJ] at hE
  have hae := (by simpa only [IntegrableOn, ← Measure.prod_restrict] using hE :
    Integrable
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        (cornerPairs v a₂).indicator (outerWeight v ν r) (p.1, p.2.2) *
          (cornerShell v ((a₁ : ℤ) + a₂) p.1 p.2.2).indicator (cornerIntegrand v (ν 1) p.1 p.2.2) p.2.1)
      (((selfDualHaarAt ℚ v).restrict {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}).prod
        (((selfDualHaarAt ℚ v).restrict {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp c}).prod
          ((selfDualHaarAt ℚ v).restrict
            {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)})))).prod_right_ae
  simp only [jacquetTruncated3]
  calc
    ∫ p in unipotentBall3 v c, psiLocal ℚ v (-(p.1 + p.2.1)) *
          gl3AmbientRightTranslate (R := ℂ) (antidiagonal3 v) (cellSectionOf v ν (conductorDatum v ν a₁ a₂))
            (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) ∂jacquetHaar3 v
        = ∫ p in unipotentBall3 v c,
            (cornerPairs v a₂).indicator (outerWeight v ν r) (p.1, p.2.2) *
              (cornerShell v ((a₁ : ℤ) + a₂) p.1 p.2.2).indicator (cornerIntegrand v (ν 1) p.1 p.2.2) p.2.1
            ∂jacquetHaar3 v := by
          refine setIntegral_congr_fun ?_ fun p _ => hpt p
          rw [unipotentBall3_eq_prod]
          exact hBc.prod (hBc.prod hB2c)
    _ = ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c},
          ∫ q in {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp c} ×ˢ
              {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)},
            (cornerPairs v a₂).indicator (outerWeight v ν r) (x, q.2) *
              (cornerShell v ((a₁ : ℤ) + a₂) x q.2).indicator (cornerIntegrand v (ν 1) x q.2) q.1
            ∂(selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v) ∂selfDualHaarAt ℚ v := by
          rw [unipotentBall3_eq_prod, hJ]
          exact setIntegral_prod _ hE
    _ = ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c},
          ∫ z in {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)},
            ∫ y in {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp c},
              (cornerPairs v a₂).indicator (outerWeight v ν r) (x, z) *
                (cornerShell v ((a₁ : ℤ) + a₂) x z).indicator (cornerIntegrand v (ν 1) x z) y
            ∂selfDualHaarAt ℚ v ∂selfDualHaarAt ℚ v ∂selfDualHaarAt ℚ v := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with x hx
          rw [← Measure.prod_restrict]
          exact integral_prod_symm _ hx
    _ = _ := by
          refine setIntegral_congr_fun hBc fun x _ => ?_
          refine setIntegral_congr_fun hB2c fun z _ => ?_
          rw [integral_const_mul]
          by_cases hxz : (x, z) ∈ cornerPairs v a₂
          · rw [setIntegral_indicator (hshell x z), Set.inter_eq_right.mpr (cornerShell_subset_ball v hxz hc)]
          · rw [Set.indicator_of_notMem hxz, zero_mul, zero_mul]

end OneReduction

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem lowerUnipotent10_zero : lowerUnipotent10 v 0 = 1 := by
  unfold lowerUnipotent10
  rw [upperUnipotent3_zero, mul_one, antidiagonal3_mul_antidiagonal3]

section Vanishing

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {a₁ a₂ : ℕ}

private theorem cellSectionOf_conductorDatum_mul_lowerUnipotent10_eq (h₂ : 2 ≤ a₂) (h₁ : 1 ≤ a₁) (y : LocalGL3 v)
    {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp (1 : ℤ)) :
    cellSectionOf v ν (conductorDatum v ν a₁ a₂) (y * lowerUnipotent10 v x) =
      charExt (ν 2) (1 + cellRatio v y 0 * x) * cellSectionOf v ν (conductorDatum v ν a₁ a₂) y := by
  by_cases hy : y ∈ cellSupport v ν a₁ a₂
  · exact (cellSectionOf_conductorDatum_mul_lowerUnipotent10 v ν h₂ h₁ hy hx).2
  · have hy' : y * lowerUnipotent10 v x ∉ cellSupport v ν a₁ a₂ := by
      intro hmem
      have hx' : Valued.v (-x) ≤ WithZero.exp (1 : ℤ) := by rwa [Valuation.map_neg]
      have hback := (cellSectionOf_conductorDatum_mul_lowerUnipotent10 v ν h₂ h₁ hmem hx').1
      rw [mul_assoc, lowerUnipotent10_mul_lowerUnipotent10, add_neg_cancel, lowerUnipotent10_zero, mul_one] at hback
      exact hy hback
    rw [cellSectionOf_conductorDatum_eq_zero_of_notMem v ν a₁ a₂ hy',
      cellSectionOf_conductorDatum_eq_zero_of_notMem v ν a₁ a₂ hy, mul_zero]

private theorem cellSectionOf_conductorDatum_mul_lowerUnipotent10_of_integral (h₂ : 2 ≤ a₂) (h₁ : 1 ≤ a₁)
    (hν₂ : HasConductorExponentAt ℚ v (ν 2) a₂) (y : LocalGL3 v) {u : v.adicCompletion ℚ} (hu : Valued.v u ≤ 1) :
    cellSectionOf v ν (conductorDatum v ν a₁ a₂) (y * lowerUnipotent10 v u) =
      cellSectionOf v ν (conductorDatum v ν a₁ a₂) y := by
  have hu' : Valued.v u ≤ WithZero.exp (1 : ℤ) :=
    le_trans hu (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  rw [cellSectionOf_conductorDatum_mul_lowerUnipotent10_eq v ν h₂ h₁ y hu']
  by_cases hy : y ∈ cellSupport v ν a₁ a₂
  · obtain ⟨-, -, -, hr0⟩ := conductorDatum_support v ν a₁ a₂ hy.2
    have hw : Valued.v (cellRatio v y 0 * u) ≤ WithZero.exp (-(a₂ : ℤ)) := by
      rw [map_mul, hr0]; exact mul_le_of_le_one_right' hu
    rw [charExt_one_add_of_valued_le v (ν 2) hν₂ (by omega) hw, one_mul]
  · rw [cellSectionOf_conductorDatum_eq_zero_of_notMem v ν a₁ a₂ hy, mul_zero]

private theorem charExt_one_add_mul_add_of_valued_le (hν₂ : HasConductorExponentAt ℚ v (ν 2) a₂) (h₂ : 2 ≤ a₂)
    {r : v.adicCompletion ℚ} (hr : Valued.v r = WithZero.exp (-(a₂ : ℤ))) {x : v.adicCompletion ℚ}
    (hx : Valued.v x ≤ WithZero.exp (1 : ℤ)) {u : v.adicCompletion ℚ} (hu : Valued.v u ≤ 1) :
    charExt (ν 2) (1 + r * (x + u)) = charExt (ν 2) (1 + r * x) := by
  have hrx : Valued.v (r * x) ≤ WithZero.exp (-((a₂ - 1 : ℕ) : ℤ)) := by
    rw [map_mul, hr]
    calc WithZero.exp (-(a₂ : ℤ)) * Valued.v x ≤ WithZero.exp (-(a₂ : ℤ)) * WithZero.exp (1 : ℤ) :=
          mul_le_mul' le_rfl hx
      _ = _ := by rw [← WithZero.exp_add]; congr 1; push_cast [Nat.cast_sub (by omega : 1 ≤ a₂)]; ring
  have h1 : Valued.v (1 + r * x) = 1 := valued_one_add_eq_one v (by omega) hrx
  have h1' : (1 + r * x) ≠ 0 := ne_zero_of_valued_eq_one v h1
  have hsplit : 1 + r * (x + u) = (1 + r * x) * (1 + (1 + r * x)⁻¹ * (r * u)) := by
    field_simp
    ring
  have hw : Valued.v ((1 + r * x)⁻¹ * (r * u)) ≤ WithZero.exp (-(a₂ : ℤ)) := by
    rw [map_mul, map_inv₀, h1, inv_one, one_mul, map_mul, hr]
    exact mul_le_of_le_one_right' hu
  have hunit : (1 + (1 + r * x)⁻¹ * (r * u)) ≠ 0 :=
    ne_zero_of_valued_eq_one v (valued_one_add_eq_one v (by omega) hw)
  rw [hsplit, charExt_mul_of_ne_zero v _ h1' hunit, charExt_one_add_of_valued_le v (ν 2) hν₂ (by omega) hw, mul_one]

private theorem jacquetWhittaker3_conductorDatum_mul_upperUnipotent3_mul_antidiagonal3 (g : LocalGL3 v)
    (x : v.adicCompletion ℚ) :
    jacquetWhittaker3 v ν (conductorDatum v ν a₁ a₂) (g * upperUnipotent3 0 x 0 * antidiagonal3 v) =
      jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (g * antidiagonal3 v * lowerUnipotent10 v x)
        (cellSectionOf v ν (conductorDatum v ν a₁ a₂))) := by
  rw [mul_upperUnipotent3_mul_antidiagonal3, jacquetWhittaker3_apply]

private theorem jacquetWhittaker3_conductorDatum_mul_upperUnipotent3_add (h₂ : 2 ≤ a₂) (h₁ : 1 ≤ a₁)
    (hν₂ : HasConductorExponentAt ℚ v (ν 2) a₂) (g : LocalGL3 v) (x : v.adicCompletion ℚ) {u : v.adicCompletion ℚ}
    (hu : Valued.v u ≤ 1) :
    jacquetWhittaker3 v ν (conductorDatum v ν a₁ a₂) (g * upperUnipotent3 0 (x + u) 0 * antidiagonal3 v) =
      jacquetWhittaker3 v ν (conductorDatum v ν a₁ a₂) (g * upperUnipotent3 0 x 0 * antidiagonal3 v) := by
  rw [jacquetWhittaker3_conductorDatum_mul_upperUnipotent3_mul_antidiagonal3,
    jacquetWhittaker3_conductorDatum_mul_upperUnipotent3_mul_antidiagonal3]
  have hfun : (gl3AmbientRightTranslate (R := ℂ) (g * antidiagonal3 v * lowerUnipotent10 v (x + u))
        (cellSectionOf v ν (conductorDatum v ν a₁ a₂)) : LocalGL3 v → ℂ) =
      gl3AmbientRightTranslate (R := ℂ) (g * antidiagonal3 v * lowerUnipotent10 v x)
        (cellSectionOf v ν (conductorDatum v ν a₁ a₂)) := by
    funext y
    show cellSectionOf v ν (conductorDatum v ν a₁ a₂) (y * (g * antidiagonal3 v * lowerUnipotent10 v (x + u))) =
      cellSectionOf v ν (conductorDatum v ν a₁ a₂) (y * (g * antidiagonal3 v * lowerUnipotent10 v x))
    rw [← lowerUnipotent10_mul_lowerUnipotent10, ← mul_assoc, ← mul_assoc,
      cellSectionOf_conductorDatum_mul_lowerUnipotent10_of_integral v ν h₂ h₁ hν₂ _ hu, mul_assoc]
  rw [hfun]

private theorem sum_translate_conductorDatum_eq_zero (h₂ : 2 ≤ a₂) (h₁ : 1 ≤ a₁)
    (hν₂ : HasConductorExponentAt ℚ v (ν 2) a₂)
    (hvol : (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) ≠ 0)
    (R : Finset (v.adicCompletion ℚ)) (hRball : ∀ x₀ ∈ R, Valued.v x₀ ≤ WithZero.exp (1 : ℤ))
    (hRint : ∀ f : v.adicCompletion ℚ → ℂ,
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) →
        ∀ u : v.adicCompletion ℚ, Valued.v u ≤ 1 → f (x + u) = f x) →
      (letI := localBorel ℚ v
        ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)}, f x ∂(selfDualHaarAt ℚ v)) =
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) *
          ∑ x₀ ∈ R, f x₀)
    (hball : ∀ r : v.adicCompletion ℚ, Valued.v r = WithZero.exp (-(a₂ : ℤ)) →
      (letI := localBorel ℚ v
        ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)}, charExt (ν 2) (1 + r * x)
          ∂(selfDualHaarAt ℚ v)) = 0)
    (h : LocalGL3 v) :
    (∑ x₀ ∈ R, gl3AmbientRightTranslate (R := ℂ) (h * lowerUnipotent10 v x₀)
      (cellSectionOf v ν (conductorDatum v ν a₁ a₂))) = 0 := by
  funext y
  rw [Finset.sum_apply, Pi.zero_apply]
  have hterm : ∀ x₀ ∈ R,
      gl3AmbientRightTranslate (R := ℂ) (h * lowerUnipotent10 v x₀) (cellSectionOf v ν (conductorDatum v ν a₁ a₂)) y =
        charExt (ν 2) (1 + cellRatio v (y * h) 0 * x₀) * cellSectionOf v ν (conductorDatum v ν a₁ a₂) (y * h) :=
    fun x₀ hx₀ => by
      show cellSectionOf v ν (conductorDatum v ν a₁ a₂) (y * (h * lowerUnipotent10 v x₀)) = _
      rw [← mul_assoc]
      exact cellSectionOf_conductorDatum_mul_lowerUnipotent10_eq v ν h₂ h₁ _ (hRball x₀ hx₀)
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  by_cases hz : y * h ∈ cellSupport v ν a₁ a₂
  · obtain ⟨_, hΦ⟩ := hz
    obtain ⟨-, -, -, hr0⟩ := conductorDatum_support v ν a₁ a₂ hΦ
    have hdecomp := hRint (fun x => charExt (ν 2) (1 + cellRatio v (y * h) 0 * x))
      (fun x hx u hu => charExt_one_add_mul_add_of_valued_le v ν hν₂ h₂ hr0 hx hu)
    rw [hball _ hr0] at hdecomp
    have hsum : (∑ x₀ ∈ R, charExt (ν 2) (1 + cellRatio v (y * h) 0 * x₀)) = 0 :=
      (mul_eq_zero.mp hdecomp.symm).resolve_left (by exact_mod_cast hvol)
    rw [hsum, zero_mul]
  · rw [cellSectionOf_conductorDatum_eq_zero_of_notMem v ν a₁ a₂ hz, mul_zero]

private theorem hasVanishingUnipotentIntegralAt_jacquetWhittaker3_conductorDatum (h₂ : 2 ≤ a₂) (h₁ : 1 ≤ a₁)
    (hν₂ : HasConductorExponentAt ℚ v (ν 2) a₂)
    (hst : ∀ h : LocalGL3 v,
      JacquetIntegrable v (gl3AmbientRightTranslate (R := ℂ) h (cellSectionOf v ν (conductorDatum v ν a₁ a₂))) ∧
        Stabilises v (gl3AmbientRightTranslate (R := ℂ) h (cellSectionOf v ν (conductorDatum v ν a₁ a₂))))
    (hvol : (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) ≠ 0)
    (hR : ∃ R : Finset (v.adicCompletion ℚ), (∀ x₀ ∈ R, Valued.v x₀ ≤ WithZero.exp (1 : ℤ)) ∧
      ∀ f : v.adicCompletion ℚ → ℂ,
        (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) →
          ∀ u : v.adicCompletion ℚ, Valued.v u ≤ 1 → f (x + u) = f x) →
        (letI := localBorel ℚ v
          ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)}, f x ∂(selfDualHaarAt ℚ v)) =
          (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) *
            ∑ x₀ ∈ R, f x₀)
    (hball : ∀ r : v.adicCompletion ℚ, Valued.v r = WithZero.exp (-(a₂ : ℤ)) →
      (letI := localBorel ℚ v
        ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)}, charExt (ν 2) (1 + r * x)
          ∂(selfDualHaarAt ℚ v)) = 0) :
    HasVanishingUnipotentIntegralAt v
      (fun h => jacquetWhittaker3 v ν (conductorDatum v ν a₁ a₂) (h * antidiagonal3 v)) := by
  intro g
  obtain ⟨R, hRball, hRint⟩ := hR
  letI := localBorel ℚ v
  have hdec : (∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)},
      jacquetWhittaker3 v ν (conductorDatum v ν a₁ a₂) (g * upperUnipotent3 0 x 0 * antidiagonal3 v)
        ∂(selfDualHaarAt ℚ v)) =
      (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) *
        ∑ x₀ ∈ R, jacquetWhittaker3 v ν (conductorDatum v ν a₁ a₂) (g * upperUnipotent3 0 x₀ 0 * antidiagonal3 v) :=
    hRint (fun x => jacquetWhittaker3 v ν (conductorDatum v ν a₁ a₂) (g * upperUnipotent3 0 x 0 * antidiagonal3 v))
      (fun x _ u hu => jacquetWhittaker3_conductorDatum_mul_upperUnipotent3_add v ν h₂ h₁ hν₂ g x hu)
  refine hdec.trans ?_
  simp_rw [jacquetWhittaker3_conductorDatum_mul_upperUnipotent3_mul_antidiagonal3]
  rw [← jacquetValue_sum v R (fun x₀ => gl3AmbientRightTranslate (R := ℂ) (g * antidiagonal3 v * lowerUnipotent10 v x₀)
    (cellSectionOf v ν (conductorDatum v ν a₁ a₂))) (fun x₀ _ => (hst _).1) (fun x₀ _ => (hst _).2),
    sum_translate_conductorDatum_eq_zero v ν h₂ h₁ hν₂ hvol R hRball hRint hball, jacquetValue_zero, mul_zero]

end Vanishing

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ)) (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {a₁ a₂ : ℕ}

private theorem hasVanishingUnipotentIntegralAt_conductorDatum_of_stabilises (h₂ : 2 ≤ a₂) (h₁ : 1 ≤ a₁)
    (hν₂ : HasConductorExponentAt ℚ v (ν 2) a₂)
    (hst : ∀ h : LocalGL3 v,
      JacquetIntegrable v (gl3AmbientRightTranslate (R := ℂ) h (cellSectionOf v ν (conductorDatum v ν a₁ a₂))) ∧
        Stabilises v (gl3AmbientRightTranslate (R := ℂ) h (cellSectionOf v ν (conductorDatum v ν a₁ a₂)))) :
    HasVanishingUnipotentIntegralAt v
      (fun h => jacquetWhittaker3 v ν (conductorDatum v ν a₁ a₂) (h * antidiagonal3 v)) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI : (selfDualHaarAt ℚ v).Regular := regular_selfDualHaarAt ℚ v
  refine hasVanishingUnipotentIntegralAt_jacquetWhittaker3_conductorDatum v ν h₂ h₁ hν₂ hst ?_ ?_ ?_
  · exact (measureReal_integers_pos (K := ℚ) (v := v) (μ := selfDualHaarAt ℚ v)).ne'
  · exact exists_finset_setIntegral_setOf_valued_le_exp_one_eq (K := ℚ) (v := v) (μ := selfDualHaarAt ℚ v)
  · intro r hr
    have hr' : Valued.v r * WithZero.exp (1 : ℤ) = WithZero.exp (-((a₂ - 1 : ℕ) : ℤ)) := by
      rw [hr, ← WithZero.exp_add]
      congr 1
      push_cast [Nat.cast_sub (by omega : 1 ≤ a₂)]
      ring
    have h := setIntegral_charExt_one_add_mul_eq_zero (K := ℚ) (v := v) (μ := selfDualHaarAt ℚ v) hν₂
      (m := a₂ - 1) (by omega) (by omega) hr'
    simpa only [mul_comm] using h

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section EigenScaling

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem transposeInv3_mul (g h : LocalGL3 v) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change (((g * h)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ =
    ((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ *
      ((h⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem transposeInv3_transposeInv3 (g : LocalGL3 v) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  change (((g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ)ᵀ = _
  rw [Matrix.transpose_transpose]

private theorem transposeInv3_one : transposeInv3 (1 : LocalGL3 v) = 1 := by
  refine Units.ext ?_
  change (((1 : LocalGL3 v)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ = 1
  rw [inv_one, Units.val_one, Matrix.transpose_one]

private theorem dualWhittakerFn3_mul_transposeInv3 {R : Type*} (W : LocalGL3 v → R) (y k : LocalGL3 v) :
    dualWhittakerFn3 W (y * transposeInv3 k) = dualWhittakerFn3 (fun g => W (g * k)) y := by
  simp only [dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_transposeInv3, mul_assoc]

private theorem dualWhittakerFn3_mul_weylPrime3_mul_transposeInv3 (W : LocalGL3 v → ℂ) {k : LocalGL3 v} {c : ℂ}
    (hW : ∀ g, W (g * k) = c * W g) (y : LocalGL3 v) :
    dualWhittakerFn3 W (y * (weylPrime3 * transposeInv3 k)) = c * dualWhittakerFn3 W (y * weylPrime3) := by
  rw [← mul_assoc, dualWhittakerFn3_mul_transposeInv3]
  simp only [dualWhittakerFn3_apply]
  exact hW _

variable {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ} {mA : MeasurableSpace (v.adicCompletion ℚ)}

private theorem localZeta30_eq_mul_of_rightTranslate (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) {k : LocalGL3 v} {c : ℂ} (hW : ∀ g, W (g * k) = c * W g) :
    localZeta30 v μ W χ s k = c * localZeta30 v μ W χ s 1 := by
  unfold localZeta30
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  simp only [mul_one, hW]
  ring

private theorem isLocalZeta30ConvergentAbove_of_rightTranslate (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {k : LocalGL3 v} {c : ℂ} (hW : ∀ g, W (g * k) = c * W g) {σ₀ : ℝ}
    (h1 : IsLocalZeta30ConvergentAbove v μ W χ 1 σ₀) : IsLocalZeta30ConvergentAbove v μ W χ k σ₀ := by
  intro s hs
  refine ((h1 s hs).const_mul c).congr (ae_of_all _ fun a => ?_)
  simp only [mul_one, hW]
  ring

private theorem localZetaDual31_eq_mul_of_rightTranslate (μ : Measure (v.adicCompletion ℚ)ˣ)
    (ν' : Measure (v.adicCompletion ℚ)) (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)
    {k : LocalGL3 v} {c : ℂ} (hW : ∀ g, W (g * k) = c * W g) :
    localZetaDual31 v μ ν' W χ s k = c * localZetaDual31 v μ ν' W χ s 1 := by
  unfold localZetaDual31 localZeta31
  rw [transposeInv3_one, mul_one, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  simp only [dualWhittakerFn3_mul_weylPrime3_mul_transposeInv3 v W hW, integral_const_mul]
  ring

private theorem isLocalZeta31ConvergentAbove_dual_of_rightTranslate (μ : Measure (v.adicCompletion ℚ)ˣ)
    (ν' : Measure (v.adicCompletion ℚ)) (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    {k : LocalGL3 v} {c : ℂ} (hW : ∀ g, W (g * k) = c * W g) {σ₁ : ℝ}
    (h1 : IsLocalZeta31ConvergentAbove v μ ν' (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 1) σ₁) :
    IsLocalZeta31ConvergentAbove v μ ν' (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 k) σ₁ := by
  intro s hs
  have h := (h1 s hs).const_mul c
  rw [transposeInv3_one, mul_one] at h
  refine h.congr (ae_of_all _ fun p => ?_)
  simp only [dualWhittakerFn3_mul_weylPrime3_mul_transposeInv3 v W hW]
  ring

end EigenScaling

section ScalarScaling

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ} {mA : MeasurableSpace (v.adicCompletion ℚ)}

private theorem dualWhittakerFn3_const_mul (c : ℂ) (W : LocalGL3 v → ℂ) :
    dualWhittakerFn3 (fun x => c * W x) = fun x => c * dualWhittakerFn3 W x := by
  funext x
  simp only [dualWhittakerFn3_apply]

private theorem localZeta30_const_mul (μ : Measure (v.adicCompletion ℚ)ˣ) (c : ℂ) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    localZeta30 v μ (fun x => c * W x) χ s g = c * localZeta30 v μ W χ s g := by
  unfold localZeta30
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  dsimp only
  ring

private theorem isLocalZeta30ConvergentAbove_const_mul (μ : Measure (v.adicCompletion ℚ)ˣ) (c : ℂ) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {g : LocalGL3 v} {σ₀ : ℝ} (h : IsLocalZeta30ConvergentAbove v μ W χ g σ₀) :
    IsLocalZeta30ConvergentAbove v μ (fun x => c * W x) χ g σ₀ := by
  intro s hs
  refine ((h s hs).const_mul c).congr (ae_of_all _ fun a => ?_)
  dsimp only
  ring

private theorem localZetaDual31_const_mul (μ : Measure (v.adicCompletion ℚ)ˣ) (ν' : Measure (v.adicCompletion ℚ)) (c : ℂ)
    (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    localZetaDual31 v μ ν' (fun x => c * W x) χ s g = c * localZetaDual31 v μ ν' W χ s g := by
  unfold localZetaDual31 localZeta31
  rw [dualWhittakerFn3_const_mul, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  dsimp only
  rw [integral_const_mul]
  ring

private theorem isLocalZeta31ConvergentAbove_const_mul (μ : Measure (v.adicCompletion ℚ)ˣ) (ν' : Measure (v.adicCompletion ℚ))
    (c : ℂ) (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {g : LocalGL3 v} {σ₁ : ℝ}
    (h : IsLocalZeta31ConvergentAbove v μ ν' W χ g σ₁) :
    IsLocalZeta31ConvergentAbove v μ ν' (fun x => c * W x) χ g σ₁ := by
  intro s hs
  refine ((h s hs).const_mul c).congr (ae_of_all _ fun p => ?_)
  dsimp only
  ring

end ScalarScaling

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

open IsDedekindDomain NumberField Filter Topology

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section OpenSubgroupPackaging

private def principalCongruenceSet3 (N : ℕ) : Set (LocalGL3 v) :=
  {k | ∀ i j : Fin 3, Valued.v (gl3Entry v k i j - gl3Entry v 1 i j) ≤ WithZero.exp (-(N : ℤ))}

private theorem mem_principalCongruenceSet3 (N : ℕ) (k : LocalGL3 v) :
    k ∈ principalCongruenceSet3 v N ↔
      ∀ i j : Fin 3, Valued.v (gl3Entry v k i j - gl3Entry v 1 i j) ≤ WithZero.exp (-(N : ℤ)) :=
  Iff.rfl

private theorem gl3Entry_one (i j : Fin 3) : gl3Entry v (1 : LocalGL3 v) i j = if i = j then 1 else 0 := by
  simp only [gl3Entry, Units.val_one, Matrix.one_apply]

private theorem one_mem_principalCongruenceSet3 (N : ℕ) : (1 : LocalGL3 v) ∈ principalCongruenceSet3 v N := by
  intro i j
  simp

private theorem isOpen_principalCongruenceSet3 (N : ℕ) : IsOpen (principalCongruenceSet3 v N) := by
  have hset : principalCongruenceSet3 v N = ⋂ i : Fin 3, ⋂ j : Fin 3,
      (fun k : LocalGL3 v => gl3Entry v k i j) ⁻¹'
        {t : v.adicCompletion ℚ | Valued.v (t - gl3Entry v 1 i j) ≤ WithZero.exp (-(N : ℤ))} := by
    ext k
    simp only [principalCongruenceSet3, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isClopen_setOf_valued_sub_le v (gl3Entry v 1 i j) N).isOpen.preimage (continuous_gl3Entry v i j)

private theorem principalCongruenceSet3_mem_nhds_one (N : ℕ) : principalCongruenceSet3 v N ∈ 𝓝 (1 : LocalGL3 v) :=
  (isOpen_principalCongruenceSet3 v N).mem_nhds (one_mem_principalCongruenceSet3 v N)

private def rightStabilizer (W : LocalGL3 v → ℂ) : Subgroup (LocalGL3 v) where
  carrier := {k | ∀ g : LocalGL3 v, W (g * k) = W g}
  one_mem' := by
    intro g
    rw [mul_one]
  mul_mem' := by
    intro a b ha hb g
    rw [← mul_assoc, hb, ha]
  inv_mem' := by
    intro a ha g
    have h := ha (g * a⁻¹)
    rw [inv_mul_cancel_right] at h
    exact h.symm

private theorem mem_rightStabilizer (W : LocalGL3 v → ℂ) (k : LocalGL3 v) :
    k ∈ rightStabilizer v W ↔ ∀ g : LocalGL3 v, W (g * k) = W g :=
  Iff.rfl

private theorem exists_isOpen_subgroup_of_principalCongruenceSet3 (W : LocalGL3 v → ℂ) (N : ℕ)
    (h : ∀ k ∈ principalCongruenceSet3 v N, ∀ g : LocalGL3 v, W (g * k) = W g) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g := by
  refine ⟨rightStabilizer v W, ?_, fun k hk g => (mem_rightStabilizer v W k).mp hk g⟩
  refine Subgroup.isOpen_of_mem_nhds _ (mem_of_superset (principalCongruenceSet3_mem_nhds_one v N) ?_)
  intro k hk
  exact (mem_rightStabilizer v W k).mpr (h k hk)

end OpenSubgroupPackaging

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section GaugeFlip

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_mul_antidiagonal3_apply_zero (k : LocalGL3 v) (i : Fin 3) :
    ((k * antidiagonal3 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 0 =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 2 := by
  simp [Units.val_mul, antidiagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem coe_mul_antidiagonal3_apply_one (k : LocalGL3 v) (i : Fin 3) :
    ((k * antidiagonal3 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 1 =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 1 := by
  simp [Units.val_mul, antidiagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem coe_mul_antidiagonal3_apply_two (k : LocalGL3 v) (i : Fin 3) :
    ((k * antidiagonal3 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 2 =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 0 := by
  simp [Units.val_mul, antidiagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem lastRowSup_mul_antidiagonal3 (k : LocalGL3 v) : lastRowSup (k * antidiagonal3 v) = lastRowSup k := by
  simp only [lastRowSup, coe_mul_antidiagonal3_apply_zero, coe_mul_antidiagonal3_apply_one,
    coe_mul_antidiagonal3_apply_two]
  ac_rfl

private theorem bottomMinor_mul_antidiagonal3_zero_one (k : LocalGL3 v) :
    bottomMinor (k * antidiagonal3 v) 0 1 = -bottomMinor k 1 2 := by
  simp only [bottomMinor, coe_mul_antidiagonal3_apply_zero, coe_mul_antidiagonal3_apply_one]
  ring

private theorem bottomMinor_mul_antidiagonal3_zero_two (k : LocalGL3 v) :
    bottomMinor (k * antidiagonal3 v) 0 2 = -bottomMinor k 0 2 := by
  simp only [bottomMinor, coe_mul_antidiagonal3_apply_zero, coe_mul_antidiagonal3_apply_two]
  ring

private theorem bottomMinor_mul_antidiagonal3_one_two (k : LocalGL3 v) :
    bottomMinor (k * antidiagonal3 v) 1 2 = -bottomMinor k 0 1 := by
  simp only [bottomMinor, coe_mul_antidiagonal3_apply_one, coe_mul_antidiagonal3_apply_two]
  ring

private theorem minorSup_mul_antidiagonal3 (k : LocalGL3 v) : minorSup (k * antidiagonal3 v) = minorSup k := by
  simp only [minorSup, bottomMinor_mul_antidiagonal3_zero_one, bottomMinor_mul_antidiagonal3_zero_two,
    bottomMinor_mul_antidiagonal3_one_two, norm_neg]
  ac_rfl

private theorem detSize_mul_antidiagonal3 (k : LocalGL3 v) : detSize (k * antidiagonal3 v) = detSize k := by
  rw [detSize, detSize, Units.val_mul, Matrix.det_mul, norm_mul, antidiagonal3_coe]
  simp [Matrix.det_fin_three]

end GaugeFlip

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section UniformConstants

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isOpen_box3 (c : Fin 3 → v.adicCompletion ℚ) (k : ℤ) :
    IsOpen {r : Fin 3 → v.adicCompletion ℚ | ∀ i, Valued.v (r i - c i) ≤ WithZero.exp (-k)} := by
  have hset : {r : Fin 3 → v.adicCompletion ℚ | ∀ i, Valued.v (r i - c i) ≤ WithZero.exp (-k)}
      = ⋂ i, (fun r : Fin 3 → v.adicCompletion ℚ => r i) ⁻¹'
          {y : v.adicCompletion ℚ | Valued.v (y - c i) ≤ WithZero.exp (-k)} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  exact isOpen_iInter_of_finite fun i =>
    (isClopen_setOf_valued_sub_le v (c i) k).isOpen.preimage (continuous_apply i)

variable {v}

private theorem exists_box_of_hasCompactSupport (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦc : HasCompactSupport Φ) :
    ∃ R : ℕ, ∀ r : Fin 3 → v.adicCompletion ℚ, Φ r ≠ 0 → ∀ i, Valued.v (r i) ≤ WithZero.exp (R : ℤ) := by

  set V : ℕ → Set (Fin 3 → v.adicCompletion ℚ) := fun n =>
    {r | ∀ i, Valued.v (r i - (0 : Fin 3 → v.adicCompletion ℚ) i) ≤ WithZero.exp (-(-(n : ℤ)))} with hV
  have hVopen : ∀ n, IsOpen (V n) := fun n => isOpen_box3 v 0 (-(n : ℤ))
  have hVmem : ∀ (n : ℕ) (r : Fin 3 → v.adicCompletion ℚ),
      r ∈ V n ↔ ∀ i, Valued.v (r i) ≤ WithZero.exp (n : ℤ) := by
    intro n r
    simp only [hV, Set.mem_setOf_eq, Pi.zero_apply, sub_zero, neg_neg]
  have hcover : tsupport Φ ⊆ ⋃ n, V n := by
    intro r _
    choose n hn using fun i => exists_valued_le_exp v (r i)
    refine Set.mem_iUnion.mpr ⟨Finset.univ.sup n, (hVmem _ r).mpr fun i => (hn i).trans ?_⟩
    exact WithZero.exp_le_exp.mpr (Int.ofNat_le.mpr (Finset.le_sup (f := n) (Finset.mem_univ i)))
  obtain ⟨t, ht⟩ := hΦc.elim_finite_subcover V hVopen hcover
  refine ⟨t.sup id, fun r hr i => ?_⟩
  have hrt : r ∈ ⋃ n ∈ t, V n := ht (subset_tsupport Φ hr)
  obtain ⟨n, hn, hrn⟩ := Set.mem_iUnion₂.mp hrt
  refine ((hVmem n r).mp hrn i).trans (WithZero.exp_le_exp.mpr (Int.ofNat_le.mpr ?_))
  exact Finset.le_sup (f := id) hn

private theorem exists_level_forall_eq_of_isLocallyConstant {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ}
    (hΦ : IsLocallyConstant Φ) (x : Fin 3 → v.adicCompletion ℚ) :
    ∃ m : ℕ, ∀ r' : Fin 3 → v.adicCompletion ℚ,
      (∀ i, Valued.v (r' i - x i) ≤ WithZero.exp (-(m : ℤ))) → Φ r' = Φ x := by
  have hO : {y : Fin 3 → v.adicCompletion ℚ | Φ y = Φ x} ∈ nhds x := (hΦ.isOpen_fiber (Φ x)).mem_nhds rfl
  rw [nhds_pi, Filter.mem_pi] at hO
  obtain ⟨I, -, s, hs, hIs⟩ := hO
  have hball : ∀ i, ∃ j : ℤ, ∀ y : v.adicCompletion ℚ, Valued.v (y - x i) ≤ WithZero.exp (-j) → y ∈ s i := by
    intro i
    obtain ⟨U, hUs, hUo, hxU⟩ := mem_nhds_iff.mp (hs i)
    obtain ⟨j, hj⟩ := exists_setOf_valued_sub_le_subset_of_isOpen v hUo hxU
    exact ⟨j, fun y hy => hUs (hj hy)⟩
  choose j hj using hball
  refine ⟨Finset.univ.sup fun i => (j i).toNat, fun r' hr' => ?_⟩
  refine hIs (Set.mem_pi.mpr fun i _ => hj i (r' i) ((hr' i).trans (WithZero.exp_le_exp.mpr ?_)))
  have h1 : j i ≤ ((j i).toNat : ℤ) := Int.self_le_toNat (j i)
  have h2 : ((j i).toNat : ℤ) ≤ ((Finset.univ.sup fun i => (j i).toNat : ℕ) : ℤ) :=
    Int.ofNat_le.mpr (Finset.le_sup (f := fun i => (j i).toNat) (Finset.mem_univ i))
  omega

private theorem exists_uniform_level_of_isLocallyConstant (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ e : ℕ, ∀ r r' : Fin 3 → v.adicCompletion ℚ,
      (∀ i, Valued.v (r' i - r i) ≤ WithZero.exp (-(e : ℤ))) → Φ r' = Φ r := by
  choose m hm using fun x : Fin 3 → v.adicCompletion ℚ => exists_level_forall_eq_of_isLocallyConstant hΦ x
  set U : (Fin 3 → v.adicCompletion ℚ) → Set (Fin 3 → v.adicCompletion ℚ) := fun x =>
    {r | ∀ i, Valued.v (r i - x i) ≤ WithZero.exp (-(m x : ℤ))} with hU
  have hUnhds : ∀ x ∈ tsupport Φ, U x ∈ nhds x := fun x _ =>
    (isOpen_box3 v x (m x)).mem_nhds fun i => by simp
  obtain ⟨t, -, ht⟩ := hΦc.elim_nhds_subcover U hUnhds
  refine ⟨t.sup m, ?_⟩

  have key : ∀ r ∈ tsupport Φ, ∀ r' : Fin 3 → v.adicCompletion ℚ,
      (∀ i, Valued.v (r' i - r i) ≤ WithZero.exp (-((t.sup m : ℕ) : ℤ))) → Φ r' = Φ r := by
    intro r hr r' hrr'
    obtain ⟨x, hxt, hrx⟩ := Set.mem_iUnion₂.mp (ht hr)
    have hle : WithZero.exp (-((t.sup m : ℕ) : ℤ)) ≤ WithZero.exp (-(m x : ℤ)) :=
      WithZero.exp_le_exp.mpr (neg_le_neg (Int.ofNat_le.mpr (Finset.le_sup (f := m) hxt)))
    have hr'x : ∀ i, Valued.v (r' i - x i) ≤ WithZero.exp (-(m x : ℤ)) := by
      intro i
      calc Valued.v (r' i - x i) = Valued.v ((r' i - r i) + (r i - x i)) := by rw [sub_add_sub_cancel]
        _ ≤ max (Valued.v (r' i - r i)) (Valued.v (r i - x i)) := Valuation.map_add _ _ _
        _ ≤ WithZero.exp (-(m x : ℤ)) := max_le ((hrr' i).trans hle) (hrx i)
    rw [hm x r' hr'x, hm x r hrx]
  intro r r' hrr'
  by_cases hr : r ∈ tsupport Φ
  · exact key r hr r' hrr'
  by_cases hr' : r' ∈ tsupport Φ
  · refine (key r' hr' r fun i => ?_).symm
    rw [← Valuation.map_neg, neg_sub]
    exact hrr' i
  rw [image_eq_zero_of_notMem_tsupport hr, image_eq_zero_of_notMem_tsupport hr']

end UniformConstants

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section LevelAlgebra

private theorem valued_le_exp_of_le {x : v.adicCompletion ℚ} {m n : ℤ} (hx : Valued.v x ≤ WithZero.exp m) (h : m ≤ n) :
    Valued.v x ≤ WithZero.exp n :=
  hx.trans (by rw [WithZero.exp_le_exp]; exact h)

private theorem valued_mul_le_exp_add {x y : v.adicCompletion ℚ} {m n : ℤ} (hx : Valued.v x ≤ WithZero.exp m)
    (hy : Valued.v y ≤ WithZero.exp n) : Valued.v (x * y) ≤ WithZero.exp (m + n) := by
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

private theorem valued_mul_le_exp_of_le_one_right {x y : v.adicCompletion ℚ} {m : ℤ} (hx : Valued.v x ≤ WithZero.exp m)
    (hy : Valued.v y ≤ 1) : Valued.v (x * y) ≤ WithZero.exp m := by
  rw [map_mul]
  simpa using mul_le_mul' hx hy

private theorem valued_mul_le_exp_of_le_one_left {x y : v.adicCompletion ℚ} {m : ℤ} (hx : Valued.v x ≤ 1)
    (hy : Valued.v y ≤ WithZero.exp m) : Valued.v (x * y) ≤ WithZero.exp m := by
  rw [map_mul]
  simpa using mul_le_mul' hx hy

private theorem valued_mul_le_one {x y : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) :
    Valued.v (x * y) ≤ 1 := by
  rw [map_mul]
  simpa using mul_le_mul' hx hy

private theorem valued_one_add_eq_one_of_le_exp {w : v.adicCompletion ℚ} {m : ℤ} (hm : m ≤ -1)
    (hw : Valued.v w ≤ WithZero.exp m) : Valued.v (1 + w) = 1 := by
  refine Valuation.map_one_add_of_lt _ (lt_of_le_of_lt hw ?_)
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem valued_eq_one_of_sub_one_le {x : v.adicCompletion ℚ} {m : ℤ} (hm : m ≤ -1)
    (hx : Valued.v (x - 1) ≤ WithZero.exp m) : Valued.v x = 1 := by
  have h : x = 1 + (x - 1) := by ring
  rw [h]
  exact valued_one_add_eq_one_of_le_exp v hm hx

private theorem ne_zero_of_valued_eq_one' {x : v.adicCompletion ℚ} (hx : Valued.v x = 1) : x ≠ 0 :=
  (Valuation.ne_zero_iff _).mp (by rw [hx]; exact one_ne_zero)

private theorem valued_gl3Entry_diag_sub_one_le {N : ℕ} {k : LocalGL3 v} (hk : k ∈ principalCongruenceSet3 v N) (i : Fin 3) :
    Valued.v (gl3Entry v k i i - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have h := (mem_principalCongruenceSet3 v N k).mp hk i i
  rwa [gl3Entry_one, if_pos rfl] at h

private theorem valued_gl3Entry_le_of_ne {N : ℕ} {k : LocalGL3 v} (hk : k ∈ principalCongruenceSet3 v N) {i j : Fin 3}
    (hij : i ≠ j) : Valued.v (gl3Entry v k i j) ≤ WithZero.exp (-(N : ℤ)) := by
  have h := (mem_principalCongruenceSet3 v N k).mp hk i j
  rwa [gl3Entry_one, if_neg hij, sub_zero] at h

private theorem valued_gl3Entry_one_le_one (i j : Fin 3) : Valued.v (gl3Entry v (1 : LocalGL3 v) i j) ≤ 1 := by
  rw [gl3Entry_one]
  split_ifs <;> simp

private theorem valued_gl3Entry_le_one_of_mem {N : ℕ} {k : LocalGL3 v} (hk : k ∈ principalCongruenceSet3 v N) (i j : Fin 3) :
    Valued.v (gl3Entry v k i j) ≤ 1 := by
  have h := (mem_principalCongruenceSet3 v N k).mp hk i j
  have hN : WithZero.exp (-(N : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have e : gl3Entry v k i j = (gl3Entry v k i j - gl3Entry v 1 i j) + gl3Entry v 1 i j := by ring
  rw [e]
  exact Valuation.map_add_le _ (h.trans hN) (valued_gl3Entry_one_le_one v i j)

variable (k : LocalGL3 v) (r : Fin 3 → v.adicCompletion ℚ)

private def cornerFactor : v.adicCompletion ℚ :=
  gl3Entry v k 0 0 + r 0 * gl3Entry v k 1 0 + r 1 * gl3Entry v k 2 0

private def entryFactor₁ : v.adicCompletion ℚ :=
  gl3Entry v k 0 1 + r 0 * gl3Entry v k 1 1 + r 1 * gl3Entry v k 2 1

private def entryFactor₂ : v.adicCompletion ℚ :=
  gl3Entry v k 0 2 + r 0 * gl3Entry v k 1 2 + r 1 * gl3Entry v k 2 2

private def lowerFactor : v.adicCompletion ℚ :=
  (gl3Entry v k 0 0 * gl3Entry v k 1 1 - gl3Entry v k 0 1 * gl3Entry v k 1 0) +
    r 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) +
      (r 0 * r 2 - r 1) * (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0)

private def outerFactor : v.adicCompletion ℚ :=
  (gl3Entry v k 0 0 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 0) +
    r 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 0) +
      (r 0 * r 2 - r 1) * (gl3Entry v k 1 0 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 0)

variable {k r}

section Estimates

variable {N R : ℕ} (hk : k ∈ principalCongruenceSet3 v N) (hr : ∀ i, Valued.v (r i) ≤ WithZero.exp (R : ℤ))
include hk hr

private theorem valued_cornerFactor_sub_one_le : Valued.v (cornerFactor v k r - 1) ≤ WithZero.exp ((R : ℤ) - N) := by
  have e : cornerFactor v k r - 1 =
      (gl3Entry v k 0 0 - 1) + r 0 * gl3Entry v k 1 0 + r 1 * gl3Entry v k 2 0 := by
    unfold cornerFactor
    ring
  rw [e]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
  · exact valued_le_exp_of_le v (valued_gl3Entry_diag_sub_one_le v hk 0) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 0) (valued_gl3Entry_le_of_ne v hk (by decide))) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 1) (valued_gl3Entry_le_of_ne v hk (by decide))) (by omega)

private theorem valued_entryFactor₁_sub_le : Valued.v (entryFactor₁ v k r - r 0) ≤ WithZero.exp ((R : ℤ) - N) := by
  have e : entryFactor₁ v k r - r 0 =
      gl3Entry v k 0 1 + r 0 * (gl3Entry v k 1 1 - 1) + r 1 * gl3Entry v k 2 1 := by
    unfold entryFactor₁
    ring
  rw [e]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
  · exact valued_le_exp_of_le v (valued_gl3Entry_le_of_ne v hk (by decide)) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 0) (valued_gl3Entry_diag_sub_one_le v hk 1)) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 1) (valued_gl3Entry_le_of_ne v hk (by decide))) (by omega)

private theorem valued_entryFactor₂_sub_le : Valued.v (entryFactor₂ v k r - r 1) ≤ WithZero.exp ((R : ℤ) - N) := by
  have e : entryFactor₂ v k r - r 1 =
      gl3Entry v k 0 2 + r 0 * gl3Entry v k 1 2 + r 1 * (gl3Entry v k 2 2 - 1) := by
    unfold entryFactor₂
    ring
  rw [e]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
  · exact valued_le_exp_of_le v (valued_gl3Entry_le_of_ne v hk (by decide)) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 0) (valued_gl3Entry_le_of_ne v hk (by decide))) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 1) (valued_gl3Entry_diag_sub_one_le v hk 2)) (by omega)

omit hk hr in

private theorem valued_minor_le_of_ne {a b c d : Fin 3} {a' b' c' d' : Fin 3}
    (h1 : Valued.v (gl3Entry v k a b * gl3Entry v k c d) ≤ WithZero.exp (-(N : ℤ)))
    (h2 : Valued.v (gl3Entry v k a' b' * gl3Entry v k c' d') ≤ WithZero.exp (-(N : ℤ))) :
    Valued.v (gl3Entry v k a b * gl3Entry v k c d - gl3Entry v k a' b' * gl3Entry v k c' d') ≤
      WithZero.exp (-(N : ℤ)) :=
  Valuation.map_sub_le _ h1 h2

omit hr in

private theorem valued_diag_minor_sub_one_le {i j : Fin 3} (hij : i ≠ j) :
    Valued.v (gl3Entry v k i i * gl3Entry v k j j - gl3Entry v k i j * gl3Entry v k j i - 1) ≤
      WithZero.exp (-(N : ℤ)) := by
  have e : gl3Entry v k i i * gl3Entry v k j j - gl3Entry v k i j * gl3Entry v k j i - 1 =
      (gl3Entry v k i i - 1) * gl3Entry v k j j + (gl3Entry v k j j - 1) - gl3Entry v k i j * gl3Entry v k j i := by
    ring
  rw [e]
  have h1 := valued_gl3Entry_le_one_of_mem v hk
  refine Valuation.map_sub_le _ (Valuation.map_add_le _ ?_ ?_) ?_
  · exact valued_mul_le_exp_of_le_one_right v (valued_gl3Entry_diag_sub_one_le v hk i) (h1 j j)
  · exact valued_gl3Entry_diag_sub_one_le v hk j
  · exact valued_mul_le_exp_of_le_one_right v (valued_gl3Entry_le_of_ne v hk hij) (h1 j i)

private theorem valued_ratio_coeff_le : Valued.v (r 0 * r 2 - r 1) ≤ WithZero.exp (2 * (R : ℤ)) := by
  have _hk := hk
  refine Valuation.map_sub_le _ ?_ ?_
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 0) (hr 2)) (by omega)
  · exact valued_le_exp_of_le v (hr 1) (by omega)

private theorem valued_lowerFactor_sub_one_le : Valued.v (lowerFactor v k r - 1) ≤ WithZero.exp (2 * (R : ℤ) - N) := by
  have e : lowerFactor v k r - 1 =
      (gl3Entry v k 0 0 * gl3Entry v k 1 1 - gl3Entry v k 0 1 * gl3Entry v k 1 0 - 1) +
        r 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) +
          (r 0 * r 2 - r 1) * (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0) := by
    unfold lowerFactor
    ring
  rw [e]
  have h1 := valued_gl3Entry_le_one_of_mem v hk
  have ho : ∀ {a b : Fin 3}, a ≠ b → Valued.v (gl3Entry v k a b) ≤ WithZero.exp (-(N : ℤ)) :=
    fun h => valued_gl3Entry_le_of_ne v hk h
  have hm1 := valued_diag_minor_sub_one_le v hk (by decide : (0 : Fin 3) ≠ 1)
  have hm2 : Valued.v (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) ≤
      WithZero.exp (-(N : ℤ)) :=
    valued_minor_le_of_ne v (valued_mul_le_exp_of_le_one_left v (h1 0 0) (ho (by decide)))
      (valued_mul_le_exp_of_le_one_right v (ho (by decide)) (h1 2 0))
  have hm3 : Valued.v (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0) ≤
      WithZero.exp (-(N : ℤ)) :=
    valued_minor_le_of_ne v (valued_mul_le_exp_of_le_one_right v (ho (by decide)) (h1 2 1))
      (valued_mul_le_exp_of_le_one_left v (h1 1 1) (ho (by decide)))
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
  · exact valued_le_exp_of_le v hm1 (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 2) hm2) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (valued_ratio_coeff_le v hk hr) hm3) (by omega)

private theorem valued_outerFactor_sub_le : Valued.v (outerFactor v k r - r 2) ≤ WithZero.exp (2 * (R : ℤ) - N) := by
  have e : outerFactor v k r - r 2 =
      (gl3Entry v k 0 0 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 0) +
        r 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 0 - 1) +
          (r 0 * r 2 - r 1) * (gl3Entry v k 1 0 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 0) := by
    unfold outerFactor
    ring
  rw [e]
  have h1 := valued_gl3Entry_le_one_of_mem v hk
  have ho : ∀ {a b : Fin 3}, a ≠ b → Valued.v (gl3Entry v k a b) ≤ WithZero.exp (-(N : ℤ)) :=
    fun h => valued_gl3Entry_le_of_ne v hk h
  have hm1 : Valued.v (gl3Entry v k 0 0 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 0) ≤
      WithZero.exp (-(N : ℤ)) :=
    valued_minor_le_of_ne v (valued_mul_le_exp_of_le_one_left v (h1 0 0) (ho (by decide)))
      (valued_mul_le_exp_of_le_one_right v (ho (by decide)) (h1 1 0))
  have hm2 := valued_diag_minor_sub_one_le v hk (by decide : (0 : Fin 3) ≠ 2)
  have hm3 : Valued.v (gl3Entry v k 1 0 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 0) ≤
      WithZero.exp (-(N : ℤ)) :=
    valued_minor_le_of_ne v (valued_mul_le_exp_of_le_one_right v (ho (by decide)) (h1 2 2))
      (valued_mul_le_exp_of_le_one_right v (ho (by decide)) (h1 2 0))
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
  · exact valued_le_exp_of_le v hm1 (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 2) hm2) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (valued_ratio_coeff_le v hk hr) hm3) (by omega)

variable (hN : 2 * R + 1 ≤ N)
include hN

private theorem valued_cornerFactor_eq_one : Valued.v (cornerFactor v k r) = 1 :=
  valued_eq_one_of_sub_one_le v (by omega) (valued_cornerFactor_sub_one_le v hk hr)

private theorem valued_lowerFactor_eq_one : Valued.v (lowerFactor v k r) = 1 :=
  valued_eq_one_of_sub_one_le v (by omega) (valued_lowerFactor_sub_one_le v hk hr)

private theorem cornerFactor_ne_zero : cornerFactor v k r ≠ 0 :=
  ne_zero_of_valued_eq_one' v (valued_cornerFactor_eq_one v hk hr hN)

private theorem lowerFactor_ne_zero : lowerFactor v k r ≠ 0 :=
  ne_zero_of_valued_eq_one' v (valued_lowerFactor_eq_one v hk hr hN)

private theorem valued_div_sub_le {a F ρ : v.adicCompletion ℚ} {t u : ℤ} (hF : Valued.v F = 1)
    (ha : Valued.v (a - ρ) ≤ WithZero.exp t) (hF1 : Valued.v (F - 1) ≤ WithZero.exp u)
    (hρ : Valued.v ρ ≤ WithZero.exp (R : ℤ)) (ht : t ≤ 3 * (R : ℤ) - N) (hu : (R : ℤ) + u ≤ 3 * (R : ℤ) - N) :
    Valued.v (a / F - ρ) ≤ WithZero.exp (3 * (R : ℤ) - N) := by
  have _hk := hk
  have _hr := hr
  have _hN := hN
  have hF0 : F ≠ 0 := ne_zero_of_valued_eq_one' v hF
  have e : a / F - ρ = ((a - ρ) - ρ * (F - 1)) / F := by
    rw [eq_div_iff hF0, sub_mul, div_mul_cancel₀ _ hF0]
    ring
  rw [e, map_div₀, hF, div_one]
  refine Valuation.map_sub_le _ (valued_le_exp_of_le v ha ht) ?_
  exact valued_le_exp_of_le v (valued_mul_le_exp_add v hρ hF1) hu

private theorem valued_entryFactor₁_div_cornerFactor_sub_le :
    Valued.v (entryFactor₁ v k r / cornerFactor v k r - r 0) ≤ WithZero.exp (3 * (R : ℤ) - N) :=
  valued_div_sub_le v hk hr hN (valued_cornerFactor_eq_one v hk hr hN) (valued_entryFactor₁_sub_le v hk hr)
    (valued_cornerFactor_sub_one_le v hk hr) (hr 0) (by omega) (by omega)

private theorem valued_entryFactor₂_div_cornerFactor_sub_le :
    Valued.v (entryFactor₂ v k r / cornerFactor v k r - r 1) ≤ WithZero.exp (3 * (R : ℤ) - N) :=
  valued_div_sub_le v hk hr hN (valued_cornerFactor_eq_one v hk hr hN) (valued_entryFactor₂_sub_le v hk hr)
    (valued_cornerFactor_sub_one_le v hk hr) (hr 1) (by omega) (by omega)

private theorem valued_outerFactor_div_lowerFactor_sub_le :
    Valued.v (outerFactor v k r / lowerFactor v k r - r 2) ≤ WithZero.exp (3 * (R : ℤ) - N) :=
  valued_div_sub_le v hk hr hN (valued_lowerFactor_eq_one v hk hr hN) (valued_outerFactor_sub_le v hk hr)
    (valued_lowerFactor_sub_one_le v hk hr) (hr 2) (by omega) (by omega)

end Estimates

private theorem valued_gl3Det_sub_one_le {N : ℕ} (hk : k ∈ principalCongruenceSet3 v N) :
    Valued.v (gl3Det v k - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have e' : ∀ i j, (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j = gl3Entry v k i j := fun _ _ => rfl
  have e : gl3Det v k - 1 =
      (gl3Entry v k 0 0 - 1) * gl3Entry v k 1 1 * gl3Entry v k 2 2 +
          (gl3Entry v k 1 1 - 1) * gl3Entry v k 2 2 + (gl3Entry v k 2 2 - 1) -
        gl3Entry v k 0 0 * gl3Entry v k 1 2 * gl3Entry v k 2 1 -
        gl3Entry v k 0 1 * gl3Entry v k 1 0 * gl3Entry v k 2 2 +
        gl3Entry v k 0 1 * gl3Entry v k 1 2 * gl3Entry v k 2 0 +
        gl3Entry v k 0 2 * gl3Entry v k 1 0 * gl3Entry v k 2 1 -
        gl3Entry v k 0 2 * gl3Entry v k 1 1 * gl3Entry v k 2 0 := by
    simp only [gl3Det, Matrix.det_fin_three, e']
    ring
  rw [e]
  have hd := valued_gl3Entry_diag_sub_one_le v hk
  have ho : ∀ {i j : Fin 3}, i ≠ j → Valued.v (gl3Entry v k i j) ≤ WithZero.exp (-(N : ℤ)) :=
    fun h => valued_gl3Entry_le_of_ne v hk h
  have h1 := valued_gl3Entry_le_one_of_mem v hk
  have hR := @valued_mul_le_exp_of_le_one_right v
  have hL := @valued_mul_le_exp_of_le_one_left v
  refine Valuation.map_sub_le _ ?_ ?_
  refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sub_le _ (Valuation.map_sub_le _
    (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · exact hR (hR (hd 0) (h1 1 1)) (h1 2 2)
  · exact hR (hd 1) (h1 2 2)
  · exact hd 2
  · exact hR (hL (h1 0 0) (ho (by decide))) (h1 2 1)
  · exact hR (hR (ho (by decide)) (h1 1 0)) (h1 2 2)
  · exact hR (hR (ho (by decide)) (h1 1 2)) (h1 2 0)
  · exact hR (hR (ho (by decide)) (h1 1 0)) (h1 2 1)
  · exact hR (hR (ho (by decide)) (h1 1 1)) (h1 2 0)

private theorem valued_gl3Det_eq_one_of_mem {N : ℕ} (hN : 1 ≤ N) (hk : k ∈ principalCongruenceSet3 v N) :
    Valued.v (gl3Det v k) = 1 :=
  valued_eq_one_of_sub_one_le v (by omega) (valued_gl3Det_sub_one_le v hk)

private theorem valued_det_le_one (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (hM : ∀ i j, Valued.v (M i j) ≤ 1) :
    Valued.v M.det ≤ 1 := by
  rw [Matrix.det_fin_three]
  have h3 : ∀ a b c d e f : Fin 3, Valued.v (M a b * M c d * M e f) ≤ 1 := fun a b c d e f =>
    valued_mul_le_one v (valued_mul_le_one v (hM a b) (hM c d)) (hM e f)
  exact Valuation.map_sub_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sub_le _
    (Valuation.map_sub_le _ (h3 0 0 1 1 2 2) (h3 0 0 1 2 2 1)) (h3 0 1 1 0 2 2)) (h3 0 1 1 2 2 0)) (h3 0 2 1 0 2 1))
    (h3 0 2 1 1 2 0)

private theorem valued_adjugate_le_one (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (hM : ∀ i j, Valued.v (M i j) ≤ 1)
    (i j : Fin 3) : Valued.v (M.adjugate i j) ≤ 1 := by
  rw [Matrix.adjugate_apply]
  refine valued_det_le_one v _ fun a b => ?_
  rw [Matrix.updateRow_apply]
  split_ifs with ha
  · rw [Pi.single_apply]
    split_ifs <;> simp
  · exact hM a b

private theorem gl3Entry_inv_eq (i j : Fin 3) :
    gl3Entry v k⁻¹ i j =
      (gl3Det v k)⁻¹ * (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).adjugate i j := by
  show ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j = _
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rfl

private theorem valued_gl3Entry_inv_le_one {N : ℕ} (hN : 1 ≤ N) (hk : k ∈ principalCongruenceSet3 v N) (i j : Fin 3) :
    Valued.v (gl3Entry v k⁻¹ i j) ≤ 1 := by
  rw [gl3Entry_inv_eq v, map_mul, map_inv₀, valued_gl3Det_eq_one_of_mem v hN hk, inv_one, one_mul]
  exact valued_adjugate_le_one v _ (fun a b => valued_gl3Entry_le_one_of_mem v hk a b) i j

private theorem gl3Entry_inv_sub_one (i j : Fin 3) :
    gl3Entry v k⁻¹ i j - gl3Entry v 1 i j =
      gl3Entry v k⁻¹ i 0 * (gl3Entry v 1 0 j - gl3Entry v k 0 j) +
        gl3Entry v k⁻¹ i 1 * (gl3Entry v 1 1 j - gl3Entry v k 1 j) +
          gl3Entry v k⁻¹ i 2 * (gl3Entry v 1 2 j - gl3Entry v k 2 j) := by
  have hmat : (k⁻¹ : LocalGL3 v).val * ((1 : LocalGL3 v).val - k.val) =
      (k⁻¹ : LocalGL3 v).val - (1 : LocalGL3 v).val := by
    rw [Matrix.mul_sub, Units.val_one, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h := congrFun (congrFun hmat i) j
  rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three] at h
  simp only [Matrix.sub_apply] at h
  exact h.symm

private theorem inv_mem_principalCongruenceSet3 {N : ℕ} (hN : 1 ≤ N) (hk : k ∈ principalCongruenceSet3 v N) :
    k⁻¹ ∈ principalCongruenceSet3 v N := by
  refine (mem_principalCongruenceSet3 v N _).mpr fun i j => ?_
  rw [gl3Entry_inv_sub_one]
  have hk' := (mem_principalCongruenceSet3 v N k).mp hk
  have hterm : ∀ l : Fin 3,
      Valued.v (gl3Entry v k⁻¹ i l * (gl3Entry v 1 l j - gl3Entry v k l j)) ≤ WithZero.exp (-(N : ℤ)) := by
    intro l
    refine valued_mul_le_exp_of_le_one_left v (valued_gl3Entry_inv_le_one v hN hk i l) ?_
    rw [Valuation.map_sub_swap]
    exact hk' l j
  exact Valuation.map_add_le _ (Valuation.map_add_le _ (hterm 0) (hterm 1)) (hterm 2)

private theorem antidiagonal3_mul_mul_antidiagonal3_mem {N : ℕ} (hk : k ∈ principalCongruenceSet3 v N) :
    antidiagonal3 v * k * antidiagonal3 v ∈ principalCongruenceSet3 v N := by
  refine (mem_principalCongruenceSet3 v N _).mpr fun i j => ?_
  rw [gl3Entry_antidiagonal3_mul_mul_antidiagonal3]
  have h := (mem_principalCongruenceSet3 v N k).mp hk (Fin.rev i) (Fin.rev j)
  have e : gl3Entry v 1 (Fin.rev i) (Fin.rev j) = gl3Entry v 1 i j := by
    rw [gl3Entry_one, gl3Entry_one]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h' => hij (Fin.rev_inj.mp h')), if_neg hij]
  rw [e] at h
  exact h

end LevelAlgebra

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section Smoothness

private theorem charExt_mul_eq_of_valued_sub_one_le (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c) {M u : v.adicCompletion ℚ} (hM : M ≠ 0)
    (hu : Valued.v (u - 1) ≤ WithZero.exp (-((c : ℤ) + 1))) : charExt ξ (M * u) = charExt ξ M := by
  have hu1 : Valued.v u = 1 := valued_eq_one_of_sub_one_le v (by omega) hu
  have hu0 : u ≠ 0 := ne_zero_of_valued_eq_one' v hu1
  rw [charExt_mul_of_ne_zero v ξ hM hu0]
  suffices h : charExt ξ u = 1 by rw [h, mul_one]
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    rw [charExt_of_ne_zero ξ hu0, (hasConductorExponentAt_zero_iff (K := ℚ) (v := v)).mp hξ (Units.mk0 u hu0) hu1,
      Units.val_one]
  · have hw : Valued.v (u - 1) ≤ WithZero.exp (-(c : ℤ)) := valued_le_exp_of_le v hu (by omega)
    have h := charExt_one_add_of_valued_le v ξ hξ (by omega) hw
    have e : (1 : v.adicCompletion ℚ) + (u - 1) = u := by ring
    rwa [e] at h

variable {v}

private theorem cornerEntry_mul_eq {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    cornerEntry v (g * k) = cornerEntry v g * cornerFactor v k (cellRatio v g) :=
  cornerEntry_mul_of_ne_zero v hc k

private theorem gl3Entry_two_one_mul_eq {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    gl3Entry v (g * k) 2 1 = cornerEntry v g * entryFactor₁ v k (cellRatio v g) :=
  gl3Entry_two_one_mul_of_ne_zero v hc k

private theorem gl3Entry_two_two_mul_eq {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    gl3Entry v (g * k) 2 2 = cornerEntry v g * entryFactor₂ v k (cellRatio v g) :=
  gl3Entry_two_two_mul_of_ne_zero v hc k

private theorem lowerMinor_mul_eq {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) (k : LocalGL3 v) :
    lowerMinor v (g * k) = lowerMinor v g * lowerFactor v k (cellRatio v g) :=
  lowerMinor_mul_of_ne_zero v hc hl k

private theorem outerMinor_mul_eq {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) (k : LocalGL3 v) :
    outerMinor v (g * k) = lowerMinor v g * outerFactor v k (cellRatio v g) :=
  outerMinor_mul_of_ne_zero v hc hl k

private theorem cellRatio_mul_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    cellRatio v (g * k) 0 = entryFactor₁ v k (cellRatio v g) / cornerFactor v k (cellRatio v g) := by
  rw [cellRatio_zero, gl3Entry_two_one_mul_eq hc k, cornerEntry_mul_eq hc k, mul_div_mul_left _ _ hc]

private theorem cellRatio_mul_one {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    cellRatio v (g * k) 1 = entryFactor₂ v k (cellRatio v g) / cornerFactor v k (cellRatio v g) := by
  rw [cellRatio_one, gl3Entry_two_two_mul_eq hc k, cornerEntry_mul_eq hc k, mul_div_mul_left _ _ hc]

private theorem cellRatio_mul_two {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) (k : LocalGL3 v) :
    cellRatio v (g * k) 2 = outerFactor v k (cellRatio v g) / lowerFactor v k (cellRatio v g) := by
  rw [cellRatio_two, outerMinor_mul_eq hc hl k, lowerMinor_mul_eq hc hl k, mul_div_mul_left _ _ hl]

variable (v)

private theorem cellSectionOf_mul_eq_of_mem (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (c : Fin 3 → ℕ)
    (hχ : ∀ i, HasConductorExponentAt ℚ v (χ i) (c i)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {R e N : ℕ}
    (he : ∀ r r' : Fin 3 → v.adicCompletion ℚ,
      (∀ i, Valued.v (r' i - r i) ≤ WithZero.exp (-(e : ℤ))) → Φ r' = Φ r)
    (hN : 2 * R + 1 ≤ N) (hNe : 3 * R + e ≤ N) (hNc : ∀ i, 2 * R + (c i + 1) ≤ N) {k : LocalGL3 v}
    (hk : k ∈ principalCongruenceSet3 v N) {g : LocalGL3 v} (hg : g ∈ bigCell3 v)
    (hr : ∀ i, Valued.v (cellRatio v g i) ≤ WithZero.exp (R : ℤ)) :
    cellSectionOf v χ Φ (g * k) = cellSectionOf v χ Φ g := by
  obtain ⟨hc, hl⟩ := (mem_bigCell3_iff v g).mp hg
  have hF0 : Valued.v (cornerFactor v k (cellRatio v g)) = 1 := valued_cornerFactor_eq_one v hk hr hN
  have hF1 : Valued.v (lowerFactor v k (cellRatio v g)) = 1 := valued_lowerFactor_eq_one v hk hr hN
  have hF0' : cornerFactor v k (cellRatio v g) ≠ 0 := cornerFactor_ne_zero v hk hr hN
  have hF1' : lowerFactor v k (cellRatio v g) ≠ 0 := lowerFactor_ne_zero v hk hr hN
  have hD : Valued.v (gl3Det v k) = 1 := valued_gl3Det_eq_one_of_mem v (by omega) hk
  have hgk : g * k ∈ bigCell3 v := by
    refine (mem_bigCell3_iff v _).mpr ⟨?_, ?_⟩
    · rw [cornerEntry_mul_eq hc k]
      exact mul_ne_zero hc hF0'
    · rw [lowerMinor_mul_eq hc hl k]
      exact mul_ne_zero hl hF1'
  have hΦ : Φ (cellRatio v (g * k)) = Φ (cellRatio v g) := by
    refine he _ _ fun i => ?_
    have h3 : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (3 * (R : ℤ) - N) →
        Valued.v t ≤ WithZero.exp (-(e : ℤ)) :=
      fun t ht => valued_le_exp_of_le v ht (by omega)
    fin_cases i
    · show Valued.v (cellRatio v (g * k) 0 - cellRatio v g 0) ≤ WithZero.exp (-(e : ℤ))
      rw [cellRatio_mul_zero hc k]
      exact h3 _ (valued_entryFactor₁_div_cornerFactor_sub_le v hk hr hN)
    · show Valued.v (cellRatio v (g * k) 1 - cellRatio v g 1) ≤ WithZero.exp (-(e : ℤ))
      rw [cellRatio_mul_one hc k]
      exact h3 _ (valued_entryFactor₂_div_cornerFactor_sub_le v hk hr hN)
    · show Valued.v (cellRatio v (g * k) 2 - cellRatio v g 2) ≤ WithZero.exp (-(e : ℤ))
      rw [cellRatio_mul_two hc hl k]
      exact h3 _ (valued_outerFactor_div_lowerFactor_sub_le v hk hr hN)
  have hval : cellValue v χ (g * k) = cellValue v χ g := by
    have hu₁ : Valued.v (gl3Det v k / lowerFactor v k (cellRatio v g) - 1) ≤ WithZero.exp (2 * (R : ℤ) - N) := by
      rw [div_sub_one hF1', map_div₀, hF1, div_one]
      have e : gl3Det v k - lowerFactor v k (cellRatio v g) =
          (gl3Det v k - 1) - (lowerFactor v k (cellRatio v g) - 1) := by ring
      rw [e]
      exact Valuation.map_sub_le _ (valued_le_exp_of_le v (valued_gl3Det_sub_one_le v hk) (by omega))
        (valued_lowerFactor_sub_one_le v hk hr)
    have hu₂ : Valued.v (lowerFactor v k (cellRatio v g) / cornerFactor v k (cellRatio v g) - 1) ≤
        WithZero.exp (2 * (R : ℤ) - N) := by
      rw [div_sub_one hF0', map_div₀, hF0, div_one]
      have e : lowerFactor v k (cellRatio v g) - cornerFactor v k (cellRatio v g) =
          (lowerFactor v k (cellRatio v g) - 1) - (cornerFactor v k (cellRatio v g) - 1) := by ring
      rw [e]
      exact Valuation.map_sub_le _ (valued_lowerFactor_sub_one_le v hk hr)
        (valued_le_exp_of_le v (valued_cornerFactor_sub_one_le v hk hr) (by omega))
    have hu₃ : Valued.v (cornerFactor v k (cellRatio v g) - 1) ≤ WithZero.exp (2 * (R : ℤ) - N) :=
      valued_le_exp_of_le v (valued_cornerFactor_sub_one_le v hk hr) (by omega)
    have hdeep : ∀ i : Fin 3, ∀ {u : v.adicCompletion ℚ}, Valued.v (u - 1) ≤ WithZero.exp (2 * (R : ℤ) - N) →
        Valued.v (u - 1) ≤ WithZero.exp (-((c i : ℤ) + 1)) := by
      intro i u hu
      have := hNc i
      exact valued_le_exp_of_le v hu (by omega)
    have hA : gl3Det v g / lowerMinor v g ≠ 0 := div_ne_zero (gl3Det_ne_zero v g) hl
    have hB : lowerMinor v g / cornerEntry v g ≠ 0 := div_ne_zero hl hc
    have hn₁ : ‖gl3Det v k / lowerFactor v k (cellRatio v g)‖ = 1 :=
      norm_eq_one_of_valued_eq_one v (by rw [map_div₀, hD, hF1, div_one])
    have hn₃ : ‖cornerFactor v k (cellRatio v g)‖ = 1 := norm_eq_one_of_valued_eq_one v hF0
    unfold cellValue
    rw [gl3Det_mul, lowerMinor_mul_eq hc hl k, cornerEntry_mul_eq hc k, mul_div_mul_comm (a := gl3Det v g),
      mul_div_mul_comm (a := lowerMinor v g), charExt_mul_eq_of_valued_sub_one_le v (χ 0) (hχ 0) hA (hdeep 0 hu₁),
      charExt_mul_eq_of_valued_sub_one_le v (χ 1) (hχ 1) hB (hdeep 1 hu₂),
      charExt_mul_eq_of_valued_sub_one_le v (χ 2) (hχ 2) hc (hdeep 2 hu₃), norm_mul, norm_mul, hn₁, hn₃, mul_one,
      mul_one]
  rw [cellSectionOf_apply_of_mem v χ Φ hgk, cellSectionOf_apply_of_mem v χ Φ hg, hval, hΦ]

private theorem exists_level_cellSectionOf_mul_eq (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (c : Fin 3 → ℕ)
    (hχ : ∀ i, HasConductorExponentAt ℚ v (χ i) (c i)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ N : ℕ, ∀ k ∈ principalCongruenceSet3 v N, ∀ g : LocalGL3 v,
      cellSectionOf v χ Φ (g * k) = cellSectionOf v χ Φ g := by
  obtain ⟨R, hR⟩ := exists_box_of_hasCompactSupport Φ hΦc
  obtain ⟨e, he⟩ := exists_uniform_level_of_isLocallyConstant Φ hΦ hΦc
  have hcD : ∀ i, c i ≤ c 0 + c 1 + c 2 := by
    intro i
    fin_cases i
    · show c 0 ≤ c 0 + c 1 + c 2
      omega
    · show c 1 ≤ c 0 + c 1 + c 2
      omega
    · show c 2 ≤ c 0 + c 1 + c 2
      omega
  have key : ∀ k' ∈ principalCongruenceSet3 v (3 * R + e + (c 0 + c 1 + c 2 + 1)), ∀ g' : LocalGL3 v,
      cellSectionOf v χ Φ g' ≠ 0 → cellSectionOf v χ Φ (g' * k') = cellSectionOf v χ Φ g' := by
    intro k' hk' g' hne
    have hg' : g' ∈ bigCell3 v := by
      by_contra h
      exact hne (cellSectionOf_apply_of_notMem v χ Φ h)
    have hΦne : Φ (cellRatio v g') ≠ 0 := by
      rw [cellSectionOf_apply_of_mem v χ Φ hg'] at hne
      exact right_ne_zero_of_mul hne
    exact cellSectionOf_mul_eq_of_mem v χ c hχ Φ he (by omega) (by omega)
      (fun i => by have := hcD i; omega) hk' hg' (hR _ hΦne)
  refine ⟨3 * R + e + (c 0 + c 1 + c 2 + 1), fun k hk g => ?_⟩
  by_cases h0 : cellSectionOf v χ Φ g = 0
  · by_contra hne
    have h1 : cellSectionOf v χ Φ (g * k) ≠ 0 := fun h => hne (by rw [h, h0])
    have h2 := key k⁻¹ (inv_mem_principalCongruenceSet3 v (by omega) hk) (g * k) h1
    rw [mul_inv_cancel_right g k] at h2
    exact h1 (h2.symm.trans h0)
  · exact key k hk g h0

private theorem exists_level_jacquetWhittaker3_mul_antidiagonal3_mul_eq (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 3 → ℕ) (hχ : ∀ i, HasConductorExponentAt ℚ v (χ i) (c i)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ N : ℕ, ∀ k ∈ principalCongruenceSet3 v N, ∀ g : LocalGL3 v,
      jacquetWhittaker3 v χ Φ (g * k * antidiagonal3 v) = jacquetWhittaker3 v χ Φ (g * antidiagonal3 v) := by
  obtain ⟨N, hN⟩ := exists_level_cellSectionOf_mul_eq v χ c hχ Φ hΦ hΦc
  refine ⟨N, fun k hk g => ?_⟩
  rw [jacquetWhittaker3_apply, jacquetWhittaker3_apply]
  have hfun : gl3AmbientRightTranslate (R := ℂ) (g * k * antidiagonal3 v) (cellSectionOf v χ Φ) =
      gl3AmbientRightTranslate (R := ℂ) (g * antidiagonal3 v) (cellSectionOf v χ Φ) := by
    funext y
    rw [gl3AmbientRightTranslate_apply, gl3AmbientRightTranslate_apply]
    have hw := antidiagonal3_mul_antidiagonal3 v
    have hy : y * (g * k * antidiagonal3 v) =
        y * (g * antidiagonal3 v) * (antidiagonal3 v * k * antidiagonal3 v) := by
      calc y * (g * k * antidiagonal3 v)
          = y * (g * ((antidiagonal3 v * antidiagonal3 v) * k) * antidiagonal3 v) := by rw [hw, one_mul]
        _ = y * (g * antidiagonal3 v) * (antidiagonal3 v * k * antidiagonal3 v) := by simp only [mul_assoc]
    rw [hy, hN _ (antidiagonal3_mul_mul_antidiagonal3_mem v hk) _]
  rw [hfun]

private theorem exists_isOpen_subgroup_jacquetWhittaker3_mul_antidiagonal3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 3 → ℕ) (hχ : ∀ i, HasConductorExponentAt ℚ v (χ i) (c i)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v,
      jacquetWhittaker3 v χ Φ (g * k * antidiagonal3 v) = jacquetWhittaker3 v χ Φ (g * antidiagonal3 v) := by
  obtain ⟨N, hN⟩ := exists_level_jacquetWhittaker3_mul_antidiagonal3_mul_eq v χ c hχ Φ hΦ hΦc
  exact exists_isOpen_subgroup_of_principalCongruenceSet3 v
    (fun h => jacquetWhittaker3 v χ Φ (h * antidiagonal3 v)) N hN

end Smoothness

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix Topology Filter

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TwistRegularity

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isLocallyConstant_of_forall_valued_eq_one {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hχ : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → χ u = 1) :
    IsLocallyConstant χ := by
  refine (IsLocallyConstant.iff_eventually_eq χ).2 fun x => ?_
  have hx0 : Valued.v (x : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  obtain ⟨m, hxm⟩ : ∃ m : ℤ, Valued.v (x : v.adicCompletion ℚ) = WithZero.exp m :=
    ⟨WithZero.log (Valued.v (x : v.adicCompletion ℚ)), (WithZero.exp_log hx0).symm⟩
  have hball : {y : (v.adicCompletion ℚ)ˣ |
      Valued.v ((y : v.adicCompletion ℚ) - x) ≤ WithZero.exp (-(1 - m))} ∈ 𝓝 x := by
    refine ((isClopen_setOf_valued_sub_le v (x : v.adicCompletion ℚ) (1 - m)).isOpen.preimage
      Units.continuous_val).mem_nhds ?_
    show Valued.v ((x : v.adicCompletion ℚ) - x) ≤ WithZero.exp (-(1 - m))
    simp
  filter_upwards [hball] with y hy
  have hlt : Valued.v ((y : v.adicCompletion ℚ) - x) < Valued.v (x : v.adicCompletion ℚ) := by
    rw [hxm]
    exact lt_of_le_of_lt hy (WithZero.exp_lt_exp.2 (by omega))
  have hyx : Valued.v (y : v.adicCompletion ℚ) = Valued.v (x : v.adicCompletion ℚ) :=
    Valuation.map_eq_of_sub_lt _ hlt
  have hu : Valued.v ((x⁻¹ * y : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hyx, inv_mul_cancel₀ hx0]
  calc χ y = χ (x * (x⁻¹ * y)) := by rw [mul_inv_cancel_left]
    _ = χ x := by rw [map_mul, hχ _ hu, mul_one]

private theorem isLocallyConstant_of_hasConductorExponentAt_zero {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hχ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ 0) : IsLocallyConstant χ :=
  isLocallyConstant_of_forall_valued_eq_one v ((LanglandsTunnell.TateLocal.hasConductorExponentAt_zero_iff ℚ v).1 hχ)

end TwistRegularity

section LocalComponent

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem norm_localChar_eq_one_of_isUnitaryChar {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hω : AutomorphicForm.IsUnitaryChar (𝓞 ℚ) ℚ ω) (u : (v.adicCompletion ℚ)ˣ) :
    ‖((NumberField.TateGlobal.localChar ω v u : ℂˣ) : ℂ)‖ = 1 := by
  rw [NumberField.TateGlobal.localChar_apply]
  exact hω _

private theorem norm_localChar_eq_one_of_isAdmissibleTwist {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hω : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ω) (u : (v.adicCompletion ℚ)ˣ) :
    ‖((NumberField.TateGlobal.localChar ω v u : ℂˣ) : ℂ)‖ = 1 :=
  norm_localChar_eq_one_of_isUnitaryChar v hω.2.2 u

private theorem norm_prod_apply_eq_one_of_eq_localChar {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hω : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ω) {ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hν : ν 0 * ν 1 * ν 2 = NumberField.TateGlobal.localChar ω v) (u : (v.adicCompletion ℚ)ˣ) :
    ‖(((ν 0 * ν 1 * ν 2) u : ℂˣ) : ℂ)‖ = 1 := by
  rw [hν]
  exact norm_localChar_eq_one_of_isAdmissibleTwist v hω u

end LocalComponent

section Scalars

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem scalar_eq_diagonal3_const (z : (v.adicCompletion ℚ)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) z = diagonal3 v (fun _ => z) := by
  refine Units.ext ?_
  change Matrix.scalar (Fin 3) (z : v.adicCompletion ℚ) = Matrix.diagonal fun _ => (z : v.adicCompletion ℚ)
  exact Matrix.scalar_apply _

private theorem scalar_mul_comm (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) z * g = g * Matrix.GeneralLinearGroup.scalar (Fin 3) z := by
  refine Units.ext ?_
  change Matrix.scalar (Fin 3) (z : v.adicCompletion ℚ) * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
    (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * Matrix.scalar (Fin 3) (z : v.adicCompletion ℚ)
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

end Scalars

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section OneEvaluation

private def outerIntegrand (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (K₂ : ℂ) (x z : v.adicCompletion ℚ) : ℂ :=
  K₂ * psiLocal ℚ v (-x) * (psiLocal ℚ v (-(1 / x) * z) * charExt ξ z)

private theorem valued_eq_exp_of_shell_condition {a₁ a₂ : ℕ} {x : v.adicCompletion ℚ} (hx0 : x ≠ 0)
    (h : Valued.v (-(1 / x)) * WithZero.exp ((a₁ : ℤ) + a₂) = WithZero.exp (a₁ : ℤ)) :
    Valued.v x = WithZero.exp (a₂ : ℤ) := by
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v x = WithZero.exp k := ⟨_, (WithZero.exp_log hvx).symm⟩
  rw [Valuation.map_neg, map_div₀, map_one, one_div, hk, ← WithZero.exp_neg, ← WithZero.exp_add,
    WithZero.exp_inj] at h
  rw [hk, WithZero.exp_inj]
  omega

private theorem shell_condition_of_valued_eq_exp {a₁ a₂ : ℕ} {x : v.adicCompletion ℚ}
    (hx : Valued.v x = WithZero.exp (a₂ : ℤ)) :
    Valued.v (-(1 / x)) * WithZero.exp ((a₁ : ℤ) + a₂) = WithZero.exp (a₁ : ℤ) := by
  rw [Valuation.map_neg, map_div₀, map_one, one_div, hx, ← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_inj]
  ring

private theorem shell_condition_two_of_valued_eq_exp {a₂ : ℕ} {x : v.adicCompletion ℚ}
    (hx : Valued.v x = WithZero.exp (a₂ : ℤ)) :
    Valued.v (-(1 / x)) * WithZero.exp (2 * (a₂ : ℤ)) = WithZero.exp (a₂ : ℤ) := by
  rw [Valuation.map_neg, map_div₀, map_one, one_div, hx, ← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_inj]
  ring

private theorem charExt_neg_one_div (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x : v.adicCompletion ℚ} (hx0 : x ≠ 0) :
    charExt ξ (-(1 / x)) = charExt ξ (-1) * (charExt ξ x)⁻¹ := by
  rw [one_div, neg_eq_neg_one_mul x⁻¹, charExt_mul_of_ne_zero v ξ (neg_ne_zero.mpr one_ne_zero) (inv_ne_zero hx0),
    charExt_inv_of_ne_zero v ξ hx0]

private theorem exists_indicator_outerWeight_mul_setIntegral_cornerIntegrand_eq (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {a₁ a₂ : ℕ} (h₁ : 1 ≤ a₁) (hν₁ : HasConductorExponentAt ℚ v (ν 1) a₁) (r : ℝ) {r₁ r₂ : ℝ}
    (hr₁ : ∀ w : v.adicCompletion ℚ, Valued.v w = WithZero.exp (a₂ : ℤ) → ‖w‖ = r₁)
    (hr₂ : ∀ w : v.adicCompletion ℚ, Valued.v w = WithZero.exp (2 * (a₂ : ℤ)) → ‖w‖ = r₂) :
    letI := localBorel ℚ v
    ∃ C₁ : ℂ, C₁ ≠ 0 ∧ ∀ x z : v.adicCompletion ℚ,
      (cornerPairs v a₂).indicator (outerWeight v ν r) (x, z) *
          ∫ y in cornerShell v ((a₁ : ℤ) + a₂) x z, cornerIntegrand v (ν 1) x z y ∂selfDualHaarAt ℚ v =
        {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (a₂ : ℤ)}.indicator (fun _ => (1 : ℂ)) x *
          {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (2 * (a₂ : ℤ))}.indicator
            (outerIntegrand v (ν 2)
              ((charExt (ν 0) (-1))⁻¹ * (charExt (ν 1) (-1))⁻¹ * C₁ * ((r⁻¹ / r₂ : ℝ) : ℂ) * ((r₁⁻¹ : ℝ) : ℂ)) x)
            z := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI : (selfDualHaarAt ℚ v).Regular := regular_selfDualHaarAt ℚ v
  obtain ⟨C₁, hC₁, hG₁⟩ := exists_gaussShellAt_psiLocal_rat_eq_ite (μ := selfDualHaarAt ℚ v) hν₁ h₁ ((a₁ : ℤ) + a₂)
  refine ⟨C₁, hC₁, fun x z => ?_⟩
  by_cases hp : (x, z) ∈ cornerPairs v a₂
  · obtain ⟨hz0, hx0⟩ := ne_zero_of_mem_cornerPairs v hp
    rw [Set.indicator_of_mem hp]
    unfold cornerShell cornerIntegrand
    rw [setIntegral_addChar_neg_mul_charExt_sub_div_eq (ν 1) ((a₁ : ℤ) + a₂) hx0 z, hG₁]
    by_cases hx : Valued.v x = WithZero.exp (a₂ : ℤ)
    · have hz : Valued.v z = WithZero.exp (2 * (a₂ : ℤ)) := valued_eq_of_mem_cornerPairs v hp hx
      have hxX : x ∈ {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (a₂ : ℤ)} := hx
      have hzZ : z ∈ {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (2 * (a₂ : ℤ))} := hz
      rw [if_pos (shell_condition_of_valued_eq_exp v hx), Set.indicator_of_mem hxX, Set.indicator_of_mem hzZ]
      dsimp only [outerWeight, outerIntegrand]
      rw [hr₁ x hx, hr₂ z hz, charExt_neg_one_div v (ν 1) hx0]
      have e : -(z / x) = -(1 / x) * z := by ring
      rw [e]
      have hA : charExt (ν 1) x ≠ 0 := charExt_ne_zero v (ν 1) hx0
      rw [mul_inv, inv_inv]
      linear_combination
        ((charExt (ν 0) (-1))⁻¹ * psiLocal ℚ v (-x) * charExt (ν 2) z * ((r⁻¹ / r₂ : ℝ) : ℂ) * ((r₁⁻¹ : ℝ) : ℂ) *
          psiLocal ℚ v (-(1 / x) * z) * (charExt (ν 1) (-1))⁻¹ * C₁) * inv_mul_cancel₀ hA
    · have hxX : x ∉ {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (a₂ : ℤ)} := hx
      have hcond : ¬ (Valued.v (-(1 / x)) * WithZero.exp ((a₁ : ℤ) + a₂) = WithZero.exp (a₁ : ℤ)) :=
        fun h => hx (valued_eq_exp_of_shell_condition v hx0 h)
      simp only [if_neg hcond, mul_zero, Set.indicator_of_notMem hxX, zero_mul]
  · rw [Set.indicator_of_notMem hp, zero_mul]
    by_cases hx : Valued.v x = WithZero.exp (a₂ : ℤ)
    · by_cases hz : Valued.v z = WithZero.exp (2 * (a₂ : ℤ))
      · exact absurd (mem_cornerPairs_of_valued v hx hz) hp
      · have hzZ : z ∉ {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (2 * (a₂ : ℤ))} := hz
        rw [Set.indicator_of_notMem hzZ, mul_zero]
    · have hxX : x ∉ {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (a₂ : ℤ)} := hx
      rw [Set.indicator_of_notMem hxX, zero_mul]

private theorem exists_setIntegral_outerIntegrand_eq (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {a₂ : ℕ} (h₂ : 1 ≤ a₂)
    (hξ : HasConductorExponentAt ℚ v ξ a₂) (K₂ : ℂ) :
    letI := localBorel ℚ v
    ∃ C₂ : ℂ, C₂ ≠ 0 ∧ ∀ x ∈ {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (a₂ : ℤ)},
      (∫ z in {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (2 * (a₂ : ℤ))}, outerIntegrand v ξ K₂ x z
          ∂selfDualHaarAt ℚ v) =
        K₂ * (charExt ξ (-1))⁻¹ * C₂ * (psiLocal ℚ v (-1 * x) * charExt ξ x) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI : (selfDualHaarAt ℚ v).Regular := regular_selfDualHaarAt ℚ v
  obtain ⟨C₂, hC₂, hG₂⟩ := exists_gaussShellAt_psiLocal_rat_eq_ite (μ := selfDualHaarAt ℚ v) hξ h₂ (2 * (a₂ : ℤ))
  refine ⟨C₂, hC₂, fun x hx => ?_⟩
  have hx' : Valued.v x = WithZero.exp (a₂ : ℤ) := hx
  have hx0 : x ≠ 0 := ne_zero_of_valued_eq_exp hx'
  unfold outerIntegrand
  rw [integral_const_mul]
  have hG : (∫ z in {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (2 * (a₂ : ℤ))},
      psiLocal ℚ v (-(1 / x) * z) * charExt ξ z ∂selfDualHaarAt ℚ v) =
        gaussShellAt ℚ v (selfDualHaarAt ℚ v) (psiLocal ℚ v) ξ (2 * (a₂ : ℤ)) (-(1 / x)) := rfl
  rw [hG, hG₂, if_pos (shell_condition_two_of_valued_eq_exp v hx'), charExt_neg_one_div v ξ hx0, neg_one_mul]
  rw [mul_inv, inv_inv]
  ring

private theorem exists_jacquetTruncated3_translate_eq (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {a₁ a₂ : ℕ}
    (h₁ : 1 ≤ a₁) (h₂ : 1 ≤ a₂) (hν₁ : HasConductorExponentAt ℚ v (ν 1) a₁)
    (hν₂ : HasConductorExponentAt ℚ v (ν 2) a₂)
    (hint : JacquetIntegrable v
      (gl3AmbientRightTranslate (R := ℂ) (antidiagonal3 v) (cellSectionOf v ν (conductorDatum v ν a₁ a₂)))) :
    ∃ K : ℂ, K ≠ 0 ∧ ∀ c : ℤ, (a₁ : ℤ) + a₂ ≤ c →
      jacquetTruncated3 v c
        (gl3AmbientRightTranslate (R := ℂ) (antidiagonal3 v) (cellSectionOf v ν (conductorDatum v ν a₁ a₂))) = K := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI : (selfDualHaarAt ℚ v).Regular := regular_selfDualHaarAt ℚ v
  obtain ⟨r, hr0, hr⟩ := exists_norm_eq_of_valued_eq_exp ℚ v ((a₁ : ℤ) + a₂)
  obtain ⟨r₁, hr₁0, hr₁⟩ := exists_norm_eq_of_valued_eq_exp ℚ v (a₂ : ℤ)
  obtain ⟨r₂, hr₂0, hr₂⟩ := exists_norm_eq_of_valued_eq_exp ℚ v (2 * (a₂ : ℤ))
  obtain ⟨C₁, hC₁, hpt⟩ := exists_indicator_outerWeight_mul_setIntegral_cornerIntegrand_eq v ν h₁ hν₁ r hr₁ hr₂
  obtain ⟨C₂, hC₂, hmid⟩ := exists_setIntegral_outerIntegrand_eq v (ν 2) h₂ hν₂
    ((charExt (ν 0) (-1))⁻¹ * (charExt (ν 1) (-1))⁻¹ * C₁ * ((r⁻¹ / r₂ : ℝ) : ℂ) * ((r₁⁻¹ : ℝ) : ℂ))
  obtain ⟨C₃, hC₃, hG₃⟩ := exists_gaussShellAt_psiLocal_rat_eq_ite (μ := selfDualHaarAt ℚ v) hν₂ h₂ (a₂ : ℤ)
  have hν2neg : charExt (ν 2) (-1 : v.adicCompletion ℚ) ≠ 0 := charExt_ne_zero v (ν 2) (neg_ne_zero.mpr one_ne_zero)
  have hK₂ : (charExt (ν 0) (-1))⁻¹ * (charExt (ν 1) (-1))⁻¹ * C₁ * ((r⁻¹ / r₂ : ℝ) : ℂ) * ((r₁⁻¹ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (inv_ne_zero (charExt_ne_zero v (ν 0) (neg_ne_zero.mpr one_ne_zero)))
      (inv_ne_zero (charExt_ne_zero v (ν 1) (neg_ne_zero.mpr one_ne_zero)))) hC₁)
      (Complex.ofReal_ne_zero.mpr (div_ne_zero (inv_ne_zero hr0.ne') hr₂0.ne')))
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero hr₁0.ne'))
  refine ⟨(charExt (ν 0) (-1))⁻¹ * (charExt (ν 1) (-1))⁻¹ * C₁ * ((r⁻¹ / r₂ : ℝ) : ℂ) * ((r₁⁻¹ : ℝ) : ℂ) *
      (charExt (ν 2) (-1))⁻¹ * C₂ * ((charExt (ν 2) (-1))⁻¹ * C₃),
    mul_ne_zero (mul_ne_zero (mul_ne_zero hK₂ (inv_ne_zero hν2neg)) hC₂) (mul_ne_zero (inv_ne_zero hν2neg) hC₃),
    fun c hc => ?_⟩
  have hXm : MeasurableSet {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (a₂ : ℤ)} :=
    measurableSet_setOf_valued_eq_exp (a₂ : ℤ)
  have hZm : MeasurableSet {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (2 * (a₂ : ℤ))} :=
    measurableSet_setOf_valued_eq_exp (2 * (a₂ : ℤ))
  have hBc : MeasurableSet {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} :=
    measurableSet_closedBall_valued (WithZero.exp c)
  have hB2c : MeasurableSet {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)} :=
    measurableSet_closedBall_valued (WithZero.exp (2 * c))
  have hXsub : {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (a₂ : ℤ)} ⊆
      {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} := by
    intro w hw
    show Valued.v w ≤ WithZero.exp c
    rw [show Valued.v w = WithZero.exp (a₂ : ℤ) from hw, WithZero.exp_le_exp]
    omega
  have hZsub : {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (2 * (a₂ : ℤ))} ⊆
      {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)} := by
    intro w hw
    show Valued.v w ≤ WithZero.exp (2 * c)
    rw [show Valued.v w = WithZero.exp (2 * (a₂ : ℤ)) from hw, WithZero.exp_le_exp]
    omega
  have hred : jacquetTruncated3 v c
        (gl3AmbientRightTranslate (R := ℂ) (antidiagonal3 v) (cellSectionOf v ν (conductorDatum v ν a₁ a₂))) =
      ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c},
        ∫ z in {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)},
          (cornerPairs v a₂).indicator (outerWeight v ν r) (x, z) *
            ∫ y in cornerShell v ((a₁ : ℤ) + a₂) x z, cornerIntegrand v (ν 1) x z y ∂selfDualHaarAt ℚ v
        ∂selfDualHaarAt ℚ v ∂selfDualHaarAt ℚ v :=
    jacquetTruncated3_translate_eq_iterated v ν hr hint hc
  have hinner : ∀ x : v.adicCompletion ℚ,
      (∫ z in {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)},
          (cornerPairs v a₂).indicator (outerWeight v ν r) (x, z) *
            ∫ y in cornerShell v ((a₁ : ℤ) + a₂) x z, cornerIntegrand v (ν 1) x z y ∂selfDualHaarAt ℚ v
          ∂selfDualHaarAt ℚ v) =
        {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (a₂ : ℤ)}.indicator
          (fun x => ∫ z in {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (2 * (a₂ : ℤ))},
            outerIntegrand v (ν 2)
              ((charExt (ν 0) (-1))⁻¹ * (charExt (ν 1) (-1))⁻¹ * C₁ * ((r⁻¹ / r₂ : ℝ) : ℂ) * ((r₁⁻¹ : ℝ) : ℂ)) x z
            ∂selfDualHaarAt ℚ v) x := by
    intro x
    rw [setIntegral_congr_fun hB2c fun z _ => hpt x z, integral_const_mul, setIntegral_indicator hZm,
      Set.inter_eq_right.mpr hZsub]
    by_cases hx : x ∈ {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (a₂ : ℤ)}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  rw [hred, setIntegral_congr_fun hBc fun x _ => hinner x, setIntegral_indicator hXm, Set.inter_eq_right.mpr hXsub,
    setIntegral_congr_fun hXm hmid, integral_const_mul]
  have hG : (∫ x in {w : v.adicCompletion ℚ | Valued.v w = WithZero.exp (a₂ : ℤ)},
      psiLocal ℚ v (-1 * x) * charExt (ν 2) x ∂selfDualHaarAt ℚ v) =
        gaussShellAt ℚ v (selfDualHaarAt ℚ v) (psiLocal ℚ v) (ν 2) (a₂ : ℤ) (-1) := rfl
  have hcond : Valued.v (-1 : v.adicCompletion ℚ) * WithZero.exp (a₂ : ℤ) = WithZero.exp (a₂ : ℤ) := by
    rw [Valuation.map_neg, map_one, one_mul]
  rw [hG, hG₃, if_pos hcond]

private theorem jacquetWhittaker3_conductorDatum_one_mul_antidiagonal3_ne_zero (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {a₁ a₂ : ℕ} (h₁ : 1 ≤ a₁) (h₂ : 2 ≤ a₂) (hν₁ : HasConductorExponentAt ℚ v (ν 1) a₁)
    (hν₂ : HasConductorExponentAt ℚ v (ν 2) a₂)
    (hst : ∀ h : LocalGL3 v,
      JacquetIntegrable v (gl3AmbientRightTranslate (R := ℂ) h (cellSectionOf v ν (conductorDatum v ν a₁ a₂))) ∧
        Stabilises v (gl3AmbientRightTranslate (R := ℂ) h (cellSectionOf v ν (conductorDatum v ν a₁ a₂)))) :
    jacquetWhittaker3 v ν (conductorDatum v ν a₁ a₂) (1 * antidiagonal3 v) ≠ 0 := by
  obtain ⟨K, hK, hKc⟩ :=
    exists_jacquetTruncated3_translate_eq v ν h₁ (by omega) hν₁ hν₂ (hst (antidiagonal3 v)).1
  obtain ⟨L, hL⟩ := (hst (antidiagonal3 v)).2
  rw [one_mul, jacquetWhittaker3_apply]
  have hc : (a₁ : ℤ) + a₂ ≤
      max (jacquetLevel v
        (gl3AmbientRightTranslate (R := ℂ) (antidiagonal3 v) (cellSectionOf v ν (conductorDatum v ν a₁ a₂))) : ℤ)
        ((a₁ : ℤ) + a₂) :=
    le_max_right _ _
  have hval := jacquetTruncated3_eq_jacquetValue v
    (gl3AmbientRightTranslate (R := ℂ) (antidiagonal3 v) (cellSectionOf v ν (conductorDatum v ν a₁ a₂))) ⟨L, hL⟩
    (le_max_left (jacquetLevel v
      (gl3AmbientRightTranslate (R := ℂ) (antidiagonal3 v) (cellSectionOf v ν (conductorDatum v ν a₁ a₂))) : ℤ)
      ((a₁ : ℤ) + a₂))
  rw [← hval, hKc _ hc]
  exact hK

end OneEvaluation

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.TateLocal MeasureTheory"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.localLFactorAt CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero cellRatio cellValue charExt_units_mul antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 isClopen_valued_le_one continuous_gl3Entry IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 inducedCoeff upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 IsBadPlace unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_diagonal3_mul jacquetWhittaker3 jacquetWhittaker3_apply converseCongruenceSet3 one_mem_converseCongruenceSet3 IsCongruenceEquivariantAt HasVanishingUnipotentIntegralAt dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le isClopen_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lastRowSup bottomMinor minorSup detSize exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt exists_norm_jacquetWhittaker3_le_of_rootSize_le exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section SlotOrder

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_perm_le_le (a : Fin 3 → ℕ) (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    ∃ σ : Equiv.Perm (Fin 3), a (σ 0) ≤ a (σ 2) ∧ a (σ 1) ≤ a (σ 2) ∧
      (ν ∘ σ) 0 * (ν ∘ σ) 1 * (ν ∘ σ) 2 = ν 0 * ν 1 * ν 2 := by
  by_cases h2 : a 0 ≤ a 2 ∧ a 1 ≤ a 2
  · exact ⟨Equiv.refl _, h2.1, h2.2, rfl⟩
  by_cases h0 : a 2 ≤ a 0 ∧ a 1 ≤ a 0
  · refine ⟨Equiv.swap 0 2, ?_, ?_, ?_⟩
    · rw [Equiv.swap_apply_left, Equiv.swap_apply_right]; exact h0.1
    · rw [Equiv.swap_apply_of_ne_of_ne (show (1 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 2 by decide),
        Equiv.swap_apply_right]
      exact h0.2
    · simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (show (1 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 2 by decide)]
      ext u
      simp only [MonoidHom.mul_apply, Units.val_mul]
      ring
  · refine ⟨Equiv.swap 1 2, ?_, ?_, ?_⟩
    · rw [Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide),
        Equiv.swap_apply_right]
      omega
    · rw [Equiv.swap_apply_left, Equiv.swap_apply_right]; omega
    · simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)]
      ext u
      simp only [MonoidHom.mul_apply, Units.val_mul]
      ring

end SlotOrder

section ScalarClosure

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isGL3PsiWhittakerFn_const_mul {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (c : ℂ) : IsGL3PsiWhittakerFn ψ (fun h => c * W h) := by
  intro x y z g
  show c * W (upperUnipotent3 x y z * g) = ψ (x + y) * (c * W g)
  rw [hW x y z g]
  ring

private theorem isCongruenceEquivariantAt_const_mul {m : ℕ} {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    {W : LocalGL3 v → ℂ} (hW : IsCongruenceEquivariantAt v m χ W) (c : ℂ) :
    IsCongruenceEquivariantAt v m χ (fun h => c * W h) := by
  intro k hk u hu g
  show c * W (g * k) = ((χ u : ℂˣ) : ℂ) * (c * W g)
  rw [hW k hk u hu g]
  ring

private theorem hasVanishingUnipotentIntegralAt_const_mul {W : LocalGL3 v → ℂ}
    (hW : HasVanishingUnipotentIntegralAt v W) (c : ℂ) : HasVanishingUnipotentIntegralAt v (fun h => c * W h) := by
  intro g
  have hg := hW g
  simp only [MeasureTheory.integral_const_mul, hg, mul_zero]

end ScalarClosure

section LocalWhittaker

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_localWhittaker_of_triple (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω₁ : IsAdmissibleTwist ℚ ω)
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → ℕ)
    (hlc : ∀ i, IsLocallyConstant (ν i))
    (hexp : ∀ i, 1 ≤ a i ∧ LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i) (a i))
    (h₀₂ : a 0 ≤ a 2) (h₁₂ : a 1 ≤ a 2) (h₂ : 2 ≤ a 2)
    (hu : ∀ i, ‖((ν i (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (hprod : ν 0 * ν 1 * ν 2 = localChar ω v) :
        ∃ a₀ : ℕ, ∀ c : ℕ, a₀ ≤ c →
          ∃ W : LocalGL3 v → ℂ,
          W 1 = 1 ∧
          (IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v) W) ∧
          (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) ∧
          (∀ m : ℕ, (∑ i, a i) ≤ m → IsCongruenceEquivariantAt v m (localChar ω v) W) ∧
          (HasVanishingUnipotentIntegralAt v W) ∧
          (∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
            (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
            (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
              ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) ∧
          (∀ (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
        W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((localChar ω v z : ℂˣ) : ℂ) * W g) ∧
            ∀ χ : (v.adicCompletion ℚ)ˣ →* ℂˣ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ 0 →
              ‖((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1 →
              ∀ g ∈ converseCongruenceSet3 v c,
                (letI := localBorel ℚ v
    ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
        P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        W χ g σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            W χ s g =
          (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ) s) * P s) ∧
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (dualWhittakerFn3 W)
        χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
      ∃ a : Fin 3 → ℕ, (∀ i, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i * χ) (a i)) ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W χ (1 - s) g =
            (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
              ((∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i * χ)) *
                (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) * P s) := by

  have hν₀ := (hexp 0).2
  have hν₁ := (hexp 1).2
  have hν₂ := (hexp 2).2
  have hΦlc : IsLocallyConstant (conductorDatum v ν (a 1) (a 2)) :=
    isLocallyConstant_conductorDatum v ν (a 1) (a 2) hν₀ (hexp 0).1 hν₁ (hexp 1).1
  have hΦc : HasCompactSupport (conductorDatum v ν (a 1) (a 2)) := hasCompactSupport_conductorDatum v ν (a 1) (a 2)

  have hst : ∀ h : LocalGL3 v,
      JacquetIntegrable v (gl3AmbientRightTranslate (R := ℂ) h (cellSectionOf v ν (conductorDatum v ν (a 1) (a 2))))
        ∧ Stabilises v (gl3AmbientRightTranslate (R := ℂ) h (cellSectionOf v ν (conductorDatum v ν (a 1) (a 2)))) :=
    fun h => jacquetIntegrable_and_stabilises_of_exists_forall_le v _
      (LanglandsTunnell.CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν
        hlc (conductorDatum v ν (a 1) (a 2)) ⟨hΦlc, hΦc⟩ h)

  have hne : jacquetWhittaker3 v ν (conductorDatum v ν (a 1) (a 2)) (1 * antidiagonal3 v) ≠ 0 :=
    jacquetWhittaker3_conductorDatum_one_mul_antidiagonal3_ne_zero v ν (hexp 1).1 h₂ hν₁ hν₂ hst
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ,
      κ = (jacquetWhittaker3 v ν (conductorDatum v ν (a 1) (a 2)) (1 * antidiagonal3 v))⁻¹ := ⟨_, rfl⟩

  have hprodu : ∀ u : (v.adicCompletion ℚ)ˣ,
      ((localChar ω v u : ℂˣ) : ℂ) = ((ν 0 u : ℂˣ) : ℂ) * ((ν 1 u : ℂˣ) : ℂ) * ((ν 2 u : ℂˣ) : ℂ) := by
    intro u
    rw [← hprod, MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul]
  have hωu : ∀ u : (v.adicCompletion ℚ)ˣ, ‖(((ν 0 * ν 1 * ν 2) u : ℂˣ) : ℂ)‖ = 1 :=
    norm_prod_apply_eq_one_of_eq_localChar v hω₁ hprod

  have hpsi : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)
      (fun h => jacquetWhittaker3 v ν (conductorDatum v ν (a 1) (a 2)) (h * antidiagonal3 v)) :=
    isGL3PsiWhittakerFn_jacquetWhittaker3_mul_antidiagonal3 v ν (conductorDatum v ν (a 1) (a 2)) fun g => (hst g).2
  have heq : ∀ m : ℕ, (∑ i, a i) ≤ m → IsCongruenceEquivariantAt v m (localChar ω v)
      (fun h => jacquetWhittaker3 v ν (conductorDatum v ν (a 1) (a 2)) (h * antidiagonal3 v)) := by
    intro m hm
    have hm' : a 0 + a 1 + a 2 ≤ m := by simpa [Fin.sum_univ_three] using hm
    exact isCongruenceEquivariantAt_jacquetWhittaker3_conductorDatum v ν hν₀ hν₁ hν₂ (hexp 0).1 (hexp 1).1
      (le_trans (by norm_num) h₂) h₀₂ h₁₂ (localChar ω v) hprodu (jacquetValue_const_mul v) hm'
  have hvan : HasVanishingUnipotentIntegralAt v
      (fun h => jacquetWhittaker3 v ν (conductorDatum v ν (a 1) (a 2)) (h * antidiagonal3 v)) :=
    hasVanishingUnipotentIntegralAt_conductorDatum_of_stabilises v ν h₂ (hexp 1).1 hν₂ hst
  obtain ⟨Uv, hUo, hUv⟩ := exists_isOpen_subgroup_jacquetWhittaker3_mul_antidiagonal3 v ν a (fun i => (hexp i).2)
    (conductorDatum v ν (a 1) (a 2)) hΦlc hΦc
  obtain ⟨B, hB⟩ := LanglandsTunnell.CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt v ν hlc
    hωu (conductorDatum v ν (a 1) (a 2)) hΦlc hΦc
  obtain ⟨t, C, hC⟩ := LanglandsTunnell.CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le v ν hlc hωu
    (conductorDatum v ν (a 1) (a 2)) hΦlc hΦc B

  refine ⟨∑ i, a i, fun c hc =>
    ⟨(fun h => κ * jacquetWhittaker3 v ν (conductorDatum v ν (a 1) (a 2)) (h * antidiagonal3 v)), ?_,
    isGL3PsiWhittakerFn_const_mul v hpsi κ, ⟨Uv, hUo, fun k hk g => ?_⟩,
    fun m hm => isCongruenceEquivariantAt_const_mul v (heq m hm) κ,
    hasVanishingUnipotentIntegralAt_const_mul v hvan κ, ⟨B, t, ‖κ‖ * C, fun h => ⟨fun hh => ?_, fun hh => ?_⟩⟩,
    fun z g => ?_, fun χ hχ₀ hχu g hg => ?_⟩⟩
  ·
    dsimp only
    rw [hκ]
    exact inv_mul_cancel₀ hne
  ·
    dsimp only
    rw [hUv k hk g]
  ·
    rw [← detSize_mul_antidiagonal3 v h, ← lastRowSup_mul_antidiagonal3 v h, ← minorSup_mul_antidiagonal3 v h] at hh
    dsimp only
    rw [hB _ hh, mul_zero]
  ·
    rw [← detSize_mul_antidiagonal3 v h, ← lastRowSup_mul_antidiagonal3 v h, ← minorSup_mul_antidiagonal3 v h] at hh ⊢
    have hb := hC (h * antidiagonal3 v) hh.1 hh.2
    dsimp only
    rw [norm_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  ·
    have hcen : Matrix.GeneralLinearGroup.scalar (Fin 3) z * g * antidiagonal3 v =
        g * antidiagonal3 v * diagonal3 v (fun _ => z) := by
      rw [mul_assoc, scalar_mul_comm, scalar_eq_diagonal3_const]
    have htor : torusChar3 v ν (fun _ => z) = ((localChar ω v z : ℂˣ) : ℂ) := by
      rw [torusChar3_const, hprodu, Fin.prod_univ_three]
    dsimp only
    rw [hcen, jacquetWhittaker3_mul_diagonal3_const, htor]
    ring
  ·
    have hc₁ : 1 ≤ c := le_trans (le_trans (le_trans (by norm_num) h₂) (Finset.single_le_sum
      (f := a) (fun i _ => Nat.zero_le _) (Finset.mem_univ 2))) hc
    have h22 : Valued.v (gl3Entry v g 2 2) = 1 := by
      rw [← gl3Entry_conj_zero_zero v g]
      exact (IsOppositeCongruence.diag_valued v hc₁ (isOppositeCongruence_conj v hg)).1
    have h22ne : gl3Entry v g 2 2 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h22
      exact zero_ne_one h22
    have hWg : ∀ x : LocalGL3 v,
        (fun h => κ * jacquetWhittaker3 v ν (conductorDatum v ν (a 1) (a 2)) (h * antidiagonal3 v)) (x * g) =
          ((localChar ω v (Units.mk0 _ h22ne) : ℂˣ) : ℂ) *
            (fun h => κ * jacquetWhittaker3 v ν (conductorDatum v ν (a 1) (a 2)) (h * antidiagonal3 v)) x :=
      isCongruenceEquivariantAt_const_mul v (heq c hc) κ g hg (Units.mk0 _ h22ne) rfl
    have hχlc : IsLocallyConstant χ := isLocallyConstant_of_hasConductorExponentAt_zero v hχ₀
    have huχ : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1 := by
      intro i
      rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hu i, hχu, mul_one]
    obtain ⟨P, σ₀, σ₁, ⟨Q, m, hPQ⟩, hc30, hz30, hc31, a', ha', hz31⟩ :=
      LanglandsTunnell.CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 v ν hlc
        (conductorDatum v ν (a 1) (a 2)) ⟨hΦlc, hΦc⟩ χ hχlc huχ
    refine ⟨fun s => ((localChar ω v (Units.mk0 _ h22ne) : ℂˣ) : ℂ) * κ * P s, σ₀, σ₁,
      ⟨Polynomial.C (((localChar ω v (Units.mk0 _ h22ne) : ℂˣ) : ℂ) * κ) * Q, m, fun s => ?_⟩, ?_, ?_, ?_,
      a', ha', fun s hs => ?_⟩
    · show ((localChar ω v (Units.mk0 _ h22ne) : ℂˣ) : ℂ) * κ * P s = _
      rw [Polynomial.eval_mul, Polynomial.eval_C, hPQ s]
      ring
    · exact isLocalZeta30ConvergentAbove_of_rightTranslate v _ _ χ hWg
        (isLocalZeta30ConvergentAbove_const_mul v _ κ _ χ hc30)
    · intro s hs
      rw [localZeta30_eq_mul_of_rightTranslate v _ _ χ s hWg, localZeta30_const_mul, hz30 s hs]
      ring
    · refine isLocalZeta31ConvergentAbove_dual_of_rightTranslate v _ _ _ χ hWg ?_
      rw [dualWhittakerFn3_const_mul]
      exact isLocalZeta31ConvergentAbove_const_mul v _ _ κ _ χ⁻¹ hc31
    · rw [localZetaDual31_eq_mul_of_rightTranslate v _ _ _ χ (1 - s) hWg, localZetaDual31_const_mul, hz31 s hs]
      ring

end LocalWhittaker

end LanglandsTunnell.CubicInduction

p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.LanglandsTunnell.CubicInduction"

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S ↔ IsBadPlace K μ v)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (hsat : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
      (∀ w ∈ primeFibre ℚ K v, ¬ IsUnramifiedCharAt μ w) ∧
        ∃ t : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) t ∧
          2 * (t : ℤ) + 12 ≤
            ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w)
    :
    ∀ v ∈ S, ∀ θ : ℂ, ‖θ‖ = 1 →
      ∃ (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → ℕ),
        (∀ i, IsLocallyConstant (ν i)) ∧
        (∀ i, 1 ≤ a i ∧ LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i) (a i)) ∧
        (∑ i, (a i : ℤ)) =
          ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w ∧
        (∀ i, ‖((ν i (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) ∧
        ν 0 * ν 1 * ν 2 = localChar ω v ∧
        (∀ s : ℂ, (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i) s) =
          ((inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹) ∧
        (∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i)) = θ ∧
        ∃ a₀ : ℕ, ∀ c : ℕ, a₀ ≤ c →
          ∃ W : LocalGL3 v → ℂ,
          W 1 = 1 ∧
          (IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v) W) ∧
          (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) ∧
          (∀ m : ℕ, (∑ i, a i) ≤ m → IsCongruenceEquivariantAt v m (localChar ω v) W) ∧
          (HasVanishingUnipotentIntegralAt v W) ∧
          (∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
            (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
            (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
              ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) ∧
          (∀ (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
        W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((localChar ω v z : ℂˣ) : ℂ) * W g) ∧
            ∀ χ : (v.adicCompletion ℚ)ˣ →* ℂˣ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ 0 →
              ‖((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1 →
              ∀ g ∈ converseCongruenceSet3 v c,
                (letI := localBorel ℚ v
    ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
        P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        W χ g σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            W χ s g =
          (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ) s) * P s) ∧
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (dualWhittakerFn3 W)
        χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
      ∃ a : Fin 3 → ℕ, (∀ i, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i * χ) (a i)) ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W χ (1 - s) g =
            (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
              ((∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i * χ)) *
                (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) * P s) := by
  intro v hv θ hθ
  have hbad : IsBadPlace K μ v := (hS v).1 hv
  obtain ⟨ν, a, h56, h57, h58, h60, h61, h62, h64⟩ :=
    LanglandsTunnell.CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated K hdeg μ hμ ω
      hω hsat v hbad θ hθ
  obtain ⟨-, t, -, ht⟩ := hsat v hbad
  have h12 : (12 : ℤ) ≤ ∑ i, (a i : ℤ) := by
    rw [h58]
    omega
  obtain ⟨σ, hσ₀, hσ₁, hνσ⟩ := LanglandsTunnell.CubicInduction.exists_perm_le_le v a ν
  have h2 : 2 ≤ a (σ 2) := by
    have hsum : (∑ i, (a i : ℤ)) = ∑ i, ((a (σ i) : ℕ) : ℤ) := (Equiv.sum_comp σ (fun i => (a i : ℤ))).symm
    rw [hsum, Fin.sum_univ_three] at h12
    omega
  refine ⟨ν ∘ σ, a ∘ σ, fun i => h56 (σ i), fun i => h57 (σ i), ?_, fun i => h60 (σ i), ?_, ?_, ?_, ?_⟩
  · rw [← h58]
    exact Equiv.sum_comp σ (fun i => (a i : ℤ))
  · rw [← h61]
    exact hνσ
  · intro s
    rw [← h62 s]
    exact Equiv.prod_comp σ (fun i => LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i) s)
  · rw [← h64]
    exact Equiv.prod_comp σ (fun i => LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i))
  · exact LanglandsTunnell.CubicInduction.exists_localWhittaker_of_triple v ω hω.1 (ν ∘ σ) (a ∘ σ) (fun i => h56 (σ i))
      (fun i => h57 (σ i)) hσ₀ hσ₁ h2 (fun i => h60 (σ i)) (hνσ.trans h61)

end S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad (solution)
