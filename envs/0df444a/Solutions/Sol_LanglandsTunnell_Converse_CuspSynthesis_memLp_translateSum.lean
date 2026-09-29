-- Prove2me | solution 1 for LanglandsTunnell.Converse.CuspSynthesis.memLp_translateSum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/86a2c94e-6584-5331-a14c-855ed83ce335

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Theorems.Thm_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg
import Theorems.Thm_LanglandsTunnell_Converse_FinWhittakerDatum_exists_norm_Wf_globalPoints_diagOne_mul_le
import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_LanglandsTunnell_Converse_exists_archParams_of_continuous
import Theorems.Thm_LanglandsTunnell_Converse_exists_isJLTwist
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_LanglandsTunnell_JLSynthesis
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumC_exists_W_eq_fderivWithin_mul
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_W_eq_fderivWithin_mul
import Theorems.Thm_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Theorems.Thm_AutomorphicForm_exists_forall_norm_le_mul_prod_rpow_neg_of_hasDerivAt_chains_of_constantTerm_eq_zero_of_mem_idealBall
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumC_norm_iteratedFDerivWithin_diagOne_le
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_norm_iteratedFDerivWithin_diagOne_le
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
set_option Elab.async false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse"

noncomputable section

namespace CuspRealizationCT

open MeasureTheory Filter Topology Complex
open AutomorphicForm.SmoothCusp

variable (K : Type) [Field K] [NumberField K]

private abbrev instAdeleBorel : MeasurableSpace (AdeleRing (𝓞 K) K) := AdelicHaar.adeleBorel (𝓞 K) K

attribute [local instance] instAdeleBorel

private theorem continuous_unipotentGL2 :
    Continuous fun x : AdeleRing (𝓞 K) K => (unipotentGL2 x : AdelicGL2 (𝓞 K) K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x : AdeleRing (𝓞 K) K => (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) _)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x : AdeleRing (𝓞 K) K => (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) _)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

variable {K}

section RightTranslation
end RightTranslation

end CuspRealizationCT

end

noncomputable section

namespace FourierUniq

open Complex MeasureTheory Filter Topology

private def e (x : ℝ) : ℂ := exp (2 * Real.pi * I * x)

section Line
end Line

section Space
end Space

end FourierUniq

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace Fourier
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.Fourier

end

section

open scoped WithZero

namespace LocalWhittaker

variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

private def IsIntegral (K : GL (Fin 2) F) : Prop := ∀ i j : Fin 2, v ((K : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1

end LocalWhittaker

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "AdelicDock LocalGL2 UnramifiedWhittaker LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LocalWhittaker"
open scoped WithZero Classical

namespace FiniteWhittaker

variable {K : Type} [Field K] [NumberField K]

private def compAt (w : HeightOneSpectrum (𝓞 K)) : AdelicGL2 (𝓞 K) K →* GL (Fin 2) (w.adicCompletion K) :=
  (finComponent (𝓞 K) K w).comp (glFin (𝓞 K) K)

private theorem compAt_apply (w : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (compAt w g : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j
      = (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w := rfl

private theorem compAt_placeEmbed_self (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (v.adicCompletion K)) :
    compAt v (placeEmbed K v h) = h := by
  show finComponent (𝓞 K) K v (glFin (𝓞 K) K (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v h))) = h
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem compAt_placeEmbed_of_ne {v w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v)
    (h : GL (Fin 2) (v.adicCompletion K)) :
    compAt w (placeEmbed K v h) = 1 := by
  show finComponent (𝓞 K) K w (glFin (𝓞 K) K (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v h))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

private theorem isIntegral_compAt_of_mem_integral {g : AdelicGL2 (𝓞 K) K} {w : HeightOneSpectrum (𝓞 K)}
    (hg : ∀ i j : Fin 2, (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w
      ∈ w.adicCompletionIntegers K) : LocalWhittaker.IsIntegral Valued.v (compAt w g) := fun i j => by
  rw [compAt_apply]
  exact (mem_adicCompletionIntegers _ _ _).mp (hg i j)

private theorem isIntegral_compAt_inv_of_mem_integral {g : AdelicGL2 (𝓞 K) K} {w : HeightOneSpectrum (𝓞 K)}
    (hg : ∀ i j : Fin 2, (glFin (𝓞 K) K g⁻¹ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w
      ∈ w.adicCompletionIntegers K) : LocalWhittaker.IsIntegral Valued.v (compAt w g)⁻¹ := by
  rw [← map_inv]
  exact isIntegral_compAt_of_mem_integral hg

private theorem placeEmbed_mem_of_isIntegral (v : HeightOneSpectrum (𝓞 K)) {M : Ideal (𝓞 K)} (hM : ¬ v.asIdeal ∣ M)
    {k : GL (Fin 2) (v.adicCompletion K)} (hk : LocalWhittaker.IsIntegral Valued.v k)
    (hk' : LocalWhittaker.IsIntegral Valued.v k⁻¹) :
    placeEmbed K v k ∈ levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K := by
  have hMbot : M ≠ ⊥ := by
    rintro rfl
    exact hM (dvd_zero _)
  have hbound : idealBound (𝓞 K) M v = 1 := idealBound_eq_one_of_not_dvd hMbot hM
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v k) ∈ levelOne (𝓞 K) K M
    rw [finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
    refine ⟨⟨fun i j => hk i j, ?_, ?_⟩, ⟨fun i j => hk' i j, ?_, ?_⟩⟩
    · rw [hbound]; exact hk 1 0
    · rw [hbound]; exact (Valuation.map_sub _ _ _).trans (max_le (hk 1 1) (by simp))
    · rw [hbound]; exact hk' 1 0
    · rw [hbound]; exact (Valuation.map_sub _ _ _).trans (max_le (hk' 1 1) (by simp))
  · show finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v k) ∈ finiteAdelicGL2Subgroup K
    rw [mem_finiteAdelicGL2Subgroup_iff]
    exact glArch_finEmbed _ _ _

end FiniteWhittaker

end

namespace LocalWhittaker

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section MapSurj

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {L : Type*} [Field L] [Algebra R L]
  [IsFractionRing R L] (v : HeightOneSpectrum R)

private def toIntegersMatrix {g : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)}
    (hg : ∀ i j, Valued.v (g i j) ≤ 1) : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers L) :=
  fun i j => ⟨g i j, (mem_adicCompletionIntegers R L v).mpr (hg i j)⟩

private theorem toIntegersMatrix_map {g : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)}
    (hg : ∀ i j, Valued.v (g i j) ≤ 1) :
    (toIntegersMatrix v hg).map (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)) = g := by
  ext i j
  rfl

private theorem mapMatrix_injective :
    Function.Injective
      ((algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)).mapMatrix :
        Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers L) →+* Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) :=
  fun _ _ h => Matrix.map_injective (fun _ _ h' => Subtype.ext h') h

private theorem exists_map_eq_of_isIntegral {g : GL (Fin 2) (v.adicCompletion L)}
    (hg : IsIntegral Valued.v g) (hg' : IsIntegral Valued.v g⁻¹) :
    ∃ k : GL (Fin 2) (v.adicCompletionIntegers L),
      Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)) k = g := by
  have hA := toIntegersMatrix_map v hg
  have hB := toIntegersMatrix_map v hg'
  have hmul : (toIntegersMatrix v hg).map (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L))
      * (toIntegersMatrix v hg').map (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)) = 1 := by
    rw [hA, hB]
    exact Units.mul_inv g
  have hmul' : (toIntegersMatrix v hg').map (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L))
      * (toIntegersMatrix v hg).map (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)) = 1 := by
    rw [hA, hB]
    exact Units.inv_mul g
  have hAB : toIntegersMatrix v hg * toIntegersMatrix v hg' = 1 := by
    apply mapMatrix_injective v
    rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
    exact hmul
  have hBA : toIntegersMatrix v hg' * toIntegersMatrix v hg = 1 := by
    apply mapMatrix_injective v
    rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
    exact hmul'
  refine ⟨⟨toIntegersMatrix v hg, toIntegersMatrix v hg', hAB, hBA⟩, ?_⟩
  ext i j : 2
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map]
  exact congrFun (congrFun hA i) j

end MapSurj

end LocalWhittaker

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "AdelicDock LocalGL2 UnramifiedWhittaker LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LocalWhittaker"
open scoped WithZero Classical

namespace FiniteWhittaker

variable {K : Type} [Field K] [NumberField K]

section IntegralInvariance

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}

private theorem not_dvd_top (v : HeightOneSpectrum (𝓞 K)) : ¬ v.asIdeal ∣ (⊤ : Ideal (𝓞 K)) := fun h =>
  v.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp h))

private theorem wf_mul_placeEmbed_of_isIntegral (dF : FinWhittakerDatum K S Pi) (w : HeightOneSpectrum (𝓞 K))
    {k : GL (Fin 2) (w.adicCompletion K)} (hk : LocalWhittaker.IsIntegral Valued.v k)
    (hk' : LocalWhittaker.IsIntegral Valued.v k⁻¹) (g : AdelicGL2 (𝓞 K) K) :
    dF.Wf (g * placeEmbed K w k) = dF.Wf g := by
  by_cases hw : w ∈ S
  · exact dF.blind_at w hw k g
  · obtain ⟨k₀, rfl⟩ := LocalWhittaker.exists_map_eq_of_isIntegral w hk hk'
    exact dF.integral_right w hw k₀ g

private theorem isIntegral_compAt_of_mem_levelTop {u : AdelicGL2 (𝓞 K) K} (hu : u ∈ levelOne (𝓞 K) K ⊤)
    (w : HeightOneSpectrum (𝓞 K)) :
    LocalWhittaker.IsIntegral Valued.v (compAt w u) ∧ LocalWhittaker.IsIntegral Valued.v (compAt w u)⁻¹ := by
  rw [mem_levelOne_iff] at hu
  obtain ⟨h1, h2⟩ := hu
  refine ⟨isIntegral_compAt_of_mem_integral fun i j => h1.integral i j w,
    isIntegral_compAt_inv_of_mem_integral fun i j => ?_⟩
  rw [map_inv]
  exact h2.integral i j w

private theorem isLevelOneMatrix_of_top {N₀ : Ideal (𝓞 K)} (hN₀ : N₀ ≠ ⊥) {m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hm : IsLevelOneMatrix (𝓞 K) K ⊤ (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    (hcomp : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N₀ → finComponent (𝓞 K) K w m = 1) :
    IsLevelOneMatrix (𝓞 K) K N₀ (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
  have hentry : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N₀ → ∀ i j : Fin 2,
      (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w
        = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
    intro w hw i j
    have h := congrArg
      (fun x : GL (Fin 2) (w.adicCompletion K) => (x : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j) (hcomp w hw)
    simpa only [finComponent_apply, Units.val_one] using h
  refine ⟨⟨hm.integral, fun w => ?_⟩, fun w => ?_⟩
  · by_cases hw : w.asIdeal ∣ N₀
    · rw [hentry w hw 1 0, Matrix.one_apply_ne (by decide), map_zero]
      exact zero_le'
    · rw [idealBound_eq_one_of_not_dvd hN₀ hw]
      exact (mem_adicCompletionIntegers _ _ _).mp (hm.integral 1 0 w)
  · by_cases hw : w.asIdeal ∣ N₀
    · rw [coe_sub_apply, coe_one_apply, hentry w hw 1 1, Matrix.one_apply_eq, sub_self, map_zero]
      exact zero_le'
    · rw [idealBound_eq_one_of_not_dvd hN₀ hw, coe_sub_apply, coe_one_apply]
      exact (Valuation.map_sub _ _ _).trans
        (max_le ((mem_adicCompletionIntegers _ _ _).mp (hm.integral 1 1 w)) (by simp))

private theorem mem_levelOne_of_forall_compAt {N₀ : Ideal (𝓞 K)} (hN₀ : N₀ ≠ ⊥) {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K ⊤) (hcomp : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N₀ → compAt w u = 1) :
    u ∈ levelOne (𝓞 K) K N₀ := by
  rw [mem_levelOne_iff] at hu ⊢
  obtain ⟨h1, h2⟩ := hu
  refine ⟨isLevelOneMatrix_of_top hN₀ h1 hcomp, ?_⟩
  have h2' : IsLevelOneMatrix (𝓞 K) K ⊤ ((glFin (𝓞 K) K u⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
    rw [map_inv]; exact h2
  have := isLevelOneMatrix_of_top hN₀ h2' fun w hw => by
    show compAt w u⁻¹ = 1
    rw [map_inv, hcomp w hw, inv_one]
  rwa [map_inv] at this

private theorem wf_mul_eq_of_forall_compAt (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) {N₀ : Ideal (𝓞 K)}
    (hN₀ : N₀ ≠ ⊥)
    (hlevel : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N₀ ⊓ finiteAdelicGL2Subgroup K,
      dF.Wf (g * u) = dF.Wf g)
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ u ∈ levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K,
      (∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N₀ → w ∉ T → compAt w u = 1) → dF.Wf (g * u) = dF.Wf g := by
  classical
  refine Finset.induction_on T ?_ ?_
  · intro u hu hcomp
    obtain ⟨hu₁, hu₂⟩ := Subgroup.mem_inf.mp hu
    exact hlevel g u (Subgroup.mem_inf.mpr
      ⟨mem_levelOne_of_forall_compAt hN₀ hu₁ fun w hw => hcomp w hw (Finset.notMem_empty w), hu₂⟩)
  · intro w₁ T hw₁T ih u hu hcomp
    obtain ⟨hk, hk'⟩ := isIntegral_compAt_of_mem_levelTop (Subgroup.mem_inf.mp hu).1 w₁
    set u₁ := u * (placeEmbed K w₁ (compAt w₁ u))⁻¹ with hu₁_def
    have hu₁ : u₁ ∈ levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K :=
      Subgroup.mul_mem _ hu (Subgroup.inv_mem _ (placeEmbed_mem_of_isIntegral w₁ (not_dvd_top w₁) hk hk'))
    have hcomp₁ : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N₀ → w ∉ T → compAt w u₁ = 1 := by
      intro w hwN hwT
      by_cases hww : w = w₁
      · subst hww
        rw [hu₁_def, map_mul, map_inv, compAt_placeEmbed_self, mul_inv_cancel]
      · have hw : compAt w u = 1 := hcomp w hwN (by
          rw [Finset.mem_insert, not_or]
          exact ⟨hww, hwT⟩)
        rw [hu₁_def, map_mul, map_inv, compAt_placeEmbed_of_ne hww, inv_one, mul_one, hw]
    have hu_eq : u = u₁ * placeEmbed K w₁ (compAt w₁ u) := (inv_mul_cancel_right u _).symm
    rw [hu_eq, ← mul_assoc, wf_mul_placeEmbed_of_isIntegral dF w₁ hk hk', ih u₁ hu₁ hcomp₁]

private theorem wf_mul_of_mem_integral (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K) : dF.Wf (g * u) = dF.Wf g := by
  classical
  obtain ⟨N₀, hN₀, hlevel⟩ := dF.level_right
  have hfin : {w : HeightOneSpectrum (𝓞 K) | w.asIdeal ∣ N₀}.Finite :=
    Ideal.finite_factors (by rw [Submodule.zero_eq_bot]; exact hN₀)
  exact wf_mul_eq_of_forall_compAt dF g hN₀ hlevel hfin.toFinset u hu
    fun w hw hwT => absurd (hfin.mem_toFinset.mpr hw) hwT

end IntegralInvariance

end FiniteWhittaker

end

noncomputable section
namespace FiniteWhittaker
end FiniteWhittaker
end

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open NumberField.AdelicVolume NumberField.TateGlobal
open Filter Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace Ideles
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K

private theorem val_mul_inv_fst_apply (z : 𝔸ˣ) (w : InfinitePlace K) :
    (z : 𝔸).1 w * ((z⁻¹ : 𝔸ˣ) : 𝔸).1 w = 1 :=
  congrArg (fun x : 𝔸 => x.1 w) z.mul_inv

private theorem val_inv_mul_fst_apply (z : 𝔸ˣ) (w : InfinitePlace K) :
    ((z⁻¹ : 𝔸ˣ) : 𝔸).1 w * (z : 𝔸).1 w = 1 :=
  congrArg (fun x : 𝔸 => x.1 w) z.inv_mul

private def archUnitAt (w : InfinitePlace K) (z : 𝔸ˣ) : (w.Completion)ˣ where
  val := (z : 𝔸).1 w
  inv := ((z⁻¹ : 𝔸ˣ) : 𝔸).1 w
  val_inv := val_mul_inv_fst_apply z w
  inv_val := val_inv_mul_fst_apply z w

private theorem archUnitAt_val (w : InfinitePlace K) (z : 𝔸ˣ) :
    (archUnitAt w z : w.Completion) = (z : 𝔸).1 w := rfl

private structure IsUnitIdeleOff (S : Finset (HeightOneSpectrum (𝓞 K))) (u : 𝔸ˣ) : Prop where
  arch : ∀ w : InfinitePlace K, (u : 𝔸).1 w = 1
  integral : ∀ v : HeightOneSpectrum (𝓞 K), (u : 𝔸).2 v ∈ v.adicCompletionIntegers K
  integral_inv : ∀ v : HeightOneSpectrum (𝓞 K), ((u⁻¹ : 𝔸ˣ) : 𝔸).2 v ∈ v.adicCompletionIntegers K
  trivial_on : ∀ v ∈ S, (u : 𝔸).2 v = 1

section Continuity
end Continuity

end LanglandsTunnell.Converse.Ideles

end

noncomputable section
namespace FiniteWhittaker
section Centre
end Centre
section SCharacter
end SCharacter
section Series
end Series
end FiniteWhittaker
end

end

section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal"
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical

namespace FiniteWhittaker

section TorusGeneric

variable {A : Type*} [CommRing A]

private theorem map_diagOne {B : Type*} [CommRing B] (f : A →+* B) (a : Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagOne a) = diagOne (Units.map (f : A →* B) a) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change f.mapMatrix (diagOne a : Matrix (Fin 2) (Fin 2) A) i j = _
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

end TorusGeneric

section TorusComponents

variable {K : Type} [Field K] [NumberField K]

private theorem globalPoints_diagOne (α : Kˣ) :
    globalPoints (𝓞 K) K (diagOne α) = diagOne (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) :=
  map_diagOne _ α

private theorem archComponent_glArch_diagOne (w : InfinitePlace K) (a : (AdeleRing (𝓞 K) K)ˣ) :
    archComponent K w (glArch (𝓞 K) K (diagOne a)) = diagOne (archUnitAt w a) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [archComponent_apply, glArch_apply, diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [archUnitAt_val] <;> rfl

end TorusComponents

section ScalingLine
end ScalingLine

end FiniteWhittaker

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

open AutomorphicForm.SmoothCusp

variable {K : Type} [Field K] [NumberField K]

section WeakApproximation
end WeakApproximation

section Components

open scoped WithZero

private theorem componentMatrix_mul (v : HeightOneSpectrum (𝓞 K)) (a b : AdelicGL2 (𝓞 K) K) :
    componentMatrix v (a * b) = componentMatrix v a * componentMatrix v b := by
  simp only [componentMatrix, map_mul, Units.val_mul]

private theorem componentMatrix_one (v : HeightOneSpectrum (𝓞 K)) : componentMatrix v (1 : AdelicGL2 (𝓞 K) K) = 1 := by
  simp only [componentMatrix, map_one, Units.val_one]

end Components

section CentreAndTopology

open scoped WithZero

private theorem continuous_componentMatrix_apply (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2) :
    Continuous fun g : AdelicGL2 (𝓞 K) K => componentMatrix v g i j :=
  (Units.continuous_val.comp ((continuous_finComponent (R := 𝓞 K) (K := K) v).comp
    (continuous_glFin (R := 𝓞 K) (K := K)))).matrix_elem i j

private theorem setOf_v_le_mem_nhds {v : HeightOneSpectrum (𝓞 K)} {t y : v.adicCompletion K} (ht : t ≠ 0)
    (hy : Valued.v y ≤ Valued.v t) : {z : v.adicCompletion K | Valued.v z ≤ Valued.v t} ∈ nhds y :=
  Filter.mem_of_superset (ball_mem_nhds (𝓞 K) K v y t ht) fun z hz => by
    rw [Set.mem_setOf_eq, ← sub_add_cancel z y]
    exact Valuation.map_add_le _ (le_of_lt hz) hy

private theorem setOf_memZK0At_mem_nhds (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) {g : AdelicGL2 (𝓞 K) K}
    (hg : MemZK0At v m g) : {g' : AdelicGL2 (𝓞 K) K | MemZK0At v m g'} ∈ nhds g := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  have ht : componentMatrix v g 1 1 ≠ 0 := (Valuation.ne_zero_iff _).mp h1
  obtain ⟨t', ht'⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v
    (Valued.v (componentMatrix v g 1 1) * WithZero.exp (-(m : ℤ)))
  have ht'0 : t' ≠ 0 := fun h => by
    rw [h, map_zero] at ht'
    exact mul_ne_zero h1 WithZero.exp_ne_zero ht'.symm
  have n11 : {g' : AdelicGL2 (𝓞 K) K | Valued.v (componentMatrix v g' 1 1) = Valued.v (componentMatrix v g 1 1)}
      ∈ nhds g :=
    (continuous_componentMatrix_apply v 1 1).continuousAt.preimage_mem_nhds (Valued.locally_const h1)
  have n00 : {g' : AdelicGL2 (𝓞 K) K | Valued.v (componentMatrix v g' 0 0) = Valued.v (componentMatrix v g 1 1)}
      ∈ nhds g := by
    have h0 : Valued.v (componentMatrix v g 0 0) ≠ 0 := h2 ▸ h1
    have := (continuous_componentMatrix_apply v 0 0).continuousAt.preimage_mem_nhds (Valued.locally_const h0)
    rw [h2] at this
    exact this
  have n01 : {g' : AdelicGL2 (𝓞 K) K | Valued.v (componentMatrix v g' 0 1) ≤ Valued.v (componentMatrix v g 1 1)}
      ∈ nhds g :=
    (continuous_componentMatrix_apply v 0 1).continuousAt.preimage_mem_nhds (setOf_v_le_mem_nhds ht h3)
  have n10 : {g' : AdelicGL2 (𝓞 K) K | Valued.v (componentMatrix v g' 1 0) ≤ Valued.v t'} ∈ nhds g :=
    (continuous_componentMatrix_apply v 1 0).continuousAt.preimage_mem_nhds
      (setOf_v_le_mem_nhds ht'0 (ht'.symm ▸ h4))
  refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem n11 n00) (Filter.inter_mem n01 n10)) ?_
  rintro g' ⟨⟨e11, e00⟩, e01, e10⟩
  simp only [Set.mem_setOf_eq] at e11 e00 e01 e10 ⊢
  refine ⟨e11 ▸ h1, e00.trans e11.symm, e11.symm ▸ e01, ?_⟩
  rw [e11, ← ht']
  exact e10

private theorem isOpen_kZeroSet (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ↥S → ℕ) :
    IsOpen (kZeroSet S m) := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hS : kZeroSet S m = ⋂ v : ↥S, {g' | MemZK0At v.1 (m v) g'} := by
    ext g'
    simp only [kZeroSet, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hS, Filter.iInter_mem]
  exact fun v => setOf_memZK0At_mem_nhds v.1 (m v) (hg v)

end CentreAndTopology

section Extend
private def InvOn (D : Set (AdelicGL2 (𝓞 K) K)) (f : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ D → globalPoints (𝓞 K) K γ * g ∈ D →
    f (globalPoints (𝓞 K) K γ * g) = f g

variable {D : Set (AdelicGL2 (𝓞 K) K)}
  {hD : ∀ g : AdelicGL2 (𝓞 K) K, ∃ γ : GL (Fin 2) K, globalPoints (𝓞 K) K γ * g ∈ D}
  {f : AdelicGL2 (𝓞 K) K → ℂ}

private theorem InvOn.eq_of_mem (hf : InvOn D f) {γ₁ γ₂ : GL (Fin 2) K} {g : AdelicGL2 (𝓞 K) K}
    (h₁ : globalPoints (𝓞 K) K γ₁ * g ∈ D) (h₂ : globalPoints (𝓞 K) K γ₂ * g ∈ D) :
    f (globalPoints (𝓞 K) K γ₁ * g) = f (globalPoints (𝓞 K) K γ₂ * g) := by
  have key : globalPoints (𝓞 K) K (γ₁ * γ₂⁻¹) * (globalPoints (𝓞 K) K γ₂ * g) =
      globalPoints (𝓞 K) K γ₁ * g := by
    rw [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
  have h := hf (γ₁ * γ₂⁻¹) _ h₂ (by rw [key]; exact h₁)
  rw [key] at h
  exact h

private theorem extend_apply_of_mem (hf : InvOn D f) {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ D) :
    extendByRationalPoints D hD f g = f g := by
  have h1 : globalPoints (𝓞 K) K 1 * g ∈ D := by rwa [map_one, one_mul]
  have h := hf.eq_of_mem (Classical.choose_spec (hD g)) h1
  rw [map_one, one_mul] at h
  exact h

private theorem extend_mul_left (hf : InvOn D f) (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    extendByRationalPoints D hD f (globalPoints (𝓞 K) K γ * g) = extendByRationalPoints D hD f g := by
  unfold extendByRationalPoints
  have h₁ := Classical.choose_spec (hD (globalPoints (𝓞 K) K γ * g))
  have h₂ := Classical.choose_spec (hD g)
  rw [← mul_assoc, ← map_mul] at h₁ ⊢
  exact hf.eq_of_mem h₁ h₂

private theorem continuous_extend (hf : InvOn D f) (hDo : IsOpen D) (hfc : ContinuousOn f D) :
    Continuous (extendByRationalPoints D hD f) := by
  refine continuous_iff_continuousAt.mpr fun g₀ => ?_
  have h₀ : globalPoints (𝓞 K) K (Classical.choose (hD g₀)) * g₀ ∈ D := Classical.choose_spec (hD g₀)
  have hU : IsOpen {g : AdelicGL2 (𝓞 K) K | globalPoints (𝓞 K) K (Classical.choose (hD g₀)) * g ∈ D} :=
    hDo.preimage (continuous_const_mul _)
  have heq : Set.EqOn (extendByRationalPoints D hD f)
      (fun g => f (globalPoints (𝓞 K) K (Classical.choose (hD g₀)) * g))
      {g : AdelicGL2 (𝓞 K) K | globalPoints (𝓞 K) K (Classical.choose (hD g₀)) * g ∈ D} :=
    fun g hg => hf.eq_of_mem (Classical.choose_spec (hD g)) hg
  have hcont : ContinuousOn (fun g => f (globalPoints (𝓞 K) K (Classical.choose (hD g₀)) * g))
      {g : AdelicGL2 (𝓞 K) K | globalPoints (𝓞 K) K (Classical.choose (hD g₀)) * g ∈ D} :=
    hfc.comp (continuous_const_mul _).continuousOn fun _ hg => hg
  exact (hcont.congr heq).continuousAt (hU.mem_nhds h₀)

end Extend

section ArchCentre
end ArchCentre

section ArchDictionary
end ArchDictionary

section
section TorusModel
end TorusModel
end
section
section TorusModel
end TorusModel
end
section
section TorusModel
end TorusModel
end
section
section TorusModel
end TorusModel
end
section
section TorusModel
end TorusModel
end
section
section TorusModel
end TorusModel
end
section
section TorusClass
end TorusClass
end
section
section TorusClass
end TorusClass
end
section
section TorusClass
end TorusClass
end
section
section TorusClass
end TorusClass
end
section
section TorusClass
end TorusClass
end
section
section TorusClass
end TorusClass
end
section
section TorusClass
end TorusClass
end
section
section GaussFixedVector

open scoped WithZero
open UnramifiedWhittaker
private theorem charExt_one_add (v : HeightOneSpectrum (𝓞 K)) {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → IsOneMod K v m u → χ u = 1)
    (hm : 1 ≤ m) {s : v.adicCompletion K} (hs : Valued.v s ≤ WithZero.exp (-(m : ℤ))) :
    TateLocal.charExt χ (1 + s) = 1 := by
  have hs1 : Valued.v s < 1 :=
    hs.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have h1 : Valued.v (1 + s) = 1 := Valuation.map_one_add_of_lt _ hs1
  have hne : (1 + s) ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero] at h1; exact h1)
  have hu1 : Valued.v (((Units.mk0 (1 + s) hne : (v.adicCompletion K)ˣ) : v.adicCompletion K)) = 1 := by
    rw [Units.val_mk0]; exact h1
  have hu2 : IsOneMod K v m (Units.mk0 (1 + s) hne) := by
    show Valued.v (((Units.mk0 (1 + s) hne : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1) ≤
      WithZero.exp (-(m : ℤ))
    rw [Units.val_mk0, add_sub_cancel_left]; exact hs
  have key : χ (Units.mk0 (1 + s) hne) = 1 := hχ (Units.mk0 (1 + s) hne) hu1 hu2
  rw [TateLocal.charExt_of_ne_zero χ hne, key, Units.val_one]

end GaussFixedVector
end
section
section GaussFixedVector

open scoped WithZero
open UnramifiedWhittaker
private theorem charExt_mul_of_ne_zero (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    {a b : v.adicCompletion K} (ha : a ≠ 0) (hb : b ≠ 0) :
    TateLocal.charExt χ (a * b) = TateLocal.charExt χ a * TateLocal.charExt χ b := by
  rw [TateLocal.charExt_of_ne_zero χ (mul_ne_zero ha hb), Units.mk0_mul, map_mul, Units.val_mul,
    TateLocal.charExt_of_ne_zero χ ha, TateLocal.charExt_of_ne_zero χ hb]

end GaussFixedVector
end
section
section TestPoint

open UnramifiedWhittaker NumberField.InfinitePlace
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
private theorem realComponent_eq_map (w : InfinitePlace K) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) :
    realComponent w hw g = ((AdelicLevel.archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion).map (Completion.ringEquivRealOfIsReal hw) :=
  Matrix.ext fun _ _ => rfl

end TestPoint
end
section
section TestPoint

open UnramifiedWhittaker NumberField.InfinitePlace
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
private theorem complexComponent_eq_map (w : InfinitePlace K) (hw : w.IsComplex) (g : AdelicGL2 (𝓞 K) K) :
    complexComponent w hw g = ((AdelicLevel.archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion).map (Completion.ringEquivComplexOfIsComplex hw) :=
  Matrix.ext fun _ _ => rfl

end TestPoint
end
section
section SeriesCoefficient

open NumberField.InfinitePlace
private theorem det_realComponent_ne_zero (w : InfinitePlace K) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) :
    (realComponent w hw g).det ≠ 0 := by
  rw [realComponent_eq_map, ← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).mpr
    ((Matrix.isUnit_iff_isUnit_det _).mp (AdelicLevel.archComponent K w (glArch (𝓞 K) K g)).isUnit).ne_zero

end SeriesCoefficient
end
section
section SeriesCoefficient

open NumberField.InfinitePlace
private theorem det_complexComponent_ne_zero (w : InfinitePlace K) (hw : w.IsComplex) (g : AdelicGL2 (𝓞 K) K) :
    (complexComponent w hw g).det ≠ 0 := by
  rw [complexComponent_eq_map, ← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).mpr
    ((Matrix.isUnit_iff_isUnit_det _).mp (AdelicLevel.archComponent K w (glArch (𝓞 K) K g)).isUnit).ne_zero

end SeriesCoefficient
end
section
section GaussCoefficient
open scoped Classical
open scoped WithZero
p2m_open "LanglandsTunnell.TateLocal NumberField.StandardAddChar NumberField.InfinitePlace AutomorphicForm.GaussTwist"
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
private noncomputable def seriesTerm (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) (α : Kˣ) : ℂ :=
  d.a α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)
    * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g)

end GaussCoefficient
end
section
section GaussCoefficient
open scoped Classical
open scoped WithZero
p2m_open "LanglandsTunnell.TateLocal NumberField.StandardAddChar NumberField.InfinitePlace AutomorphicForm.GaussTwist"
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
private theorem jlSeries'_eq_tsum_seriesTerm (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) :
    jlSeries' d archR archC dR dC dF g = ∑' α : Kˣ, seriesTerm d archR archC dR dC dF g α := by
  simp only [jlSeries', whittakerSeries, seriesTerm]

end GaussCoefficient
end
end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

open MeasureTheory Topology

section TorusInterchange
end TorusInterchange

section TorusMeasure
end TorusMeasure

section LatticeWeight

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
private noncomputable def archLatticeWeight (k N : ℕ) (ξ : K) : ℝ :=
  (max 1 ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ^ k
    * (∏ w : {w : InfinitePlace K // w.IsReal}, (1 + |(NumberField.mixedEmbedding K ξ).1 w|) ^ (-(N : ℝ)))
    * ∏ w : {w : InfinitePlace K // w.IsComplex}, (1 + ‖(NumberField.mixedEmbedding K ξ).2 w‖) ^ (-(2 * N : ℝ))

private def integralAfter (δ : 𝓞 K) : Set Kˣ :=
  {α | ∃ β : 𝓞 K, (β : K) = (δ : K) * (α : K)}

private theorem mem_spanSingleton_inv_of_mem_integralAfter {δ : 𝓞 K} (hδ : δ ≠ 0) {α : Kˣ}
    (hα : α ∈ integralAfter δ) :
    (α : K) ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((δ : K)⁻¹) := by
  obtain ⟨β, hβ⟩ := hα
  have hδK : (δ : K) ≠ 0 := by exact_mod_cast hδ
  refine (FractionalIdeal.mem_spanSingleton (S := nonZeroDivisors (𝓞 K))).2 ⟨β, ?_⟩
  rw [Algebra.smul_def, ← NumberField.RingOfIntegers.coe_eq_algebraMap, hβ, mul_comm ((δ : K)) _, mul_assoc,
    mul_inv_cancel₀ hδK, mul_one]

private theorem exists_summable_archLatticeWeight_subtype (δ : 𝓞 K) (k : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Summable fun ξ : {ξ : K // ξ ≠ 0 ∧ ξ ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((δ : K)⁻¹)} =>
        archLatticeWeight k N ξ.1 := by
  obtain ⟨N₀, hN₀⟩ := NumberField.mixedEmbedding.exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg K
    (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((δ : K)⁻¹)) k 0 1 one_pos
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨C, hC⟩ := hN₀ N hN
  refine (hC 1 le_rfl).1.congr fun ξ => ?_
  simp only [archLatticeWeight, one_mul]

private theorem exists_summable_archLatticeWeight (δ : 𝓞 K) (hδ : δ ≠ 0) (k : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Summable fun α : Kˣ => (integralAfter δ).indicator (fun α : Kˣ => archLatticeWeight k N (α : K)) α := by
  obtain ⟨N₀, hN₀⟩ := exists_summable_archLatticeWeight_subtype δ k
  refine ⟨N₀, fun N hN => ?_⟩
  rw [← summable_subtype_iff_indicator]
  have hf : Function.Injective fun α : {α : Kˣ // α ∈ integralAfter δ} =>
      (⟨(α.1 : K), α.1.ne_zero, mem_spanSingleton_inv_of_mem_integralAfter hδ α.2⟩ :
        {ξ : K // ξ ≠ 0 ∧ ξ ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((δ : K)⁻¹)}) :=
    fun a b hab => Subtype.ext (Units.ext (congrArg Subtype.val hab))
  have h := (hN₀ N hN).comp_injective hf
  exact h

end LatticeWeight

section Absorption

variable {K : Type} [Field K] [NumberField K]

private theorem prod_one_add_rpow_le_archLatticeWeight (k N : ℕ) (ξ : K) :
    (max 1 ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ^ k * ∏ w : InfinitePlace K, (1 + w ξ) ^ (-(2 * N : ℝ))
      ≤ archLatticeWeight k N ξ := by
  classical
  classical
  unfold archLatticeWeight
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsplit : ∏ w : InfinitePlace K, (1 + w ξ) ^ (-(2 * N : ℝ))
      = (∏ w : {w : InfinitePlace K // w.IsReal}, (1 + w.1 ξ) ^ (-(2 * N : ℝ)))
        * ∏ w : {w : InfinitePlace K // w.IsComplex}, (1 + w.1 ξ) ^ (-(2 * N : ℝ)) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K => w.IsReal)]
    congr 1
    exact Fintype.prod_equiv (Equiv.subtypeEquivRight fun w => (InfinitePlace.not_isReal_iff_isComplex)) _ _
      fun w => rfl
  rw [hsplit]
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · refine Finset.prod_le_prod ?_ ?_
    · intro w _
      exact (Real.rpow_pos_of_pos (by linarith [apply_nonneg w.1 ξ]) _).le
    intro w _
    rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isReal, ← Real.norm_eq_abs,
      InfinitePlace.norm_embedding_of_isReal w.2 ξ]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [apply_nonneg w.1 ξ]) (by linarith)
  · refine le_of_eq (Finset.prod_congr rfl fun w _ => ?_)
    rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex, InfinitePlace.norm_embedding_eq]

private theorem one_le_abs_norm_of_ne_zero {β : 𝓞 K} (hβ : β ≠ 0) : (1 : ℝ) ≤ |Algebra.norm ℚ (β : K)| := by
  have h : Algebra.norm ℤ β ≠ 0 := (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hβ
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ β| := Int.one_le_abs h
  rw [← Algebra.coe_norm_int β]
  exact_mod_cast h1

private theorem exists_le_archLatticeWeight (δ : 𝓞 K) (hδ : δ ≠ 0) {κ σ : ℝ} (hκ : 0 ≤ κ) (hσ : 0 ≤ σ)
    {k : ℕ} (hk : κ ≤ k) (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ α : Kˣ, α ∈ integralAfter δ →
      |Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
          * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ))
        ≤ C * archLatticeWeight k N (α : K) := by
  classical
  have hδ1 : (1 : ℝ) ≤ |Algebra.norm ℚ (δ : K)| := one_le_abs_norm_of_ne_zero hδ
  refine ⟨2 * N + ⌈σ⌉₊, |Algebra.norm ℚ (δ : K)| ^ (κ + σ), by positivity, fun α hα => ?_⟩
  obtain ⟨β, hβ⟩ := hα
  have hβ0 : β ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hβ
    exact mul_ne_zero (by exact_mod_cast hδ) (α.ne_zero) hβ.symm
  have hαpos : ∀ w : InfinitePlace K, 0 < w (α : K) := fun w => InfinitePlace.pos_iff.mpr α.ne_zero
  have hW := prod_one_add_rpow_le_archLatticeWeight (K := K) k N (α : K)
  have hβnorm : (1 : ℝ) ≤ |Algebra.norm ℚ (β : K)| := one_le_abs_norm_of_ne_zero hβ0
  rw [hβ, map_mul, abs_mul, Rat.cast_mul] at hβnorm
  have hmult : ∏ w : InfinitePlace K, w (α : K) ^ InfinitePlace.mult w
      ≤ (∏ w : InfinitePlace K, w (α : K)) * ∏ w : InfinitePlace K, (1 + w (α : K)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod ?_ ?_
    · intro w _
      exact pow_nonneg (hαpos w).le _
    intro w _
    unfold InfinitePlace.mult
    split_ifs <;> simp only [pow_one, pow_two] <;> nlinarith [hαpos w]
  rw [InfinitePlace.prod_eq_abs_norm] at hmult
  have hmult' : ((|Algebra.norm ℚ (α : K)| : ℚ) : ℝ)
      ≤ (∏ w : InfinitePlace K, w (α : K)) * ∏ w : InfinitePlace K, (1 + w (α : K)) := by
    exact_mod_cast hmult
  have hδα : ((|Algebra.norm ℚ ((δ : K) * (α : K))| : ℚ) : ℝ)
      = ((|Algebra.norm ℚ (δ : K)| : ℚ) : ℝ) * ((|Algebra.norm ℚ (α : K)| : ℚ) : ℝ) := by
    rw [map_mul, abs_mul, Rat.cast_mul]
  rw [hδα]
  set nδ : ℝ := ((|Algebra.norm ℚ (δ : K)| : ℚ) : ℝ) with hnδ
  set nα : ℝ := ((|Algebra.norm ℚ (α : K)| : ℚ) : ℝ) with hnα
  set P : ℝ := ∏ w : InfinitePlace K, w (α : K) with hP
  set Q : ℝ := ∏ w : InfinitePlace K, (1 + w (α : K)) with hQ
  have hδpos : 0 < nδ := by linarith
  have hα0 : 0 ≤ nα := by rw [hnα]; exact Rat.cast_nonneg.mpr (abs_nonneg _)
  have hPpos : 0 < P := Finset.prod_pos fun w _ => hαpos w
  have hQpos : 0 < Q := Finset.prod_pos fun w _ => by linarith [hαpos w]
  have hN1 : (nδ * nα) ^ κ ≤ nδ ^ κ * (max 1 nα) ^ k := by
    rw [Real.mul_rpow hδpos.le hα0]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hδpos.le _)
    calc nα ^ κ ≤ (max 1 nα) ^ κ := Real.rpow_le_rpow hα0 (le_max_right _ _) hκ
      _ ≤ (max 1 nα) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) hk
      _ = (max 1 nα) ^ k := Real.rpow_natCast _ _
  have hPinv : P⁻¹ ≤ nδ * Q := by
    rw [inv_le_iff_one_le_mul₀ hPpos]
    calc (1 : ℝ) ≤ nδ * nα := hβnorm
      _ ≤ nδ * (P * Q) := mul_le_mul_of_nonneg_left hmult' hδpos.le
      _ = nδ * Q * P := by ring
  have hN2 : ∏ w : InfinitePlace K, (w (α : K)) ^ (-σ) ≤ nδ ^ σ * Q ^ σ := by
    rw [Real.finsetProd_rpow Finset.univ (fun w : InfinitePlace K => w (α : K)) (fun w _ => (hαpos w).le) (-σ),
      ← hP, Real.rpow_neg hPpos.le, ← Real.inv_rpow hPpos.le, ← Real.mul_rpow hδpos.le hQpos.le]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hPpos.le) hPinv hσ
  have hN3 : Q ^ σ * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-((2 * N + ⌈σ⌉₊ : ℕ) : ℝ))
      ≤ ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(2 * N : ℝ)) := by
    have hQ1 : ∀ w : InfinitePlace K, (1 : ℝ) ≤ 1 + w (α : K) := fun w => by linarith [hαpos w]
    have hsplit : ∀ w : InfinitePlace K, (1 + w (α : K)) ^ (-((2 * N + ⌈σ⌉₊ : ℕ) : ℝ))
        = (1 + w (α : K)) ^ (-(2 * N : ℝ)) * ((1 + w (α : K)) ^ (-(⌈σ⌉₊ : ℝ))) := fun w => by
      rw [← Real.rpow_add (by linarith [hαpos w])]
      congr 1
      push_cast
      ring
    simp only [hsplit, Finset.prod_mul_distrib]
    rw [Real.finsetProd_rpow Finset.univ (fun w : InfinitePlace K => 1 + w (α : K)) (fun w _ => by linarith [hαpos w])
      (-(⌈σ⌉₊ : ℝ)), ← hQ]
    set A : ℝ := ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(2 * N : ℝ)) with hA
    have hA0 : 0 ≤ A := Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (by linarith [hαpos w]) _).le
    have hQ1' : (1 : ℝ) ≤ Q :=
      calc (1 : ℝ) = ∏ _w : InfinitePlace K, (1 : ℝ) := Finset.prod_const_one.symm
        _ ≤ Q := Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ => hQ1 w
    have hQQ : Q ^ (-(⌈σ⌉₊ : ℝ)) * Q ^ σ ≤ 1 := by
      rw [← Real.rpow_add hQpos]
      calc Q ^ (-(⌈σ⌉₊ : ℝ) + σ) ≤ Q ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hQ1' (by linarith [Nat.le_ceil σ])
        _ = 1 := Real.rpow_zero Q
    calc Q ^ σ * (A * Q ^ (-(⌈σ⌉₊ : ℝ))) = A * (Q ^ (-(⌈σ⌉₊ : ℝ)) * Q ^ σ) := by ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hQQ hA0
      _ = A := mul_one A
  have hδκσ : nδ ^ (κ + σ) = nδ ^ κ * nδ ^ σ := Real.rpow_add hδpos _ _
  have hPσ : 0 ≤ ∏ w : InfinitePlace K, (w (α : K)) ^ (-σ) :=
    Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (hαpos w) _).le
  have hM0 : 0 ≤ ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-((2 * N + ⌈σ⌉₊ : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (by linarith [hαpos w]) _).le
  have hQσ : 0 ≤ Q ^ σ := Real.rpow_nonneg hQpos.le _
  rw [hδκσ]
  calc (nδ * nα) ^ κ * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
        * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-((2 * N + ⌈σ⌉₊ : ℕ) : ℝ))
      ≤ nδ ^ κ * (max 1 nα) ^ k * (nδ ^ σ * Q ^ σ)
          * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-((2 * N + ⌈σ⌉₊ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hN1 hN2 hPσ (by positivity)) hM0
    _ = nδ ^ κ * nδ ^ σ * ((max 1 nα) ^ k
          * (Q ^ σ * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-((2 * N + ⌈σ⌉₊ : ℕ) : ℝ)))) := by ring
    _ ≤ nδ ^ κ * nδ ^ σ * ((max 1 nα) ^ k * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(2 * N : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN3 (by positivity)) (by positivity)
    _ ≤ nδ ^ κ * nδ ^ σ * archLatticeWeight k N (α : K) := mul_le_mul_of_nonneg_left hW (by positivity)

end Absorption

section LocalMajorant

variable {K : Type} [Field K] [NumberField K]

private theorem archLatticeWeight_nonneg (k N : ℕ) (ξ : K) : 0 ≤ archLatticeWeight k N ξ := by
  classical
  unfold archLatticeWeight
  refine mul_nonneg (mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) ?_) ?_
  · exact Finset.prod_nonneg fun w _ => Real.rpow_nonneg (by positivity) _
  · exact Finset.prod_nonneg fun w _ => Real.rpow_nonneg (by positivity) _

end LocalMajorant

section TermContinuity

variable {K : Type} [Field K] [NumberField K]

private theorem exists_nhds_forall_wf_mul_eq {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    (dF : FinWhittakerDatum K S Pi) (g₀ : AdelicGL2 (𝓞 K) K) :
    ∃ V ∈ 𝓝 g₀, ∀ (x : AdelicGL2 (𝓞 K) K), ∀ g ∈ V, dF.Wf (x * g) = dF.Wf (x * g₀) := by
  refine ⟨(fun g : AdelicGL2 (𝓞 K) K => g₀⁻¹ * g) ⁻¹' (levelOne (𝓞 K) K ⊤ : Set (AdelicGL2 (𝓞 K) K)), ?_, ?_⟩
  · refine ((isOpen_levelOne (𝓞 K) K top_ne_bot).preimage (continuous_const_mul _)).mem_nhds ?_
    show g₀⁻¹ * g₀ ∈ levelOne (𝓞 K) K ⊤
    rw [inv_mul_cancel]
    exact one_mem _
  intro x g hg
  have hkmem : g₀⁻¹ * g ∈ levelOne (𝓞 K) K ⊤ := hg
  have hgk : g = g₀ * (g₀⁻¹ * g) := (mul_inv_cancel_left g₀ g).symm
  rw [hgk, ← mul_assoc, dF.finite_dependent (x * g₀ * (g₀⁻¹ * g))
    (x * g₀ * AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K (g₀⁻¹ * g)))
    (by simp only [map_mul, AdelicDock.glFin_finEmbed])]
  refine FiniteWhittaker.wf_mul_of_mem_integral dF _ (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [AdelicDock.finEmbed_mem_levelOne_iff]
    exact hkmem
  · exact (mem_finiteAdelicGL2Subgroup_iff _ _).mpr (AdelicDock.glArch_finEmbed _ _ _)

end TermContinuity

section FiniteTransport

variable {K : Type} [Field K] [NumberField K]

open LanglandsTunnell.TateLocal NumberField.StandardAddChar

private theorem exists_nhds_wf_bound {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    (dF : FinWhittakerDatum K S Pi)
    (hgrow : ∃ κ : ℝ, ∀ v ∉ S,
      ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ)
    (coef : Kˣ → ℂ)
    (hfloor : ∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) → coef α = 0)
    (g₀ : AdelicGL2 (𝓞 K) K) :
    ∃ δ : 𝓞 K, δ ≠ 0 ∧ ∃ V ∈ 𝓝 g₀, ∃ C κ : ℝ, 0 ≤ κ ∧ ∀ g ∈ V, ∀ α : Kˣ,
      coef α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g) ≠ 0 →
        α ∈ integralAfter δ ∧
          ‖dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g)‖ ≤ C * |Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ := by
  obtain ⟨δ, hδ, C, κ, hκ, hrow⟩ := FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le K S Pi hgrow dF g₀
    (fun v => addCharLevel (psiLocal K v.1))
  obtain ⟨V, hV, hVeq⟩ := exists_nhds_forall_wf_mul_eq dF g₀
  refine ⟨δ, hδ, V, hV, C, κ, hκ, fun g hg α hne => ?_⟩
  have hcoef : coef α ≠ 0 := left_ne_zero_of_mul hne
  have hW : dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g) ≠ 0 := right_ne_zero_of_mul hne
  have htrans : dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g) = dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g₀) :=
    hVeq _ g hg
  have hval : ∀ v : ↥S,
      Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
        ≤ WithZero.exp (addCharLevel (psiLocal K v.1)) := by
    by_contra h
    exact hcoef (hfloor α (not_forall.mp h))
  rw [htrans] at hW ⊢
  obtain ⟨β, hβ, hbound⟩ := hrow α hval hW
  refine ⟨⟨β, hβ⟩, ?_⟩
  rwa [hβ] at hbound

end FiniteTransport

section Assembly
end Assembly

section GrowthExponent

variable {K : Type} [Field K] [NumberField K]

private theorem two_le_absNorm_real (v : HeightOneSpectrum (𝓞 K)) : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem norm_b_eq_absNorm (Pi : HeckeEigensystem K ℂ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) : ‖Pi.b v‖ = (Ideal.absNorm v.asIdeal : ℝ) := by
  have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith [two_le_absNorm_real (K := K) v]
  obtain ⟨-, -, hωu⟩ := id hω
  have hunit : ‖((ω (uniformizerIdele K v) : ℂˣ) : ℂ)‖ = 1 := hωu _
  rw [hωb v hv, HeckeEigensystem.twist_b, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hN _), ← Real.rpow_natCast, ← Real.rpow_mul hN.le] at hunit
  have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ) * ((2 : ℕ) : ℝ)) = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    rw [show -(1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  rw [hpow] at hunit
  field_simp at hunit
  linarith [hunit, norm_nonneg (Pi.b v)]

private theorem exists_growth_exponent (Pi : HeckeEigensystem K ℂ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC) :
    ∃ κ : ℝ, ∀ v ∉ S, ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ := by
  classical
  obtain ⟨μ, hμ, hunr⟩ := exists_isJLTwist K S epsS d.m d.epsS_level
  obtain ⟨⟨-, hcont, hunit⟩, -⟩ := id hμ
  obtain ⟨uR, aR, uC, kC, hcR, hcC⟩ := exists_archParams_of_continuous K μ hcont
  obtain ⟨R, hR⟩ := hnice
  have hD := hR μ hμ uR aR uC kC hcR hcC
  dsimp only at hD
  obtain ⟨-, hconv, -⟩ := hD
  set D := twistedDatum K (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
    S archR archC μ uR aR uC kC with hDdef
  have h2 := (hconv 2 (by norm_num [hDdef, twistedDatum])).1
  have hcof := Filter.eventually_cofinite.1 ((Metric.tendsto_nhds.1 h2.tendsto_cofinite_zero) 1 one_pos)
  set F₁ := hcof.toFinset with hF₁
  set B : ℝ := 1 + ∑ i ∈ F₁, ‖Pi.a i.1‖ with hB
  have hBpos : 0 < B := by
    have : 0 ≤ ∑ i ∈ F₁, ‖Pi.a i.1‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  refine ⟨max 4 (Real.logb 2 B), fun v hv => ?_⟩
  have hN2 := two_le_absNorm_real (K := K) v
  have hNpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  have hNnat : 0 < Ideal.absNorm v.asIdeal := by exact_mod_cast hNpos
  have hκ0 : (0 : ℝ) ≤ max 4 (Real.logb 2 B) := le_trans (by norm_num) (le_max_left _ _)
  have hN4 : (Ideal.absNorm v.asIdeal : ℝ) ^ (4 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ max 4 (Real.logb 2 B) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hNB : B ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ max 4 (Real.logb 2 B) := by
    calc B = (2 : ℝ) ^ Real.logb 2 B := (Real.rpow_logb (by norm_num) (by norm_num) hBpos).symm
      _ ≤ (2 : ℝ) ^ max 4 (Real.logb 2 B) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_max_right _ _)
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ max 4 (Real.logb 2 B) := Real.rpow_le_rpow (by norm_num) hN2 hκ0
  have hb : ‖Pi.b v‖ = (Ideal.absNorm v.asIdeal : ℝ) := norm_b_eq_absNorm Pi S ω hω hωb hv
  refine ⟨?_, ?_⟩
  swap
  · rw [hb]
    calc (Ideal.absNorm v.asIdeal : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ ≤ _ := hN4
  by_cases hmem : (⟨v, hv⟩ : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) ∈ F₁
  ·
    have hle : ‖Pi.a v‖ ≤ B := by
      have := Finset.single_le_sum (f := fun i : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} => ‖Pi.a i.1‖)
        (fun i _ => norm_nonneg _) hmem
      simp only at this
      linarith
    exact hle.trans hNB
  ·
    have hnear : dist ‖(D.euler ⟨v, hv⟩).eval ((D.norm ⟨v, hv⟩ : ℂ) ^ (-(2 : ℂ))) - 1‖ 0 < 1 := by
      have := hmem
      rw [hF₁, Set.Finite.mem_toFinset] at this
      simpa using this
    rw [Real.dist_0_eq_abs, abs_norm, hDdef] at hnear
    simp only [twistedDatum] at hnear
    rw [if_pos (hunr v hv)] at hnear
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow, HeckeEigensystem.twist_a, HeckeEigensystem.twist_b] at hnear
    set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hNdef
    set c : ℂ := ((N ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hc
    set m : ℂ := ((μ (uniformizerIdele K v) : ℂˣ) : ℂ) with hm
    set m₂ : ℂ := (((μ (uniformizerIdele K v)) ^ 2 : ℂˣ) : ℂ) with hm₂
    set x : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)) with hx
    have hxn : ‖x‖ = N ^ (-(2 : ℝ)) := by
      rw [hx, Complex.norm_natCast_cpow_of_pos hNnat, hNdef]
      simp
    have hμ1 : ‖m‖ = 1 := hunit _
    have hμ2 : ‖m₂‖ = 1 := by
      rw [hm₂, Units.val_pow_eq_pow_val, norm_pow]
      exact by rw [← hm, hμ1, one_pow]
    have hbn : ‖c ^ 2 * Pi.b v‖ = 1 := by
      obtain ⟨-, -, hωu⟩ := id hω
      have := hωu (uniformizerIdele K v)
      rwa [hωb v hv, HeckeEigensystem.twist_b] at this
    have hcn : ‖c‖ = N ^ (-(1 / 2 : ℝ)) := by
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hNpos _)]
    have hkey : ‖c‖ * ‖Pi.a v‖ * ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by
      have hsplit : m * (c * Pi.a v) * x
          = -((1 - m * (c * Pi.a v) * x + m₂ * (c ^ 2 * Pi.b v) * x ^ 2) - 1) + m₂ * (c ^ 2 * Pi.b v) * x ^ 2 := by
        ring
      have hL : ‖m * (c * Pi.a v) * x‖ = ‖c‖ * ‖Pi.a v‖ * ‖x‖ := by
        rw [norm_mul, norm_mul, norm_mul, hμ1, one_mul]
      have hR' : ‖m₂ * (c ^ 2 * Pi.b v) * x ^ 2‖ = ‖x‖ ^ 2 := by
        rw [norm_mul, norm_mul, hμ2, hbn, norm_pow, one_mul, one_mul]
      rw [← hL, hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, hR']
      exact add_le_add hnear.le le_rfl
    rw [hcn, hxn] at hkey
    have hx4 : (N ^ (-(2 : ℝ))) ^ 2 ≤ 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hprod : N ^ (-(1 / 2 : ℝ)) * N ^ (-(2 : ℝ)) = (N ^ ((5 : ℝ) / 2))⁻¹ := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_neg hNpos.le]; norm_num
    have hfive : N ^ ((5 : ℝ) / 2) * 2 ≤ N ^ (4 : ℝ) := by
      calc N ^ ((5 : ℝ) / 2) * 2 ≤ N ^ ((5 : ℝ) / 2) * N ^ (1 : ℝ) := by
            rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hN2 (Real.rpow_pos_of_pos hNpos _).le
        _ = N ^ ((7 : ℝ) / 2) := by rw [← Real.rpow_add hNpos]; norm_num
        _ ≤ N ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hpos52 : 0 < N ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hNpos _
    have ha : ‖Pi.a v‖ ≤ N ^ ((5 : ℝ) / 2) * 2 := by
      have h1 : ‖Pi.a v‖ * (N ^ ((5 : ℝ) / 2))⁻¹ ≤ 2 := by
        have := hkey
        rw [mul_comm _ ‖Pi.a v‖, mul_assoc, hprod] at this
        linarith
      rwa [← div_eq_mul_inv, div_le_iff₀ hpos52, mul_comm] at h1
    exact ha.trans (hfive.trans hN4)

end GrowthExponent

section EpsBound

variable {K : Type} [Field K] [NumberField K] {S : Finset (HeightOneSpectrum (𝓞 K))}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

private theorem norm_localChar_eq_one {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 K) K μ)
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) : ‖((localChar μ v u : ℂˣ) : ℂ)‖ = 1 :=
  hμ _

private theorem norm_epsS_eq_one_of_valuation_eq_one (d : JLData K S epsS ω) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ S) (u : (v.adicCompletion K)ˣ) (hu : Valued.v (u : v.adicCompletion K) = 1) :
    ‖((epsS v u : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨μ, hμ, -⟩ := exists_isJLTwist K S epsS d.m d.epsS_level
  obtain ⟨⟨-, -, hunit⟩, hS⟩ := hμ
  have h := congrArg (fun x : ℂˣ => ‖(x : ℂ)‖) (hS v hv u hu)
  simp only [Units.val_mul, norm_mul, Units.val_one, norm_one] at h
  rwa [norm_localChar_eq_one hunit, one_mul] at h

private theorem norm_epsChar_le_one (d : JLData K S epsS ω) (hω : IsAdmissibleTwist K ω) (g : AdelicGL2 (𝓞 K) K) :
    ‖d.epsChar g‖ ≤ 1 := by
  obtain ⟨-, -, hωu⟩ := hω
  unfold JLData.epsChar
  split_ifs with hg
  · rw [norm_prod]
    refine Finset.prod_le_one (fun v _ => norm_nonneg _) (fun v _ => ?_)
    obtain ⟨hd, had, -, -⟩ := hg v
    have hd0 : componentMatrix v.1 g 1 1 ≠ 0 := fun h => hd (by rw [h, map_zero])
    have ha0 : componentMatrix v.1 g 0 0 ≠ 0 := fun h => hd (by rw [← had, h, map_zero])
    have hx0 : componentMatrix v.1 g 0 0 / componentMatrix v.1 g 1 1 ≠ 0 := div_ne_zero ha0 hd0
    rw [norm_mul, TateLocal.charExt_of_ne_zero _ hd0, TateLocal.charExt_of_ne_zero _ hx0,
      norm_localChar_eq_one hωu, one_mul]
    refine le_of_eq (norm_epsS_eq_one_of_valuation_eq_one d v.2 _ ?_)
    rw [Units.val_mk0, map_div₀, had, div_self hd]
  · simp

end EpsBound

end LanglandsTunnell.Converse.CuspSynthesis

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section ArchContinuity

open NumberField.InfinitePlace
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

private theorem continuous_realComponent (w : InfinitePlace K) (hw : w.IsReal) : Continuous (realComponent w hw) := by
  have hc : Continuous fun g : AdelicGL2 (𝓞 K) K =>
      ((AdelicLevel.archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) :=
    Units.continuous_val.comp
      ((AdelicLevel.continuous_archComponent K w).comp (AdelicLevel.continuous_glArch (𝓞 K) K))
  have he : Continuous (Completion.ringEquivRealOfIsReal hw) :=
    (Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
  have hfun : realComponent w hw = fun g : AdelicGL2 (𝓞 K) K =>
      (((AdelicLevel.archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).map (Completion.ringEquivRealOfIsReal hw)) :=
    funext (realComponent_eq_map w hw)
  rw [hfun]
  exact hc.matrix_map he

private theorem continuous_complexComponent (w : InfinitePlace K) (hw : w.IsComplex) :
    Continuous (complexComponent w hw) := by
  have hc : Continuous fun g : AdelicGL2 (𝓞 K) K =>
      ((AdelicLevel.archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) :=
    Units.continuous_val.comp
      ((AdelicLevel.continuous_archComponent K w).comp (AdelicLevel.continuous_glArch (𝓞 K) K))
  have he : Continuous (Completion.ringEquivComplexOfIsComplex hw) :=
    (Completion.isometry_extensionEmbedding (v := w)).continuous
  have hfun : complexComponent w hw = fun g : AdelicGL2 (𝓞 K) K =>
      (((AdelicLevel.archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).map (Completion.ringEquivComplexOfIsComplex hw)) :=
    funext (complexComponent_eq_map w hw)
  rw [hfun]
  exact hc.matrix_map he

private theorem isOpen_glSetR : IsOpen ArchR.glSet := by
  have h : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => M.det :=
    (continuous_id : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => M).matrix_det
  exact isOpen_ne_fun h continuous_const

private theorem isOpen_glSetC : IsOpen ArchC.glSet := by
  have h : Continuous fun M : Matrix (Fin 2) (Fin 2) ℂ => M.det :=
    (continuous_id : Continuous fun M : Matrix (Fin 2) (Fin 2) ℂ => M).matrix_det
  exact isOpen_ne_fun h continuous_const

end ArchContinuity

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

section ArchProfileBounds

open Matrix

namespace ArchIwasawa

section Generic

variable {A : Type*} [CommRing A]

private theorem diagOne_mul_unip_mul (t x : A) (M : Matrix (Fin 2) (Fin 2) A) :
    !![t, 0; 0, 1] * (!![1, x; 0, 1] * M) = !![1, t * x; 0, 1] * (!![t, 0; 0, 1] * M) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagOne_mul_smul (t r : A) (M : Matrix (Fin 2) (Fin 2) A) :
    !![t, 0; 0, 1] * (r • M) = r • (!![t, 0; 0, 1] * M) :=
  Matrix.mul_smul _ _ _

private theorem diagOne_mul_diagOne_mul (t y : A) (k : Matrix (Fin 2) (Fin 2) A) :
    !![t, 0; 0, 1] * (!![y, 0; 0, 1] * k) = !![t * y, 0; 0, 1] * k := by
  rw [← Matrix.mul_assoc]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagOne_mul_iwasawa (t x r y : A) (k : Matrix (Fin 2) (Fin 2) A) :
    !![t, 0; 0, 1] * (!![1, x; 0, 1] * (r • (!![y, 0; 0, 1] * k)))
      = !![1, t * x; 0, 1] * (r • (!![t * y, 0; 0, 1] * k)) := by
  rw [diagOne_mul_unip_mul, diagOne_mul_smul, diagOne_mul_diagOne_mul]

end Generic

namespace Real

variable (g : Matrix (Fin 2) (Fin 2) ℝ)

private noncomputable def _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.rowNorm : ℝ := √(g 1 0 ^ 2 + g 1 1 ^ 2)

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "rowNorm"
private noncomputable def kOf : Matrix (Fin 2) (Fin 2) ℝ := (rowNorm g)⁻¹ • !![g 1 1, -g 1 0; g 1 0, g 1 1]

private noncomputable def _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.yOf : ℝ := g.det / rowNorm g ^ 2

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "yOf"
private noncomputable def xOf : ℝ := (g 0 0 * g 1 0 + g 0 1 * g 1 1) / rowNorm g ^ 2

variable {g}

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.rowNorm_sq : rowNorm g ^ 2 = g 1 0 ^ 2 + g 1 1 ^ 2 :=
  Real.sq_sqrt (by positivity)

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "rowNorm_sq"
private theorem rowNorm_nonneg : 0 ≤ rowNorm g := Real.sqrt_nonneg _

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.rowNorm_pos (hg : g.det ≠ 0) : 0 < rowNorm g := by
  apply Real.sqrt_pos.mpr
  by_contra h
  have h0 : g 1 0 = 0 ∧ g 1 1 = 0 := by
    constructor <;> nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
  apply hg
  rw [Matrix.det_fin_two, h0.1, h0.2]
  ring

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "rowNorm_pos"
private theorem rowNorm_ne_zero (hg : g.det ≠ 0) : rowNorm g ≠ 0 := (rowNorm_pos hg).ne'

private theorem kOf_mem (hg : g.det ≠ 0) : kOf g ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  have hr := rowNorm_ne_zero hg
  have hsq := rowNorm_sq (g := g)
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kOf, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> (try rw [hsq]) <;> ring

private theorem eq_unip_mul (hg : g.det ≠ 0) :
    g = !![1, xOf g; 0, 1] * (rowNorm g • (!![yOf g, 0; 0, 1] * kOf g)) := by
  have hr := rowNorm_ne_zero hg
  have hsq := rowNorm_sq (g := g)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kOf, xOf, yOf, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;>
    field_simp <;> (try rw [hsq]) <;> ring

private theorem abs_yOf : |yOf g| = |g.det| / rowNorm g ^ 2 := by
  rw [yOf, abs_div, abs_pow, abs_of_nonneg rowNorm_nonneg]

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.yOf_ne_zero (hg : g.det ≠ 0) : yOf g ≠ 0 :=
  div_ne_zero hg (pow_ne_zero 2 (rowNorm_ne_zero hg))

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "yOf_ne_zero"
private theorem diagOne_mul_eq (hg : g.det ≠ 0) (t : ℝ) :
    !![t, 0; 0, 1] * g = !![1, t * xOf g; 0, 1] * (rowNorm g • (!![t * yOf g, 0; 0, 1] * kOf g)) := by
  conv_lhs => rw [eq_unip_mul hg]
  exact diagOne_mul_iwasawa t (xOf g) (rowNorm g) (yOf g) (kOf g)

end Real

namespace Complex

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

private noncomputable def _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.rowNorm : ℝ := √(‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2)

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "rowNorm"
private noncomputable def kOf : Matrix (Fin 2) (Fin 2) ℂ :=
  ((rowNorm g : ℝ) : ℂ)⁻¹ • !![(starRingEnd ℂ) (g 1 1), -(starRingEnd ℂ) (g 1 0); g 1 0, g 1 1]

private noncomputable def _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.yOf : ℂ := g.det / ((rowNorm g : ℝ) : ℂ) ^ 2

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "yOf"
private noncomputable def xOf : ℂ :=
  (g 0 0 * (starRingEnd ℂ) (g 1 0) + g 0 1 * (starRingEnd ℂ) (g 1 1)) / ((rowNorm g : ℝ) : ℂ) ^ 2

variable {g}

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.rowNorm_sq : rowNorm g ^ 2 = ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 :=
  _root_.Real.sq_sqrt (by positivity)

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "rowNorm_sq"
private theorem rowNorm_nonneg : 0 ≤ rowNorm g := _root_.Real.sqrt_nonneg _

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.rowNorm_pos (hg : g.det ≠ 0) : 0 < rowNorm g := by
  apply _root_.Real.sqrt_pos.mpr
  by_contra h
  have h0 : g 1 0 = 0 ∧ g 1 1 = 0 := by
    constructor <;> rw [← norm_eq_zero] <;> nlinarith [norm_nonneg (g 1 0), norm_nonneg (g 1 1)]
  apply hg
  rw [Matrix.det_fin_two, h0.1, h0.2]
  ring

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "rowNorm_pos"
private theorem rowNorm_ne_zero (hg : g.det ≠ 0) : rowNorm g ≠ 0 := (rowNorm_pos hg).ne'

open ComplexConjugate in
private theorem ofReal_rowNorm_sq : ((rowNorm g : ℝ) : ℂ) ^ 2 = conj (g 1 0) * g 1 0 + conj (g 1 1) * g 1 1 := by
  rw [Complex.conj_mul', Complex.conj_mul', ← Complex.ofReal_pow, rowNorm_sq]
  push_cast
  ring

private theorem kOf_mem (hg : g.det ≠ 0) : kOf g ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hr : ((rowNorm g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rowNorm_ne_zero hg)
  have hsq := ofReal_rowNorm_sq (g := g)
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kOf, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] <;>
    field_simp <;> (try rw [hsq]) <;> ring

private theorem eq_unip_mul (hg : g.det ≠ 0) :
    g = !![1, xOf g; 0, 1] * (((rowNorm g : ℝ) : ℂ) • (!![yOf g, 0; 0, 1] * kOf g)) := by
  have hr : ((rowNorm g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rowNorm_ne_zero hg)
  have hsq := ofReal_rowNorm_sq (g := g)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kOf, xOf, yOf, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;>
    field_simp <;> (try rw [hsq]) <;> ring

private theorem norm_yOf : ‖yOf g‖ = ‖g.det‖ / rowNorm g ^ 2 := by
  rw [yOf, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg rowNorm_nonneg]

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.yOf_ne_zero (hg : g.det ≠ 0) : yOf g ≠ 0 :=
  div_ne_zero hg (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (rowNorm_ne_zero hg)))

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "yOf_ne_zero"
private theorem diagOne_mul_eq (hg : g.det ≠ 0) (t : ℂ) :
    !![t, 0; 0, 1] * g
      = !![1, t * xOf g; 0, 1] * (((rowNorm g : ℝ) : ℂ) • (!![t * yOf g, 0; 0, 1] * kOf g)) := by
  conv_lhs => rw [eq_unip_mul hg]
  exact diagOne_mul_iwasawa t (xOf g) _ (yOf g) (kOf g)

end Complex

end ArchIwasawa

namespace ArchIwasawa

private theorem rpow_neg_le_rpow_neg_max {s σ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : s ^ (-σ) ≤ s ^ (-(max σ 0)) :=
  Real.rpow_le_rpow_of_exponent_ge hs hs1 (by have := le_max_left σ 0; linarith)

namespace Real
end Real

end ArchIwasawa

namespace ArchIwasawa
namespace Complex
end ArchIwasawa.Complex

private theorem norm_exp_two_pi_I_mul (x : ℝ) : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * x)‖ = 1 := by
  have h : 2 * (Real.pi : ℂ) * Complex.I * x = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem norm_psi (x : ℝ) : ‖ArchR.psi x‖ = 1 := norm_exp_two_pi_I_mul x

private theorem norm_psiC (z : ℂ) : ‖ArchC.psi z‖ = 1 := norm_exp_two_pi_I_mul (2 * z.re)

private theorem norm_centralChar_mul {P : RealArchParam} {z : ℝ} (hz : 0 < z) :
    ‖ArchR.centralChar P z * ((|z| : ℝ) : ℂ)‖ = z ^ P.centralExponent.re * z := by
  have hite : (if P.centralSign = 0 then (1 : ℂ) else ((SignType.sign z : ℝ) : ℂ)) = 1 := by
    rw [sign_pos hz]
    simp
  rw [ArchR.centralChar, ArchR.quasiChar, hite, mul_one, norm_mul, abs_of_pos hz, Complex.norm_cpow_eq_rpow_re_of_pos hz,
    Complex.norm_real, Real.norm_of_nonneg hz.le]

private theorem norm_centralCharC_mul {P : ComplexArchParam} {r : ℝ} (hr : 0 < r) :
    ‖ArchC.centralChar P r * ((‖(r : ℂ)‖ ^ 2 : ℝ) : ℂ)‖ = r ^ (2 * P.centralExponent).re * r ^ 2 := by
  have hnr : ‖(r : ℂ)‖ = r := Complex.norm_of_nonneg hr.le
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [ArchC.centralChar, ArchC.quasiChar, hnr, div_self hr0, _root_.one_zpow, mul_one, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg r)]

private theorem norm_asPi_zero (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖ = ‖W (!![y, 0; 0, 1] * k)‖ := by
  rw [norm_iteratedFDerivWithin_zero]
  rfl

private theorem norm_asPiC_zero (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖iteratedFDerivWithin ℝ 0 (ArchC.asPi W) ArchC.glSet (ArchC.diagOneMulCoords z k)‖ = ‖W (!![z, 0; 0, 1] * k)‖ := by
  rw [norm_iteratedFDerivWithin_zero]
  rfl

namespace ArchDatumR p2m_export "LanglandsTunnell.Converse.ArchDatumR" "W unip_law decay_top smooth central_law mk exists_W_eq_fderivWithin_mul norm_iteratedFDerivWithin_diagOne_le" end ArchDatumR
namespace ArchDatumR
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumR" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumR.top_bound {P : RealArchParam} (D : ArchDatumR P) (N : ℕ) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ → 1 ≤ |y| →
      ‖D.W (!![y, 0; 0, 1] * k)‖ ≤ C * |y| ^ (-(N : ℝ)) := by
  obtain ⟨C, h⟩ := D.decay_top 0 N
  exact ⟨C, fun y k hk hy => (norm_asPi_zero D.W y k).symm.trans_le (h y k hk hy)⟩

end ArchDatumR
p2m_export "LanglandsTunnell.Converse" "ArchDatumR.top_bound"
namespace ArchDatumC p2m_export "LanglandsTunnell.Converse.ArchDatumC" "central_law unip_law W mk decay_top smooth exists_W_eq_fderivWithin_mul norm_iteratedFDerivWithin_diagOne_le" end ArchDatumC
namespace ArchDatumC
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumC" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumC.top_bound {P : ComplexArchParam} (D : ArchDatumC P) (N : ℕ) :
    ∃ C : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), k ∈ Matrix.unitaryGroup (Fin 2) ℂ → 1 ≤ ‖z‖ →
      ‖D.W (!![z, 0; 0, 1] * k)‖ ≤ C * ‖z‖ ^ (-(N : ℝ)) := by
  obtain ⟨C, h⟩ := D.decay_top 0 N
  exact ⟨C, fun z k hk hz => (norm_asPiC_zero D.W z k).symm.trans_le (h z k hk hz)⟩

end ArchDatumC
p2m_export "LanglandsTunnell.Converse" "ArchDatumC.top_bound"
end ArchProfileBounds

open Topology

section ProfileAssembly

private theorem rpow_neg_mul_le_of_le {x σ σ' : ℝ} (hx : 0 < x) (hσ' : σ' ≤ σ) {n : ℕ} (hn : σ - σ' ≤ n)
    (M : ℕ) :
    x ^ (-σ') * (1 + x) ^ (-((M + n : ℕ) : ℝ)) ≤ x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) := by
  have h1x : 0 < 1 + x := by linarith
  have hpow : x ^ (σ - σ') ≤ (1 + x) ^ (n : ℝ) := by
    calc x ^ (σ - σ') ≤ (1 + x) ^ (σ - σ') :=
          Real.rpow_le_rpow hx.le (by linarith) (by linarith)
      _ ≤ (1 + x) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hn
  have hsplit : x ^ (-σ') = x ^ (-σ) * x ^ (σ - σ') := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have hsplit' : (1 + x) ^ (-((M + n : ℕ) : ℝ)) = (1 + x) ^ (-(M : ℝ)) * ((1 + x) ^ (n : ℝ))⁻¹ := by
    rw [← Real.rpow_neg h1x.le, ← Real.rpow_add h1x]; congr 1; push_cast; ring
  rw [hsplit, hsplit']
  have hpos : 0 < (1 + x) ^ (n : ℝ) := Real.rpow_pos_of_pos h1x _
  have hxσ : 0 ≤ x ^ (-σ) := (Real.rpow_pos_of_pos hx _).le
  have hM : 0 ≤ (1 + x) ^ (-(M : ℝ)) := (Real.rpow_pos_of_pos h1x _).le
  calc x ^ (-σ) * x ^ (σ - σ') * ((1 + x) ^ (-(M : ℝ)) * ((1 + x) ^ (n : ℝ))⁻¹)
      = x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) * (x ^ (σ - σ') / (1 + x) ^ (n : ℝ)) := by ring
    _ ≤ x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) * 1 := by
          gcongr
          exact (div_le_one hpos).mpr hpow
    _ = x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) := mul_one _

end ProfileAssembly

open Topology

section ProfilePlaceIdentities

private theorem det_diagOneR_mul (y : ℝ) (m : Matrix (Fin 2) (Fin 2) ℝ) : (ArchR.diagOne y * m).det = y * m.det := by
  rw [Matrix.det_mul, ArchR.diagOne, Matrix.det_fin_two_of]; ring

private theorem det_diagOneC_mul (z : ℂ) (m : Matrix (Fin 2) (Fin 2) ℂ) : (ArchC.diagOne z * m).det = z * m.det := by
  rw [Matrix.det_mul, ArchC.diagOne, Matrix.det_fin_two_of]; ring

private theorem real_factor_bound (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) {σ A B : ℝ} {N : ℕ} {m : Matrix (Fin 2) (Fin 2) ℝ}
    {y : ℝ} (hy : y ≠ 0) (hW : ‖W (ArchR.diagOne y * m)‖ ≤ A * (|y| ^ (-σ) * (1 + |y|) ^ (-(N : ℝ))))
    (hB : (Real.sqrt |m.det|)⁻¹ ≤ B) :
    ‖W (ArchR.diagOne y * m) * ((Real.sqrt |(ArchR.diagOne y * m).det| : ℝ) : ℂ)⁻¹‖
      ≤ max A 0 * B * (|y| ^ (-(σ + 1 / 2)) * (1 + |y|) ^ (-(N : ℝ))) := by
  have hay : 0 < |y| := abs_pos.mpr hy
  have hsqy : 0 < Real.sqrt |y| := Real.sqrt_pos.mpr hay
  have hBnn : 0 ≤ B := (inv_nonneg.mpr (Real.sqrt_nonneg _)).trans hB
  have hnorm : ‖(((Real.sqrt |(ArchR.diagOne y * m).det| : ℝ) : ℂ))⁻¹‖ = (Real.sqrt |y|)⁻¹ * (Real.sqrt |m.det|)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), det_diagOneR_mul, abs_mul,
      Real.sqrt_mul (abs_nonneg y), mul_inv]
  have hsq : (Real.sqrt |y|)⁻¹ = |y| ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hay.le]
  have hsplit : |y| ^ (-(σ + 1 / 2)) = |y| ^ (-σ) * |y| ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hay]; congr 1; ring
  have hprof : 0 ≤ |y| ^ (-σ) * (1 + |y|) ^ (-(N : ℝ)) :=
    mul_nonneg (Real.rpow_pos_of_pos hay _).le (Real.rpow_pos_of_pos (by linarith) _).le
  have hW' : ‖W (ArchR.diagOne y * m)‖ ≤ max A 0 * (|y| ^ (-σ) * (1 + |y|) ^ (-(N : ℝ))) :=
    hW.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hprof)
  rw [norm_mul, hnorm]
  calc ‖W (ArchR.diagOne y * m)‖ * ((Real.sqrt |y|)⁻¹ * (Real.sqrt |m.det|)⁻¹)
      ≤ (max A 0 * (|y| ^ (-σ) * (1 + |y|) ^ (-(N : ℝ)))) * ((Real.sqrt |y|)⁻¹ * B) := by
        gcongr
    _ = max A 0 * B * ((|y| ^ (-σ) * |y| ^ (-(1 / 2 : ℝ))) * (1 + |y|) ^ (-(N : ℝ))) := by rw [hsq]; ring
    _ = max A 0 * B * (|y| ^ (-(σ + 1 / 2)) * (1 + |y|) ^ (-(N : ℝ))) := by rw [hsplit]

private theorem complex_factor_bound (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ) {σ A B : ℝ} {N : ℕ} {m : Matrix (Fin 2) (Fin 2) ℂ}
    {z : ℂ} (hz : z ≠ 0) (hW : ‖W (ArchC.diagOne z * m)‖ ≤ A * (‖z‖ ^ (-σ) * (1 + ‖z‖) ^ (-(N : ℝ))))
    (hB : ‖m.det‖⁻¹ ≤ B) :
    ‖W (ArchC.diagOne z * m) * ((‖(ArchC.diagOne z * m).det‖ : ℝ) : ℂ)⁻¹‖
      ≤ max A 0 * B * (‖z‖ ^ (-(σ + 1)) * (1 + ‖z‖) ^ (-(N : ℝ))) := by
  have haz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hBnn : 0 ≤ B := (inv_nonneg.mpr (norm_nonneg _)).trans hB
  have hnorm : ‖(((‖(ArchC.diagOne z * m).det‖ : ℝ) : ℂ))⁻¹‖ = ‖z‖⁻¹ * ‖m.det‖⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), det_diagOneC_mul, norm_mul,
      mul_inv]
  have hinv : ‖z‖⁻¹ = ‖z‖ ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one]
  have hsplit : ‖z‖ ^ (-(σ + 1)) = ‖z‖ ^ (-σ) * ‖z‖ ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add haz]; congr 1; ring
  have hprof : 0 ≤ ‖z‖ ^ (-σ) * (1 + ‖z‖) ^ (-(N : ℝ)) :=
    mul_nonneg (Real.rpow_pos_of_pos haz _).le (Real.rpow_pos_of_pos (by linarith) _).le
  have hW' : ‖W (ArchC.diagOne z * m)‖ ≤ max A 0 * (‖z‖ ^ (-σ) * (1 + ‖z‖) ^ (-(N : ℝ))) :=
    hW.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hprof)
  rw [norm_mul, hnorm]
  calc ‖W (ArchC.diagOne z * m)‖ * (‖z‖⁻¹ * ‖m.det‖⁻¹)
      ≤ (max A 0 * (‖z‖ ^ (-σ) * (1 + ‖z‖) ^ (-(N : ℝ)))) * (‖z‖⁻¹ * B) := by
        gcongr
    _ = max A 0 * B * ((‖z‖ ^ (-σ) * ‖z‖ ^ (-(1 : ℝ))) * (1 + ‖z‖) ^ (-(N : ℝ))) := by rw [hinv]; ring
    _ = max A 0 * B * (‖z‖ ^ (-(σ + 1)) * (1 + ‖z‖) ^ (-(N : ℝ))) := by rw [hsplit]

end ProfilePlaceIdentities

namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis"

section ArchProfile

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

private noncomputable def archFactorAt (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  if hw : w.IsReal then
    (dR w hw).W (realComponent w hw g) * ((Real.sqrt |(realComponent w hw g).det| : ℝ) : ℂ)⁻¹
  else
    (dC w (not_isReal_iff_isComplex.mp hw)).W (complexComponent w (not_isReal_iff_isComplex.mp hw) g)
      * ((‖(complexComponent w (not_isReal_iff_isComplex.mp hw) g).det‖ : ℝ) : ℂ)⁻¹

private theorem archW'_eq_prod_archFactorAt (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) (g : AdelicGL2 (𝓞 K) K) :
    archW' archR archC dR dC g = ∏ w : InfinitePlace K, archFactorAt archR archC dR dC w g := by
  unfold archW' archW archNormFactor archFactorAt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  split_ifs <;> rfl

private theorem realComponent_globalPoints_diagOne_mul (w : InfinitePlace K) (hw : w.IsReal) (α : Kˣ)
    (g : AdelicGL2 (𝓞 K) K) :
    realComponent w hw (globalPoints (𝓞 K) K (diagOne α) * g)
      = ArchR.diagOne (ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K))) * realComponent w hw g := by
  rw [realComponent_eq_map, realComponent_eq_map, FiniteWhittaker.globalPoints_diagOne, map_mul, map_mul,
    FiniteWhittaker.archComponent_glArch_diagOne, Units.val_mul, Matrix.map_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne, diagOne_coe_apply, Ideles.archUnitAt_val, NumberField.AdeleRing.algebraMap_fst_apply]
  all_goals rfl

private theorem complexComponent_globalPoints_diagOne_mul (w : InfinitePlace K) (hw : w.IsComplex) (α : Kˣ)
    (g : AdelicGL2 (𝓞 K) K) :
    complexComponent w hw (globalPoints (𝓞 K) K (diagOne α) * g)
      = ArchC.diagOne (ringEquivComplexOfIsComplex hw (algebraMap K w.Completion (α : K)))
          * complexComponent w hw g := by
  rw [complexComponent_eq_map, complexComponent_eq_map, FiniteWhittaker.globalPoints_diagOne, map_mul, map_mul,
    FiniteWhittaker.archComponent_glArch_diagOne, Units.val_mul, Matrix.map_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ArchC.diagOne, diagOne_coe_apply, Ideles.archUnitAt_val, NumberField.AdeleRing.algebraMap_fst_apply]
  all_goals rfl

omit [NumberField K] in
private theorem abs_ringEquivReal_algebraMap (w : InfinitePlace K) (hw : w.IsReal) (x : K) :
    |ringEquivRealOfIsReal hw (algebraMap K w.Completion x)| = w x := by
  have h1 := (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)
    (algebraMap K w.Completion x)
  rw [Real.norm_eq_abs] at h1
  rw [ringEquivRealOfIsReal_apply, h1,
    show algebraMap K w.Completion x = (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.Completion) from rfl,
    Completion.norm_coe, RingEquiv.apply_symm_apply]

omit [NumberField K] in
private theorem norm_ringEquivComplex_algebraMap (w : InfinitePlace K) (hw : w.IsComplex) (x : K) :
    ‖ringEquivComplexOfIsComplex hw (algebraMap K w.Completion x)‖ = w x := by
  have h1 := (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (algebraMap K w.Completion x)
  rw [ringEquivComplexOfIsComplex_apply, h1,
    show algebraMap K w.Completion x = (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.Completion) from rfl,
    Completion.norm_coe, RingEquiv.apply_symm_apply]

end ArchProfile

end CuspSynthesis

end LanglandsTunnell.Converse

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]

section TorusModel
end TorusModel

section TorusClass
end TorusClass

section GaussFixedVector

open scoped WithZero
open UnramifiedWhittaker

private def IsKZero (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    Prop :=
  Valued.v (M 0 0) = 1 ∧ Valued.v (M 1 1) = 1 ∧ Valued.v (M 0 1) ≤ 1 ∧ Valued.v (M 1 0) ≤ WithZero.exp (-(m : ℤ))

private noncomputable def kChar (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : ℂ :=
  TateLocal.charExt (localChar ω v) (M 1 1) * TateLocal.charExt (epsS v) (M 0 0 / M 1 1)

private theorem kZero_mul_entries (v : HeightOneSpectrum (𝓞 K)) (m : ℕ)
    {G k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)}
    (h11 : Valued.v (G 1 1) ≠ 0) (h00 : Valued.v (G 0 0) = Valued.v (G 1 1))
    (h01 : Valued.v (G 0 1) ≤ Valued.v (G 1 1))
    (h10 : Valued.v (G 1 0) ≤ Valued.v (G 1 1) * WithZero.exp (-(m : ℤ))) (hk : IsKZero v m k) :
    ∃ s t : v.adicCompletion K, Valued.v s ≤ WithZero.exp (-(m : ℤ)) ∧ Valued.v t ≤ WithZero.exp (-(m : ℤ)) ∧
      (G * k) 0 0 = G 0 0 * k 0 0 * (1 + s) ∧ (G * k) 1 1 = G 1 1 * k 1 1 * (1 + t) ∧
      Valued.v ((G * k) 0 1) ≤ Valued.v (G 1 1) ∧
      Valued.v ((G * k) 1 0) ≤ Valued.v (G 1 1) * WithZero.exp (-(m : ℤ)) := by
  obtain ⟨hk00, hk11, hk01, hk10⟩ := hk
  have hG00 : G 0 0 ≠ 0 := fun h => h11 (by rw [← h00, h, map_zero])
  have hG11 : G 1 1 ≠ 0 := fun h => h11 (by rw [h, map_zero])
  have hk00' : k 0 0 ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero] at hk00; exact hk00)
  have hk11' : k 1 1 ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero] at hk11; exact hk11)
  refine ⟨G 0 1 * k 1 0 / (G 0 0 * k 0 0), G 1 0 * k 0 1 / (G 1 1 * k 1 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_div₀, map_mul, map_mul, hk00, mul_one, h00, div_le_iff₀ (zero_lt_iff.mpr h11)]
    calc Valued.v (G 0 1) * Valued.v (k 1 0) ≤ Valued.v (G 1 1) * WithZero.exp (-(m : ℤ)) := mul_le_mul' h01 hk10
      _ = WithZero.exp (-(m : ℤ)) * Valued.v (G 1 1) := mul_comm _ _
  · rw [map_div₀, map_mul, map_mul, hk11, mul_one, div_le_iff₀ (zero_lt_iff.mpr h11)]
    calc Valued.v (G 1 0) * Valued.v (k 0 1) ≤ Valued.v (G 1 1) * WithZero.exp (-(m : ℤ)) * 1 := mul_le_mul' h10 hk01
      _ = WithZero.exp (-(m : ℤ)) * Valued.v (G 1 1) := by rw [mul_one, mul_comm]
  · rw [Matrix.mul_apply, Fin.sum_univ_two, mul_add, mul_one, mul_div_assoc',
      mul_div_cancel_left₀ _ (mul_ne_zero hG00 hk00')]
  · rw [Matrix.mul_apply, Fin.sum_univ_two, mul_add, mul_one, mul_div_assoc',
      mul_div_cancel_left₀ _ (mul_ne_zero hG11 hk11'), add_comm]
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [map_mul, h00]; exact (mul_le_mul_right hk01 _).trans_eq (mul_one _)
    · rw [map_mul, hk11, mul_one]; exact h01
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [map_mul, hk00, mul_one]; exact h10
    · rw [map_mul]; exact mul_le_mul_right hk10 _

private theorem componentMatrix_mul_placeEmbed_self (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)
    (k : GL (Fin 2) (v.adicCompletion K)) :
    componentMatrix v (g * placeEmbed K v k) =
      componentMatrix v g * (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  rw [componentMatrix_mul]
  congr 1
  show ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
    ((AdelicDock.finEmbed (𝓞 K) K) (AdelicDock.localEmbed (𝓞 K) K v k))) :
    GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = _
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

private theorem componentMatrix_mul_placeEmbed_of_ne {v w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v)
    (g : AdelicGL2 (𝓞 K) K) (k : GL (Fin 2) (v.adicCompletion K)) :
    componentMatrix w (g * placeEmbed K v k) = componentMatrix w g := by
  rw [componentMatrix_mul]
  conv_rhs => rw [← mul_one (componentMatrix w g)]
  congr 1
  show ((AdelicLevel.finComponent (𝓞 K) K w (AdelicLevel.glFin (𝓞 K) K
    ((AdelicDock.finEmbed (𝓞 K) K) (AdelicDock.localEmbed (𝓞 K) K v k))) :
    GL (Fin 2) (w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) = _
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hw, Units.val_one]

private theorem placeEmbed_mem_finiteAdelicGL2Subgroup (v : HeightOneSpectrum (𝓞 K))
    (k : GL (Fin 2) (v.adicCompletion K)) : placeEmbed K v k ∈ finiteAdelicGL2Subgroup K :=
  AdelicDock.glArch_finEmbed (𝓞 K) K _

private theorem archW_mul_of_mem_finiteAdelicGL2Subgroup
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ finiteAdelicGL2Subgroup K) (g : AdelicGL2 (𝓞 K) K) :
    archW' archR archC dR dC (g * k) = archW' archR archC dR dC g := by
  have h : glArch (𝓞 K) K (g * k) = glArch (𝓞 K) K g := by
    rw [map_mul, (mem_finiteAdelicGL2Subgroup_iff K k).mp hk, mul_one]
  simp only [archW', archNormFactor, archW, realComponent, complexComponent, h]

private theorem memZK0At_mul_placeEmbed {S : Finset (HeightOneSpectrum (𝓞 K))}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω) (v : ↥S) {k : GL (Fin 2) (v.1.adicCompletion K)} (hk : IsKZero v.1 (d.m v) k)
    {g : AdelicGL2 (𝓞 K) K} (hg : MemZK0At v.1 (d.m v) g) :
    MemZK0At v.1 (d.m v) (g * placeEmbed K v.1 k) ∧
      TateLocal.charExt (localChar ω v.1) (componentMatrix v.1 (g * placeEmbed K v.1 k) 1 1) *
          TateLocal.charExt (epsS v.1)
            (componentMatrix v.1 (g * placeEmbed K v.1 k) 0 0 / componentMatrix v.1 (g * placeEmbed K v.1 k) 1 1) =
        kChar epsS ω v.1 k *
          (TateLocal.charExt (localChar ω v.1) (componentMatrix v.1 g 1 1) *
            TateLocal.charExt (epsS v.1) (componentMatrix v.1 g 0 0 / componentMatrix v.1 g 1 1)) := by
  obtain ⟨hg11, hg00, hg01, hg10⟩ := hg
  obtain ⟨s, t, hs, ht, e00, e11, e01, e10⟩ := kZero_mul_entries v.1 (d.m v) hg11 hg00 hg01 hg10 hk
  obtain ⟨hk00, hk11, -, -⟩ := hk
  have hm : 1 ≤ d.m v := d.m_pos v
  have hlt : WithZero.exp (-(d.m v : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hs1 : Valued.v (1 + s) = 1 := Valuation.map_one_add_of_lt _ (hs.trans_lt hlt)
  have ht1 : Valued.v (1 + t) = 1 := Valuation.map_one_add_of_lt _ (ht.trans_lt hlt)
  set G := componentMatrix v.1 g with hG
  have hG11 : G 1 1 ≠ 0 := fun h => hg11 (by rw [h, map_zero])
  have hG00 : G 0 0 ≠ 0 := fun h => hg11 (by rw [← hg00, h, map_zero])
  have hk00' : (k : Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) 0 0 ≠ 0 := fun h =>
    zero_ne_one (by rw [h, map_zero] at hk00; exact hk00)
  have hk11' : (k : Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) 1 1 ≠ 0 := fun h =>
    zero_ne_one (by rw [h, map_zero] at hk11; exact hk11)
  have hs0 : (1 + s) ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero] at hs1; exact hs1)
  have ht0 : (1 + t) ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero] at ht1; exact ht1)
  refine ⟨?_, ?_⟩
  · unfold MemZK0At
    rw [componentMatrix_mul_placeEmbed_self, ← hG]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e11, map_mul, map_mul, hk11, ht1, mul_one, mul_one]; exact hg11
    · rw [e00, e11, map_mul, map_mul, map_mul, map_mul, hk00, hk11, hs1, ht1, hg00]
    · rw [e11, map_mul, map_mul, hk11, ht1, mul_one, mul_one]; exact e01
    · rw [e11, map_mul, map_mul, hk11, ht1, mul_one, mul_one]; exact e10
  rw [componentMatrix_mul_placeEmbed_self, ← hG]
  have er : G 0 0 * (k : Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) 0 0 * (1 + s) /
        (G 1 1 * (k : Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) 1 1 * (1 + t)) =
      G 0 0 / G 1 1 *
        ((k : Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) 0 0 /
          (k : Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) 1 1) *
        (1 + (s - t) / (1 + t)) := by
    field_simp
    ring
  have hr : Valued.v ((s - t) / (1 + t)) ≤ WithZero.exp (-(d.m v : ℤ)) := by
    rw [map_div₀, ht1, div_one]
    exact (Valuation.map_sub _ _ _).trans (max_le hs ht)
  rw [e00, e11, er, charExt_mul_of_ne_zero v.1 _ (mul_ne_zero hG11 hk11') ht0,
    charExt_mul_of_ne_zero v.1 _ hG11 hk11', charExt_one_add v.1 (d.central_level v) hm ht,
    charExt_mul_of_ne_zero v.1 _ (mul_ne_zero (div_ne_zero hG00 hG11) (div_ne_zero hk00' hk11'))
      (fun h => zero_ne_one (by
        have := Valuation.map_one_add_of_lt _ (hr.trans_lt hlt)
        rw [h, map_zero] at this; exact this)),
    charExt_mul_of_ne_zero v.1 _ (div_ne_zero hG00 hG11) (div_ne_zero hk00' hk11'),
    charExt_one_add v.1 (d.epsS_level v) hm hr, kChar]
  ring

private theorem epsChar_mul_placeEmbed {S : Finset (HeightOneSpectrum (𝓞 K))}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω) (v : ↥S) {k : GL (Fin 2) (v.1.adicCompletion K)} (hk : IsKZero v.1 (d.m v) k)
    (hki : IsKZero v.1 (d.m v) (k⁻¹ : GL (Fin 2) (v.1.adicCompletion K))) (g : AdelicGL2 (𝓞 K) K) :
    d.epsChar (g * placeEmbed K v.1 k) = kChar epsS ω v.1 k * d.epsChar g := by
  classical
  have hcomp : ∀ w : ↥S, w ≠ v → componentMatrix w.1 (g * placeEmbed K v.1 k) = componentMatrix w.1 g :=
    fun w hw => componentMatrix_mul_placeEmbed_of_ne (fun h => hw (Subtype.ext h)) g k
  have hguard : (∀ w : ↥S, MemZK0At w.1 (d.m w) (g * placeEmbed K v.1 k)) ↔ ∀ w : ↥S, MemZK0At w.1 (d.m w) g := by
    constructor
    · intro h w
      by_cases hw : w = v
      · subst hw
        have h' := (memZK0At_mul_placeEmbed d w hki (h w)).1
        rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at h'
      · have h' := h w; unfold MemZK0At at h' ⊢; rwa [hcomp w hw] at h'
    · intro h w
      by_cases hw : w = v
      · subst hw; exact (memZK0At_mul_placeEmbed d w hk (h w)).1
      · have h' := h w; unfold MemZK0At at h' ⊢; rwa [hcomp w hw]
  unfold JLData.epsChar
  by_cases hg : ∀ w : ↥S, MemZK0At w.1 (d.m w) g
  · rw [if_pos hg, if_pos (hguard.mpr hg), ← Finset.mul_prod_erase _ _ (Finset.mem_univ v),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ v), (memZK0At_mul_placeEmbed d v hk (hg v)).2, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [hcomp w (Finset.ne_of_mem_erase hw)]
  · rw [if_neg hg, if_neg (fun h => hg (hguard.mp h)), mul_zero]

private theorem mul_placeEmbed_mem_kZeroSet_iff {S : Finset (HeightOneSpectrum (𝓞 K))}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω) (v : ↥S) {k : GL (Fin 2) (v.1.adicCompletion K)} (hk : IsKZero v.1 (d.m v) k)
    (hki : IsKZero v.1 (d.m v) (k⁻¹ : GL (Fin 2) (v.1.adicCompletion K))) (g : AdelicGL2 (𝓞 K) K) :
    g * placeEmbed K v.1 k ∈ kZeroSet S d.m ↔ g ∈ kZeroSet S d.m := by
  constructor
  · intro h w
    by_cases hw : w = v
    · subst hw
      have h' := (memZK0At_mul_placeEmbed d w hki (h w)).1
      rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at h'
    · have h' := h w
      unfold MemZK0At at h' ⊢
      rwa [componentMatrix_mul_placeEmbed_of_ne (fun h => hw (Subtype.ext h))] at h'
  · intro h w
    by_cases hw : w = v
    · subst hw; exact (memZK0At_mul_placeEmbed d w hk (h w)).1
    · have h' := h w
      unfold MemZK0At at h' ⊢
      rwa [componentMatrix_mul_placeEmbed_of_ne (fun h => hw (Subtype.ext h))]

private theorem jlSeries_mul_placeEmbed {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (v : ↥S) {k : GL (Fin 2) (v.1.adicCompletion K)}
    (hk : IsKZero v.1 (d.m v) k) (hki : IsKZero v.1 (d.m v) (k⁻¹ : GL (Fin 2) (v.1.adicCompletion K)))
    (g : AdelicGL2 (𝓞 K) K) :
    jlSeries' d archR archC dR dC dF (g * placeEmbed K v.1 k) =
      kChar epsS ω v.1 k * jlSeries' d archR archC dR dC dF g := by
  simp only [jlSeries', whittakerSeries, ← mul_assoc,
    archW_mul_of_mem_finiteAdelicGL2Subgroup archR archC dR dC (placeEmbed_mem_finiteAdelicGL2Subgroup v.1 k),
    dF.blind_at v.1 v.2, epsChar_mul_placeEmbed d v hk hki, ← tsum_mul_left]
  congr 1
  funext α
  ring

variable {D : Set (AdelicGL2 (𝓞 K) K)}
  {hD : ∀ g : AdelicGL2 (𝓞 K) K, ∃ γ : GL (Fin 2) K, globalPoints (𝓞 K) K γ * g ∈ D}
  {f : AdelicGL2 (𝓞 K) K → ℂ} in
private theorem extend_mul_right_eq_mul (hf : InvOn D f) (k : AdelicGL2 (𝓞 K) K) (c : ℂ)
    (hk : ∀ g : AdelicGL2 (𝓞 K) K, g * k ∈ D ↔ g ∈ D) (hfk : ∀ g ∈ D, f (g * k) = c * f g)
    (g : AdelicGL2 (𝓞 K) K) :
    extendByRationalPoints D hD f (g * k) = c * extendByRationalPoints D hD f g := by
  unfold extendByRationalPoints
  have h₁ := Classical.choose_spec (hD (g * k))
  have h₂ := Classical.choose_spec (hD g)
  rw [← mul_assoc] at h₁ ⊢
  rw [hfk _ ((hk _).mp h₁), hf.eq_of_mem ((hk _).mp h₁) h₂]

private theorem theForm_mul_placeEmbed {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (hinv : InvOn (kZeroSet S d.m) (jlSeries' d archR archC dR dC dF))
    (v : ↥S) {k : GL (Fin 2) (v.1.adicCompletion K)}
    (hk : IsKZero v.1 (d.m v) k) (hki : IsKZero v.1 (d.m v) (k⁻¹ : GL (Fin 2) (v.1.adicCompletion K)))
    (g : AdelicGL2 (𝓞 K) K) :
    theForm d archR archC dR dC dF (g * placeEmbed K v.1 k) =
      kChar epsS ω v.1 k * theForm d archR archC dR dC dF g := by
  show extendByRationalPoints (kZeroSet S d.m) (kZeroSet_meets S d.m) (jlSeries' d archR archC dR dC dF) _ =
    _ * extendByRationalPoints (kZeroSet S d.m) (kZeroSet_meets S d.m) (jlSeries' d archR archC dR dC dF) g
  exact extend_mul_right_eq_mul hinv _ _ (mul_placeEmbed_mem_kZeroSet_iff d v hk hki)
    (fun g' _ => jlSeries_mul_placeEmbed d archR archC dR dC dF v hk hki g') g

private theorem theForm_mul_of_level {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (hinv : InvOn (kZeroSet S d.m) (jlSeries' d archR archC dR dC dF))
    {N₀ : Ideal (𝓞 K)} (hN₀ : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ levelOne (𝓞 K) K N₀ ⊓ finiteAdelicGL2Subgroup K,
      dF.Wf (g * u) = dF.Wf g)
    {u : AdelicGL2 (𝓞 K) K} (hu : u ∈ levelOne (𝓞 K) K N₀ ⊓ finiteAdelicGL2Subgroup K)
    (huS : ∀ v : ↥S, componentMatrix v.1 u = 1) (g : AdelicGL2 (𝓞 K) K) :
    theForm d archR archC dR dC dF (g * u) = theForm d archR archC dR dC dF g := by
  have hc : ∀ (h : AdelicGL2 (𝓞 K) K) (v : ↥S), componentMatrix v.1 (h * u) = componentMatrix v.1 h :=
    fun h v => by rw [componentMatrix_mul, huS v, mul_one]
  have hmem : ∀ h : AdelicGL2 (𝓞 K) K, h * u ∈ kZeroSet S d.m ↔ h ∈ kZeroSet S d.m := fun h => by
    simp only [kZeroSet, Set.mem_setOf_eq, MemZK0At, hc h]
  have heps : ∀ h : AdelicGL2 (𝓞 K) K, d.epsChar (h * u) = d.epsChar h := fun h => by
    have hg' : (∀ w : ↥S, MemZK0At w.1 (d.m w) (h * u)) ↔ ∀ w : ↥S, MemZK0At w.1 (d.m w) h := by
      simp only [MemZK0At, hc h]
    unfold JLData.epsChar
    by_cases hg : ∀ w : ↥S, MemZK0At w.1 (d.m w) h
    · rw [if_pos hg, if_pos (hg'.mpr hg)]; simp only [hc h]
    · rw [if_neg hg, if_neg (fun h' => hg (hg'.mp h'))]
  have hser : ∀ h ∈ kZeroSet S d.m,
      jlSeries' d archR archC dR dC dF (h * u) = 1 * jlSeries' d archR archC dR dC dF h := by
    intro h _
    simp only [one_mul, jlSeries', whittakerSeries, ← mul_assoc, heps,
      archW_mul_of_mem_finiteAdelicGL2Subgroup archR archC dR dC (Subgroup.mem_inf.mp hu).2, fun g' => hN₀ g' u hu]
  have h := extend_mul_right_eq_mul (hD := kZeroSet_meets S d.m) hinv u 1 hmem hser g
  rw [one_mul] at h
  exact h

private theorem idealBound_le_of_pow_dvd {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)} {m : ℕ}
    (h : v.asIdeal ^ m ∣ N) : idealBound (𝓞 K) N v ≤ WithZero.exp (-(m : ℤ)) := by
  rw [idealBound_of_ne_bot hN, WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hN) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
  exact h

private theorem isLocalLevelOne_componentMatrix {N : Ideal (𝓞 K)} {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K N) (v : HeightOneSpectrum (𝓞 K)) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v N (componentMatrix v u) := by
  obtain ⟨⟨⟨hint, hll⟩, hlr⟩, -⟩ := mem_finiteLevelOne_iff.mp (mem_levelOne_iff.mp hu)
  refine ⟨fun i j => hint i j v, hll v, ?_⟩
  have h := hlr v
  rw [coe_sub_apply, coe_one_apply] at h
  exact h

private theorem levelOne_le_levelOne_top (N : Ideal (𝓞 K)) : levelOne (𝓞 K) K N ≤ levelOne (𝓞 K) K ⊤ := by
  have key : ∀ M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      IsLevelOneMatrix (𝓞 K) K N M → IsLevelOneMatrix (𝓞 K) K ⊤ M := fun M ⟨⟨hint, hll⟩, hlr⟩ =>
    ⟨⟨hint, fun w => (hll w).trans (by rw [idealBound_top]; exact idealBound_le_one _ _)⟩,
      fun w => (hlr w).trans (by rw [idealBound_top]; exact idealBound_le_one _ _)⟩
  intro u hu
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hu ⊢
  exact ⟨key _ hu.1, key _ hu.2⟩

private theorem isKZero_of_isLocalLevelOne (v : HeightOneSpectrum (𝓞 K)) {N : Ideal (𝓞 K)} {m : ℕ} (hm : 1 ≤ m)
    (hNv : idealBound (𝓞 K) N v ≤ WithZero.exp (-(m : ℤ))) {M Mi : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)}
    (hM : AdelicDock.IsLocalLevelOne (𝓞 K) K v N M) (hMi : AdelicDock.IsLocalLevelOne (𝓞 K) K v N Mi)
    (hMMi : M * Mi = 1) : IsKZero v m M := by
  obtain ⟨hint, hll, hlr⟩ := hM
  obtain ⟨hinti, hlli, -⟩ := hMi
  have hle : ∀ i j, Valued.v (M i j) ≤ 1 := fun i j =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hint i j)
  have hlei : ∀ i j, Valued.v (Mi i j) ≤ 1 := fun i j =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hinti i j)
  have hlt : WithZero.exp (-(m : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have h11 : Valued.v (M 1 1) = 1 := by
    have e : M 1 1 = 1 + (M 1 1 - 1) := by ring
    rw [e]
    exact Valuation.map_one_add_of_lt _ ((hlr.trans hNv).trans_lt hlt)
  have h00 : Valued.v (M 0 0) = 1 := by
    have e : (M * Mi) 0 0 = 1 := by rw [hMMi, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Fin.sum_univ_two] at e
    have e' : M 0 0 * Mi 0 0 = 1 + -(M 0 1 * Mi 1 0) := by rw [← e]; ring
    have hsmall : Valued.v (-(M 0 1 * Mi 1 0)) < 1 := by
      rw [Valuation.map_neg, map_mul]
      calc Valued.v (M 0 1) * Valued.v (Mi 1 0) ≤ 1 * WithZero.exp (-(m : ℤ)) :=
            mul_le_mul' (hle 0 1) (hlli.trans hNv)
        _ < 1 := by rw [one_mul]; exact hlt
    have hprod : Valued.v (M 0 0) * Valued.v (Mi 0 0) = 1 := by
      rw [← map_mul, e']; exact Valuation.map_one_add_of_lt _ hsmall
    by_contra hne
    have hlt' : Valued.v (M 0 0) < 1 := lt_of_le_of_ne (hle 0 0) hne
    have : Valued.v (M 0 0) * Valued.v (Mi 0 0) < 1 :=
      calc Valued.v (M 0 0) * Valued.v (Mi 0 0) ≤ Valued.v (M 0 0) * 1 := mul_le_mul_right (hlei 0 0) _
        _ = Valued.v (M 0 0) := mul_one _
        _ < 1 := hlt'
    exact absurd hprod this.ne
  exact ⟨h00, h11, hle 0 1, hll.trans hNv⟩

private theorem theForm_mul_of_mem_levelOne {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (hinv : InvOn (kZeroSet S d.m) (jlSeries' d archR archC dR dC dF))
    (hWf : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K, dF.Wf (g * u) = dF.Wf g)
    {N : Ideal (𝓞 K)} (hN : ∀ v : ↥S, idealBound (𝓞 K) N v.1 ≤ WithZero.exp (-(d.m v : ℤ))) (S' : Finset ↥S) :
    ∀ (u : AdelicGL2 (𝓞 K) K), u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K →
      (∀ v : ↥S, v ∉ S' → componentMatrix v.1 u = 1) → ∀ g : AdelicGL2 (𝓞 K) K,
      theForm d archR archC dR dC dF (g * u) =
        (∏ v ∈ S', kChar epsS ω v.1 (componentMatrix v.1 u)) * theForm d archR archC dR dC dF g := by
  classical
  induction S' using Finset.induction_on with
  | empty =>
    intro u hu h1 g
    rw [Finset.prod_empty, one_mul]
    exact theForm_mul_of_level d archR archC dR dC dF hinv hWf
      ⟨levelOne_le_levelOne_top N (Subgroup.mem_inf.mp hu).1, (Subgroup.mem_inf.mp hu).2⟩
      (fun v => h1 v (Finset.notMem_empty v)) g
  | insert v S' hv ih =>
    intro u hu h1 g
    set k : GL (Fin 2) (v.1.adicCompletion K) :=
      AdelicLevel.finComponent (𝓞 K) K v.1 (AdelicLevel.glFin (𝓞 K) K u) with hk
    have hcu : componentMatrix v.1 u = (k : Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) := rfl
    have hcui : componentMatrix v.1 u⁻¹ = ((k⁻¹ : GL (Fin 2) (v.1.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) := by
      simp only [componentMatrix, map_inv, hk]
    set u' : AdelicGL2 (𝓞 K) K := u * placeEmbed K v.1 k⁻¹ with hu'
    have e : u = u' * placeEmbed K v.1 k := by
      rw [hu', mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    have hlv : AdelicDock.IsLocalLevelOne (𝓞 K) K v.1 N (k : Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) :=
      hcu ▸ isLocalLevelOne_componentMatrix (Subgroup.mem_inf.mp hu).1 v.1
    have hlvi : AdelicDock.IsLocalLevelOne (𝓞 K) K v.1 N
        ((k⁻¹ : GL (Fin 2) (v.1.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) :=
      hcui ▸ isLocalLevelOne_componentMatrix (inv_mem (Subgroup.mem_inf.mp hu).1) v.1
    have hkz : IsKZero v.1 (d.m v) k :=
      isKZero_of_isLocalLevelOne v.1 (d.m_pos v) (hN v) hlv hlvi (Units.mul_inv k)
    have hkzi : IsKZero v.1 (d.m v) (k⁻¹ : GL (Fin 2) (v.1.adicCompletion K)) :=
      isKZero_of_isLocalLevelOne v.1 (d.m_pos v) (hN v) hlvi hlv (Units.inv_mul k)
    have hu'mem : u' ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
      refine Subgroup.mul_mem _ hu ⟨?_, placeEmbed_mem_finiteAdelicGL2Subgroup v.1 _⟩
      show (AdelicDock.finEmbed (𝓞 K) K) (AdelicDock.localEmbed (𝓞 K) K v.1 k⁻¹) ∈ levelOne (𝓞 K) K N
      rw [AdelicDock.finEmbed_mem_levelOne_iff, AdelicDock.localEmbed_mem_finiteLevelOne_iff,
        AdelicDock.mem_localLevelOne_iff, inv_inv]
      exact ⟨hlvi, hlv⟩
    have h1' : ∀ w : ↥S, w ∉ S' → componentMatrix w.1 u' = 1 := by
      intro w hw
      by_cases hwv : w = v
      · subst hwv
        rw [hu', componentMatrix_mul_placeEmbed_self, hcu, Units.mul_inv]
      · rw [hu', componentMatrix_mul_placeEmbed_of_ne (fun h => hwv (Subtype.ext h))]
        exact h1 w (fun h => (Finset.mem_insert.mp h).elim hwv hw)
    have hcw : ∀ w ∈ S', kChar epsS ω w.1 (componentMatrix w.1 u') = kChar epsS ω w.1 (componentMatrix w.1 u) := by
      intro w hw
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      rw [hu', componentMatrix_mul_placeEmbed_of_ne (fun h => hwv (Subtype.ext h))]
    calc theForm d archR archC dR dC dF (g * u)
        = theForm d archR archC dR dC dF (g * u' * placeEmbed K v.1 k) := by rw [e, ← mul_assoc]
      _ = kChar epsS ω v.1 k * theForm d archR archC dR dC dF (g * u') :=
          theForm_mul_placeEmbed d archR archC dR dC dF hinv v hkz hkzi _
      _ = kChar epsS ω v.1 k *
            ((∏ w ∈ S', kChar epsS ω w.1 (componentMatrix w.1 u')) * theForm d archR archC dR dC dF g) := by
          rw [ih u' hu'mem h1' g]
      _ = (∏ w ∈ insert v S', kChar epsS ω w.1 (componentMatrix w.1 u)) * theForm d archR archC dR dC dF g := by
          rw [Finset.prod_insert hv, hcu, Finset.prod_congr rfl hcw, mul_assoc]

private def finPlaceEval (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →+* v.adicCompletion K where
  toFun x := x.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem componentMatrix_eq_map (v : HeightOneSpectrum (𝓞 K)) (u : AdelicGL2 (𝓞 K) K) :
    componentMatrix v u = (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).map (finPlaceEval v) :=
  Matrix.ext fun _ _ => rfl

private theorem kChar_eq_charExt_det {S : Finset (HeightOneSpectrum (𝓞 K))}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω) (v : ↥S) {M : Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)}
    (hk : IsKZero v.1 (d.m v) M) (h11 : Valued.v (M 1 1 - 1) ≤ WithZero.exp (-(d.m v : ℤ))) :
    kChar epsS ω v.1 M = TateLocal.charExt (epsS v.1) M.det := by
  obtain ⟨hk00, hk11, hk01, hk10⟩ := hk
  have hm : 1 ≤ d.m v := d.m_pos v
  have hlt : WithZero.exp (-(d.m v : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hM00 : M 0 0 ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero] at hk00; exact hk00)
  have hM11 : M 1 1 ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero] at hk11; exact hk11)
  have e11 : M 1 1 = 1 + (M 1 1 - 1) := by ring
  have eω : TateLocal.charExt (localChar ω v.1) (M 1 1) = 1 := by
    rw [e11]; exact charExt_one_add v.1 (d.central_level v) hm h11
  have eε : TateLocal.charExt (epsS v.1) (M 1 1) = 1 := by
    rw [e11]; exact charExt_one_add v.1 (d.epsS_level v) hm h11
  have ediv : TateLocal.charExt (epsS v.1) (M 0 0 / M 1 1) = TateLocal.charExt (epsS v.1) (M 0 0) := by
    have h := charExt_mul_of_ne_zero v.1 (epsS v.1) (div_ne_zero hM00 hM11) hM11
    rw [div_mul_cancel₀ _ hM11, eε, mul_one] at h
    exact h.symm
  have er : M.det = M 0 0 * M 1 1 * (1 + -(M 0 1 * M 1 0) / (M 0 0 * M 1 1)) := by
    rw [Matrix.det_fin_two]; field_simp; ring
  have hr : Valued.v (-(M 0 1 * M 1 0) / (M 0 0 * M 1 1)) ≤ WithZero.exp (-(d.m v : ℤ)) := by
    rw [map_div₀, Valuation.map_neg, map_mul, map_mul, hk00, hk11, mul_one, div_one]
    calc Valued.v (M 0 1) * Valued.v (M 1 0) ≤ 1 * WithZero.exp (-(d.m v : ℤ)) := mul_le_mul' hk01 hk10
      _ = WithZero.exp (-(d.m v : ℤ)) := one_mul _
  have hr1 : (1 + -(M 0 1 * M 1 0) / (M 0 0 * M 1 1)) ≠ 0 := fun h => zero_ne_one (by
    have := Valuation.map_one_add_of_lt _ (hr.trans_lt hlt)
    rw [h, map_zero] at this; exact this)
  rw [kChar, eω, one_mul, ediv, er, charExt_mul_of_ne_zero v.1 _ (mul_ne_zero hM00 hM11) hr1,
    charExt_mul_of_ne_zero v.1 _ hM00 hM11, charExt_one_add v.1 (d.epsS_level v) hm hr, eε, mul_one, mul_one]

private theorem kChar_componentMatrix_eq_one {S : Finset (HeightOneSpectrum (𝓞 K))}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω) {N : Ideal (𝓞 K)} (v : ↥S) (hNv : idealBound (𝓞 K) N v.1 ≤ WithZero.exp (-(d.m v : ℤ)))
    {x : AdelicGL2 (𝓞 K) K} (hx : x ∈ levelOne (𝓞 K) K N)
    (h00 : Valued.v (componentMatrix v.1 x 0 0 - 1) ≤ WithZero.exp (-(d.m v : ℤ))) :
    kChar epsS ω v.1 (componentMatrix v.1 x) = 1 := by
  set M : Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K) := componentMatrix v.1 x with hM
  have hMi : componentMatrix v.1 x⁻¹ * M = 1 := by rw [hM, ← componentMatrix_mul, inv_mul_cancel, componentMatrix_one]
  have hMMi : M * componentMatrix v.1 x⁻¹ = 1 := by rw [hM, ← componentMatrix_mul, mul_inv_cancel, componentMatrix_one]
  have hlv : AdelicDock.IsLocalLevelOne (𝓞 K) K v.1 N M := isLocalLevelOne_componentMatrix hx v.1
  have hlvi : AdelicDock.IsLocalLevelOne (𝓞 K) K v.1 N (componentMatrix v.1 x⁻¹) :=
    isLocalLevelOne_componentMatrix (inv_mem hx) v.1
  have hkz : IsKZero v.1 (d.m v) M := isKZero_of_isLocalLevelOne v.1 (d.m_pos v) hNv hlv hlvi hMMi
  have h11 : Valued.v (M 1 1 - 1) ≤ WithZero.exp (-(d.m v : ℤ)) := hlv.lowerRight.trans hNv
  rw [kChar_eq_charExt_det d v hkz h11]
  have hle : ∀ i j, Valued.v (M i j) ≤ 1 := fun i j =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hlv.integral i j)
  have hdet1 : Valued.v (M.det - 1) ≤ WithZero.exp (-(d.m v : ℤ)) := by
    have e : M.det - 1 = (M 0 0 - 1) * M 1 1 + (M 1 1 - 1) - M 0 1 * M 1 0 := by
      rw [Matrix.det_fin_two]; ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans (max_le ?_ h11)) ?_)
    · rw [map_mul]
      calc Valued.v (M 0 0 - 1) * Valued.v (M 1 1) ≤ WithZero.exp (-(d.m v : ℤ)) * 1 := mul_le_mul' h00 (hle 1 1)
        _ = WithZero.exp (-(d.m v : ℤ)) := mul_one _
    · rw [map_mul]
      calc Valued.v (M 0 1) * Valued.v (M 1 0) ≤ 1 * WithZero.exp (-(d.m v : ℤ)) :=
            mul_le_mul' (hle 0 1) (hkz.2.2.2)
        _ = WithZero.exp (-(d.m v : ℤ)) := one_mul _
  have hlt : WithZero.exp (-(d.m v : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    have := d.m_pos v
    omega
  have hdetv : Valued.v M.det = 1 := by
    have e : M.det = 1 + (M.det - 1) := by ring
    rw [e]
    exact Valuation.map_one_add_of_lt _ (hdet1.trans_lt hlt)
  have hdet0 : M.det ≠ 0 := fun h => by
    rw [h, map_zero] at hdetv
    exact zero_ne_one hdetv
  rw [TateLocal.charExt_of_ne_zero _ hdet0, d.epsS_level v (Units.mk0 M.det hdet0) hdetv hdet1, Units.val_one]

end GaussFixedVector

section UnipotentLaw

open UnramifiedWhittaker

private theorem ext_of_glArch_of_componentMatrix {x y : AdelicGL2 (𝓞 K) K}
    (harch : glArch (𝓞 K) K x = glArch (𝓞 K) K y)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 K), componentMatrix w x = componentMatrix w y) : x = y := by
  refine Units.ext (AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 K) K ?_ ?_)
  · exact congrArg Units.val harch
  · exact AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K fun w => hfin w

private theorem glFin_unipotentGL2 (a : AdeleRing (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 a) = unipotentGL2 a.2 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glFin_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}

private theorem glArch_unipotentGL2 (a : AdeleRing (𝓞 K) K) :
    glArch (𝓞 K) K (unipotentGL2 a) = unipotentGL2 a.1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

end UnipotentLaw

section TestPoint

open UnramifiedWhittaker NumberField.InfinitePlace

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}

private theorem componentMatrix_eq_of_glFin_eq {x y : AdelicGL2 (𝓞 K) K} (h : glFin (𝓞 K) K x = glFin (𝓞 K) K y)
    (v : HeightOneSpectrum (𝓞 K)) : componentMatrix v x = componentMatrix v y := by
  unfold componentMatrix
  rw [h]

end TestPoint

section SeriesCoefficient

open NumberField.InfinitePlace

private noncomputable def unipotentInf (y : InfiniteAdeleRing K) : AdelicGL2 (𝓞 K) K :=
  unipotentGL2 (((y, 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K)

private theorem glFin_unipotentInf (y : InfiniteAdeleRing K) : glFin (𝓞 K) K (unipotentInf y) = 1 := by
  rw [unipotentInf, glFin_unipotentGL2]
  exact unipotentGL2_zero

private theorem glArch_unipotentInf (y : InfiniteAdeleRing K) : glArch (𝓞 K) K (unipotentInf y) = unipotentGL2 y := by
  rw [unipotentInf, glArch_unipotentGL2]

private theorem archComponent_glArch_unipotentGL2 (w : InfinitePlace K) (a : AdeleRing (𝓞 K) K) :
    ((AdelicLevel.archComponent K w (glArch (𝓞 K) K (unipotentGL2 a)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) = !![1, a.1 w; 0, 1] := by
  rw [glArch_unipotentGL2]
  ext i j
  rw [AdelicLevel.archComponent_apply, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem realComponent_unipotentGL2_mul (w : InfinitePlace K) (hw : w.IsReal) (a : AdeleRing (𝓞 K) K)
    (g : AdelicGL2 (𝓞 K) K) :
    realComponent w hw (unipotentGL2 a * g) =
      ArchR.unip (Completion.ringEquivRealOfIsReal hw (a.1 w)) * realComponent w hw g := by
  rw [realComponent_eq_map, realComponent_eq_map, map_mul, map_mul, Units.val_mul, ← RingEquiv.coe_toRingHom,
    Matrix.map_mul, archComponent_glArch_unipotentGL2, ArchR.unip]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem complexComponent_unipotentGL2_mul (w : InfinitePlace K) (hw : w.IsComplex) (a : AdeleRing (𝓞 K) K)
    (g : AdelicGL2 (𝓞 K) K) :
    complexComponent w hw (unipotentGL2 a * g) =
      ArchC.unip (Completion.ringEquivComplexOfIsComplex hw (a.1 w)) * complexComponent w hw g := by
  rw [complexComponent_eq_map, complexComponent_eq_map, map_mul, map_mul, Units.val_mul,
    ← RingEquiv.coe_toRingHom, Matrix.map_mul, archComponent_glArch_unipotentGL2, ArchC.unip]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end SeriesCoefficient

section FiniteGauss
section Structure
end Structure
section Quotient
end Quotient
end FiniteGauss

section AbstractDescent
end AbstractDescent

section AbstractGauss
end AbstractGauss

section LocalDescent
end LocalDescent

section ProductFormula
end ProductFormula

section LocalData
end LocalData

section GaussCoefficient

open scoped Classical

open scoped WithZero
p2m_open "LanglandsTunnell.TateLocal NumberField.StandardAddChar NumberField.InfinitePlace AutomorphicForm.GaussTwist"

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

private theorem globalPoints_unipotentGL2 (ξ : K) :
    globalPoints (𝓞 K) K (unipotentGL2 ξ) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

end GaussCoefficient

section GaussNonvanishing
end GaussNonvanishing

section FixedVectorAt
end FixedVectorAt

end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section
namespace WhittakerFirstTerm
end WhittakerFirstTerm
end

noncomputable section
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section WhittakerFibre
end WhittakerFibre
end LanglandsTunnell.Converse.CuspSynthesis
end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section BoxTwist
end BoxTwist
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section EigenClauses

open AutomorphicForm.SmoothCusp FiniteWhittaker
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

private theorem epsChar_mul_of_forall_compAt_eq_one (d : JLData K S epsS ω) {ρ : AdelicGL2 (𝓞 K) K}
    (hρ : ∀ w ∈ S, compAt w ρ = 1) (g : AdelicGL2 (𝓞 K) K) : d.epsChar (g * ρ) = d.epsChar g := by
  have h : ∀ w : ↥S, componentMatrix w.1 (g * ρ) = componentMatrix w.1 g := fun w => by
    show ((compAt w.1 (g * ρ) : GL (Fin 2) (w.1.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion K))
      = ((compAt w.1 g : GL (Fin 2) (w.1.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion K))
    rw [map_mul, hρ w.1 w.2, mul_one]
  unfold JLData.epsChar
  exact if_congr (by simp only [MemZK0At, h]) (by simp only [h]) rfl

end EigenClauses

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis
end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section RationalAssembly
end RationalAssembly
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section BorelInvariance
end BorelInvariance
end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section DualSeries
end DualSeries
end LanglandsTunnell.Converse.CuspSynthesis
end

noncomputable section
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section SOrderCharacters
end SOrderCharacters
end LanglandsTunnell.Converse.CuspSynthesis
end

noncomputable section
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section OnePlaceNorm
end OnePlaceNorm
end LanglandsTunnell.Converse.CuspSynthesis
end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section UnfoldingModel
end UnfoldingModel
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section UnfoldingSums
end UnfoldingSums
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section UnfoldingConstant
end UnfoldingConstant
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section BochnerUnfolding
end BochnerUnfolding
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section TorusSeparation
end TorusSeparation
section TorusCharacter
end TorusCharacter
section TorusComparison
end TorusComparison
end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "AdelicDock LocalGL2 UnramifiedWhittaker LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LocalWhittaker"
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal NumberField.AdelicVolume
open MeasureTheory
open scoped WithZero Classical

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

namespace FiniteWhittaker

variable {K : Type} [Field K] [NumberField K]

section ZetaFactor
end ZetaFactor

section Central
end Central

section Vanishing
end Vanishing

section Reading
end Reading

section Translate

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}

private theorem wf_mul_of_glFin_mem_top (dF : FinWhittakerDatum K S Pi) (x : AdelicGL2 (𝓞 K) K)
    {y : AdelicGL2 (𝓞 K) K} (hy : glFin (𝓞 K) K y ∈ finiteLevelOne (𝓞 K) K ⊤) : dF.Wf (x * y) = dF.Wf x := by
  have hfin : glFin (𝓞 K) K (x * y) = glFin (𝓞 K) K (x * finEmbed (𝓞 K) K (glFin (𝓞 K) K y)) := by
    rw [map_mul, map_mul, glFin_finEmbed]
  rw [dF.finite_dependent _ _ hfin]
  refine wf_mul_of_mem_integral dF x (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [mem_levelOne_iff, glFin_finEmbed]
    exact hy
  · exact (mem_finiteAdelicGL2Subgroup_iff K _).mpr (glArch_finEmbed (𝓞 K) K _)

end Translate

end FiniteWhittaker

end

noncomputable section
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace ArchUnfold
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.ArchUnfold
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace ArchDatumR
p2m_export "LanglandsTunnell.Converse.ArchDatumR" "W unip_law decay_top smooth central_law mk exists_W_eq_fderivWithin_mul norm_iteratedFDerivWithin_diagOne_le"
p2m_open "LanglandsTunnell.Converse.ArchDatumR LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.ArchDatumR
end

noncomputable section
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section Regrouping
end Regrouping
end LanglandsTunnell.Converse.CuspSynthesis
end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section TorusUnfolding
end TorusUnfolding
end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section IntegrandContinuity
end IntegrandContinuity
end LanglandsTunnell.Converse.CuspSynthesis
end

noncomputable section
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section BadPlaceKernel
end BadPlaceKernel
end LanglandsTunnell.Converse.CuspSynthesis
end

noncomputable section
namespace LocalIwasawa
end LocalIwasawa
namespace FiniteWhittaker
section IntegralComponents
end IntegralComponents
end FiniteWhittaker
end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section DualCentre
end DualCentre
end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section
namespace FiniteWhittaker
section WeylCollapse
end WeylCollapse
end FiniteWhittaker
end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section CutInversion
end CutInversion
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section ComparisonAssembly
end ComparisonAssembly
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section ArchInclusionComponents
end ArchInclusionComponents
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section TorusPointContinuity
end TorusPointContinuity
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section Witnesses

open AutomorphicForm.SmoothCusp FiniteWhittaker
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

private theorem abs_det_realComponent (w : InfinitePlace K) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) :
    |(realComponent w hw g).det| = NumberField.AdelicVolume.archDetNorm w g := by
  rw [realComponent_eq_map, ← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    RingEquiv.coe_toRingHom, NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    NumberField.AdelicVolume.archDetNorm,
    ← Real.norm_eq_abs]
  exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
    (map_zero _) _

private theorem norm_det_complexComponent (w : InfinitePlace K) (hw : w.IsComplex) (g : AdelicGL2 (𝓞 K) K) :
    ‖(complexComponent w hw g).det‖ = NumberField.AdelicVolume.archDetNorm w g := by
  rw [complexComponent_eq_map, ← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    RingEquiv.coe_toRingHom, NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply,
    NumberField.AdelicVolume.archDetNorm]
  exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

end Witnesses

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section Conjuncts
end Conjuncts
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section WeightConjunct
end WeightConjunct
end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section TwistTransport

open MeasureTheory AutomorphicForm NumberField.TateGlobal

variable {K : Type} [Field K] [NumberField K]

private theorem det_unipotentGL2' (x : AdeleRing (𝓞 K) K) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  ext
  simp [Matrix.det_fin_two_of]

end TwistTransport

end LanglandsTunnell.Converse.CuspSynthesis

end

noncomputable section
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section TwistPins
end TwistPins
end LanglandsTunnell.Converse.CuspSynthesis
end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
section TwistedConjunct
end TwistedConjunct
end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section SliceCoefficients

open AutomorphicForm.WindowedSiegel

section SliceCoefficientsGeneric

variable {E : Type*} [Field E]

private theorem sliceCoef_unip_eq (b : E) :
    (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) E) = 1 + b • Matrix.single 0 1 (1 : E) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single, Matrix.one_apply]

private theorem sliceCoef_smul_single_eq (c : E) :
    c • Matrix.single 0 1 (1 : E) = (!![0, c; 0, 0] : Matrix (Fin 2) (Fin 2) E) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem sliceCoef_conj_apply (R : Matrix (Fin 2) (Fin 2) E) (c : E) (i j : Fin 2) :
    (R⁻¹ * (c • Matrix.single 0 1 (1 : E)) * R : Matrix (Fin 2) (Fin 2) E) i j
      = R.det⁻¹ * (R.adjugate i 0 * (c * R 1 j)) := by
  rw [sliceCoef_smul_single_eq, Matrix.inv_def, Ring.inverse_eq_inv]
  simp only [Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem sliceCoef_trace_conj (R : Matrix (Fin 2) (Fin 2) E) (hR : R.det ≠ 0) (c : E) :
    (R⁻¹ * (c • Matrix.single 0 1 (1 : E)) * R).trace = 0 := by
  rw [Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv R (isUnit_iff_ne_zero.mpr hR), one_mul, Matrix.trace_smul,
    Matrix.trace_single_eq_of_ne, smul_zero]
  decide

private theorem sliceCoef_conj_unip_mul (R : Matrix (Fin 2) (Fin 2) E) (b c : E) :
    ((!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) E) * R)⁻¹ * (c • Matrix.single 0 1 (1 : E)) * (!![1, b; 0, 1] * R)
      = R⁻¹ * (c • Matrix.single 0 1 (1 : E)) * R := by
  have hinv : (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) E)⁻¹ = !![1, -b; 0, 1] := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp
  have hcomm : (!![1, -b; 0, 1] : Matrix (Fin 2) (Fin 2) E) * (c • Matrix.single 0 1 (1 : E)) * !![1, b; 0, 1]
      = c • Matrix.single 0 1 (1 : E) := by
    rw [sliceCoef_smul_single_eq, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp
  rw [Matrix.mul_inv_rev, hinv]
  calc R⁻¹ * !![1, -b; 0, 1] * (c • Matrix.single 0 1 (1 : E)) * (!![1, b; 0, 1] * R)
      = R⁻¹ * (!![1, -b; 0, 1] * (c • Matrix.single 0 1 (1 : E)) * !![1, b; 0, 1]) * R := by
        simp only [Matrix.mul_assoc]
    _ = R⁻¹ * (c • Matrix.single 0 1 (1 : E)) * R := by rw [hcomm]

private theorem sliceCoef_conj_unip_eq (R : Matrix (Fin 2) (Fin 2) E) (hR : R.det ≠ 0) (c : E) :
    R⁻¹ * !![1, c; 0, 1] * R = 1 + R⁻¹ * (c • Matrix.single 0 1 (1 : E)) * R := by
  rw [sliceCoef_unip_eq, mul_add, add_mul, mul_one, Matrix.nonsing_inv_mul R (isUnit_iff_ne_zero.mpr hR)]

private theorem sliceCoef_conj_mul_smul (R : Matrix (Fin 2) (Fin 2) E) (t c : E) :
    R⁻¹ * ((t * c) • Matrix.single 0 1 (1 : E)) * R = t • (R⁻¹ * (c • Matrix.single 0 1 (1 : E)) * R) := by
  rw [mul_smul, Matrix.mul_smul, Matrix.smul_mul]

private theorem sliceCoef_conj_real_smul (R : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) (c : ℂ) :
    R⁻¹ * ((t • c) • Matrix.single 0 1 (1 : ℂ)) * R = t • (R⁻¹ * (c • Matrix.single 0 1 (1 : ℂ)) * R) := by
  calc R⁻¹ * ((t • c) • Matrix.single 0 1 (1 : ℂ)) * R
      = R⁻¹ * (t • (c • Matrix.single 0 1 (1 : ℂ))) * R := by rw [smul_assoc]
    _ = t • (R⁻¹ * (c • Matrix.single 0 1 (1 : ℂ))) * R := congrArg (· * R) (Matrix.mul_smul _ _ _)
    _ = t • (R⁻¹ * (c • Matrix.single 0 1 (1 : ℂ)) * R) := Matrix.smul_mul _ _ _

end SliceCoefficientsGeneric

section SliceCoefficientsBound

variable {E : Type*} [NormedField E]

private theorem sliceCoef_norm_conj_apply_le (R : Matrix (Fin 2) (Fin 2) E) (c : E) (i j : Fin 2) :
    ‖(R⁻¹ * (c • Matrix.single 0 1 (1 : E)) * R : Matrix (Fin 2) (Fin 2) E) i j‖ ≤ ‖c‖ * rowNormSq R / ‖R.det‖ := by
  rw [sliceCoef_conj_apply, norm_mul, norm_inv, norm_mul, norm_mul, div_eq_mul_inv]
  have hrow : ‖R.adjugate i 0‖ * ‖R 1 j‖ ≤ rowNormSq R := by
    unfold rowNormSq
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;>
      nlinarith [norm_nonneg (R 1 0), norm_nonneg (R 1 1), sq_nonneg (‖R 1 0‖ - ‖R 1 1‖),
        sq_nonneg ‖R 1 0‖, sq_nonneg ‖R 1 1‖]
  calc ‖R.det‖⁻¹ * (‖R.adjugate i 0‖ * (‖c‖ * ‖R 1 j‖))
      = ‖c‖ * (‖R.adjugate i 0‖ * ‖R 1 j‖) * ‖R.det‖⁻¹ := by ring
    _ ≤ ‖c‖ * rowNormSq R * ‖R.det‖⁻¹ := by gcongr

end SliceCoefficientsBound

private noncomputable abbrev archOf (v : mixedEmbedding.mixedSpace K) : InfiniteAdeleRing K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm v

private noncomputable def sliceCurve (v : mixedEmbedding.mixedSpace K) (h : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    GL (Fin 2) (InfiniteAdeleRing K) :=
  (glArch (𝓞 K) K h)⁻¹ * unipotentGL2 (archOf (t • v)) * glArch (𝓞 K) K h

open NumberField.InfinitePlace in
private theorem sliceCoef_coord_archOf_real (w : InfinitePlace K) (hw : w.IsReal) (v : mixedEmbedding.mixedSpace K) :
    Completion.ringEquivRealOfIsReal hw (archOf v w) = v.1 ⟨w, hw⟩ := by
  have h := (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply v
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
  rw [Completion.ringEquivRealOfIsReal_apply]
  exact congrFun (congrArg Prod.fst h) ⟨w, hw⟩

open NumberField.InfinitePlace in
private theorem sliceCoef_coord_archOf_complex (w : InfinitePlace K) (hw : w.IsComplex)
    (v : mixedEmbedding.mixedSpace K) :
    Completion.ringEquivComplexOfIsComplex hw (archOf v w) = v.2 ⟨w, hw⟩ := by
  have h := (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply v
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
  rw [Completion.ringEquivComplexOfIsComplex_apply]
  exact congrFun (congrArg Prod.snd h) ⟨w, hw⟩

open NumberField.InfinitePlace in
private theorem sliceCoef_archOf_apply_real (v : mixedEmbedding.mixedSpace K) (w : InfinitePlace K) (hw : w.IsReal) :
    archOf v w = (Completion.ringEquivRealOfIsReal hw).symm (v.1 ⟨w, hw⟩) :=
  (RingEquiv.eq_symm_apply _).mpr (sliceCoef_coord_archOf_real w hw v)

open NumberField.InfinitePlace in
private theorem sliceCoef_archOf_apply_complex (v : mixedEmbedding.mixedSpace K) (w : InfinitePlace K)
    (hw : w.IsComplex) :
    archOf v w = (Completion.ringEquivComplexOfIsComplex hw).symm (v.2 ⟨w, hw⟩) :=
  (RingEquiv.eq_symm_apply _).mpr (sliceCoef_coord_archOf_complex w hw v)

open NumberField.InfinitePlace in
private theorem sliceCoef_continuous_archOf (v : mixedEmbedding.mixedSpace K) :
    Continuous fun t : ℝ => archOf (t • v) := by
  show Continuous fun t : ℝ => (archOf (t • v) : ∀ w : InfinitePlace K, w.Completion)
  refine continuous_pi fun w => ?_
  by_cases hw : w.IsReal
  · simp only [sliceCoef_archOf_apply_real _ w hw, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    refine (Completion.isometryEquivRealOfIsReal hw).symm.continuous.comp ?_
    exact continuous_id.mul continuous_const
  · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    simp only [sliceCoef_archOf_apply_complex _ w hw', Prod.smul_snd, Pi.smul_apply]
    refine (Completion.isometryEquivComplexOfIsComplex hw').symm.continuous.comp ?_
    exact continuous_id.smul continuous_const

private theorem sliceCoef_realComponent_mul (w : InfinitePlace K) (hw : w.IsReal) (x y : AdelicGL2 (𝓞 K) K) :
    realComponent w hw (x * y) = realComponent w hw x * realComponent w hw y := by
  rw [realComponent_eq_map, realComponent_eq_map, realComponent_eq_map, map_mul, map_mul, Units.val_mul,
    ← RingEquiv.coe_toRingHom, Matrix.map_mul]

private theorem sliceCoef_complexComponent_mul (w : InfinitePlace K) (hw : w.IsComplex) (x y : AdelicGL2 (𝓞 K) K) :
    complexComponent w hw (x * y) = complexComponent w hw x * complexComponent w hw y := by
  rw [complexComponent_eq_map, complexComponent_eq_map, complexComponent_eq_map, map_mul, map_mul, Units.val_mul,
    ← RingEquiv.coe_toRingHom, Matrix.map_mul]

private theorem sliceCoef_realComponent_one (w : InfinitePlace K) (hw : w.IsReal) : realComponent w hw 1 = 1 := by
  rw [realComponent_eq_map, map_one, map_one, Units.val_one,
    Matrix.map_one (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (map_zero _) (map_one _)]

private theorem sliceCoef_complexComponent_one (w : InfinitePlace K) (hw : w.IsComplex) :
    complexComponent w hw 1 = 1 := by
  rw [complexComponent_eq_map, map_one, map_one, Units.val_one,
    Matrix.map_one (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) (map_zero _) (map_one _)]

private theorem sliceCoef_realComponent_inv (w : InfinitePlace K) (hw : w.IsReal) (x : AdelicGL2 (𝓞 K) K) :
    realComponent w hw x⁻¹ = (realComponent w hw x)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← sliceCoef_realComponent_mul, inv_mul_cancel, sliceCoef_realComponent_one]

private theorem sliceCoef_complexComponent_inv (w : InfinitePlace K) (hw : w.IsComplex) (x : AdelicGL2 (𝓞 K) K) :
    complexComponent w hw x⁻¹ = (complexComponent w hw x)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← sliceCoef_complexComponent_mul, inv_mul_cancel, sliceCoef_complexComponent_one]

open NumberField.InfinitePlace in
private theorem sliceCoef_height_real (w : InfinitePlace K) (hw : w.IsReal) (v : mixedEmbedding.mixedSpace K)
    (h : AdelicGL2 (𝓞 K) K) :
    mixedEmbedding.normAtPlace w v / localHeight (archComponent K w (glArch (𝓞 K) K h))
      = ‖v.1 ⟨w, hw⟩‖ * rowNormSq (realComponent w hw h) / ‖(realComponent w hw h).det‖ := by
  have hn : ∀ x : w.Completion, ‖Completion.ringEquivRealOfIsReal hw x‖ = ‖x‖ := fun x => by
    rw [Completion.ringEquivRealOfIsReal_apply]
    exact (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) x
  have hrow : rowNormSq (realComponent w hw h) =
      rowNormSq ((archComponent K w (glArch (𝓞 K) K h) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) := by
    rw [realComponent_eq_map]
    unfold rowNormSq
    simp only [Matrix.map_apply, hn]
  have hdet : ‖(realComponent w hw h).det‖ =
      ‖((archComponent K w (glArch (𝓞 K) K h) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det‖ := by
    rw [realComponent_eq_map, ← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      RingEquiv.coe_toRingHom, hn]
  rw [mixedEmbedding.normAtPlace_apply_of_isReal hw, hrow, hdet]
  unfold localHeight
  rw [div_div_eq_mul_div]

open NumberField.InfinitePlace in
private theorem sliceCoef_height_complex (w : InfinitePlace K) (hw : w.IsComplex) (v : mixedEmbedding.mixedSpace K)
    (h : AdelicGL2 (𝓞 K) K) :
    mixedEmbedding.normAtPlace w v / localHeight (archComponent K w (glArch (𝓞 K) K h))
      = ‖v.2 ⟨w, hw⟩‖ * rowNormSq (complexComponent w hw h) / ‖(complexComponent w hw h).det‖ := by
  have hn : ∀ x : w.Completion, ‖Completion.ringEquivComplexOfIsComplex hw x‖ = ‖x‖ := fun x => by
    rw [Completion.ringEquivComplexOfIsComplex_apply]
    exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
  have hrow : rowNormSq (complexComponent w hw h) =
      rowNormSq ((archComponent K w (glArch (𝓞 K) K h) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) := by
    rw [complexComponent_eq_map]
    unfold rowNormSq
    simp only [Matrix.map_apply, hn]
  have hdet : ‖(complexComponent w hw h).det‖ =
      ‖((archComponent K w (glArch (𝓞 K) K h) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det‖ := by
    rw [complexComponent_eq_map, ← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      RingEquiv.coe_toRingHom, hn]
  rw [mixedEmbedding.normAtPlace_apply_of_isComplex hw, hrow, hdet]
  unfold localHeight
  rw [div_div_eq_mul_div]

private theorem unipotentInf_mul_eq_mul_sliceCurve (v : mixedEmbedding.mixedSpace K) (h : AdelicGL2 (𝓞 K) K)
    (t : ℝ) :
    unipotentInf (archOf (t • v)) * h = h * AutomorphicForm.adelicArchGLIncl K (sliceCurve v h t) := by
  refine ext_of_glArch_of_componentMatrix ?_ fun w => componentMatrix_eq_of_glFin_eq ?_ w
  · rw [map_mul, map_mul, glArch_unipotentInf, AutomorphicForm.glArch_adelicArchGLIncl]
    simp only [sliceCurve, mul_assoc, mul_inv_cancel_left]
  · rw [map_mul, map_mul, glFin_unipotentInf, AutomorphicForm.glFin_adelicArchGLIncl, one_mul, mul_one]

private theorem sliceCoef_adelicArchGLIncl_sliceCurve (v : mixedEmbedding.mixedSpace K) (h : AdelicGL2 (𝓞 K) K)
    (t : ℝ) :
    AutomorphicForm.adelicArchGLIncl K (sliceCurve v h t) = h⁻¹ * (unipotentInf (archOf (t • v)) * h) := by
  rw [unipotentInf_mul_eq_mul_sliceCurve, inv_mul_cancel_left]

private theorem sliceCurve_zero (v : mixedEmbedding.mixedSpace K) (h : AdelicGL2 (𝓞 K) K) : sliceCurve v h 0 = 1 := by
  unfold sliceCurve
  rw [zero_smul, show archOf (0 : mixedEmbedding.mixedSpace K) = 0 from map_zero _, unipotentGL2_zero, mul_one,
    inv_mul_cancel]

private theorem continuous_adelicArchGLIncl_sliceCurve (v : mixedEmbedding.mixedSpace K) (h : AdelicGL2 (𝓞 K) K) :
    Continuous fun t : ℝ => AutomorphicForm.adelicArchGLIncl K (sliceCurve v h t) := by
  simp only [sliceCoef_adelicArchGLIncl_sliceCurve]
  refine continuous_const.mul (Continuous.mul ?_ continuous_const)
  have hy : Continuous fun t : ℝ =>
      (((archOf (t • v), 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) :=
    (sliceCoef_continuous_archOf v).prodMk continuous_const
  unfold unipotentInf
  exact (CuspRealizationCT.continuous_unipotentGL2 K).comp hy

private noncomputable def sliceCoefR (w : InfinitePlace K) (hw : w.IsReal) (v : mixedEmbedding.mixedSpace K)
    (h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) ℝ :=
  (realComponent w hw h)⁻¹ * (v.1 ⟨w, hw⟩ • Matrix.single 0 1 (1 : ℝ)) * realComponent w hw h

private noncomputable def sliceCoefC (w : InfinitePlace K) (hw : w.IsComplex) (v : mixedEmbedding.mixedSpace K)
    (h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) ℂ :=
  (complexComponent w hw h)⁻¹ * (v.2 ⟨w, hw⟩ • Matrix.single 0 1 (1 : ℂ)) * complexComponent w hw h

private theorem realComponent_sliceCurve (w : InfinitePlace K) (hw : w.IsReal) (v : mixedEmbedding.mixedSpace K)
    (h : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    realComponent w hw (AutomorphicForm.adelicArchGLIncl K (sliceCurve v h t)) = 1 + t • sliceCoefR w hw v h := by
  have hy : InfinitePlace.Completion.ringEquivRealOfIsReal hw
      ((((archOf (t • v), 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K).1 w)
        = t * v.1 ⟨w, hw⟩ := by
    rw [show (((archOf (t • v), 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K).1
        = archOf (t • v) from rfl, sliceCoef_coord_archOf_real]
    simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
  rw [sliceCoef_adelicArchGLIncl_sliceCurve, sliceCoef_realComponent_mul, sliceCoef_realComponent_inv, unipotentInf,
    realComponent_unipotentGL2_mul, hy, ArchR.unip, ← Matrix.mul_assoc,
    sliceCoef_conj_unip_eq _ (det_realComponent_ne_zero w hw h), sliceCoef_conj_mul_smul]
  rfl

private theorem complexComponent_sliceCurve (w : InfinitePlace K) (hw : w.IsComplex)
    (v : mixedEmbedding.mixedSpace K) (h : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    complexComponent w hw (AutomorphicForm.adelicArchGLIncl K (sliceCurve v h t)) = 1 + t • sliceCoefC w hw v h := by
  have hy : InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      ((((archOf (t • v), 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K).1 w)
        = t • v.2 ⟨w, hw⟩ := by
    rw [show (((archOf (t • v), 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K).1
        = archOf (t • v) from rfl, sliceCoef_coord_archOf_complex]
    simp only [Prod.smul_snd, Pi.smul_apply]
  rw [sliceCoef_adelicArchGLIncl_sliceCurve, sliceCoef_complexComponent_mul, sliceCoef_complexComponent_inv,
    unipotentInf, complexComponent_unipotentGL2_mul, hy, ArchC.unip, ← Matrix.mul_assoc,
    sliceCoef_conj_unip_eq _ (det_complexComponent_ne_zero w hw h), sliceCoef_conj_real_smul]
  rfl

private theorem continuous_sliceCoefR (w : InfinitePlace K) (hw : w.IsReal) (v : mixedEmbedding.mixedSpace K) :
    Continuous (sliceCoefR w hw v) := by
  have hR : Continuous (realComponent w hw) := continuous_realComponent w hw
  have hinv : Continuous fun h : AdelicGL2 (𝓞 K) K => (realComponent w hw h)⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    exact (hR.matrix_det.inv₀ fun h => det_realComponent_ne_zero w hw h).smul hR.matrix_adjugate
  unfold sliceCoefR
  exact (hinv.matrix_mul continuous_const).matrix_mul hR

private theorem continuous_sliceCoefC (w : InfinitePlace K) (hw : w.IsComplex) (v : mixedEmbedding.mixedSpace K) :
    Continuous (sliceCoefC w hw v) := by
  have hR : Continuous (complexComponent w hw) := continuous_complexComponent w hw
  have hinv : Continuous fun h : AdelicGL2 (𝓞 K) K => (complexComponent w hw h)⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    exact (hR.matrix_det.inv₀ fun h => det_complexComponent_ne_zero w hw h).smul hR.matrix_adjugate
  unfold sliceCoefC
  exact (hinv.matrix_mul continuous_const).matrix_mul hR

private theorem sliceCoefR_unipotentGL2_mul (w : InfinitePlace K) (hw : w.IsReal) (v : mixedEmbedding.mixedSpace K)
    (a : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K) :
    sliceCoefR w hw v (unipotentGL2 a * h) = sliceCoefR w hw v h := by
  unfold sliceCoefR
  rw [realComponent_unipotentGL2_mul, ArchR.unip]
  exact sliceCoef_conj_unip_mul _ _ _

private theorem sliceCoefC_unipotentGL2_mul (w : InfinitePlace K) (hw : w.IsComplex)
    (v : mixedEmbedding.mixedSpace K) (a : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K) :
    sliceCoefC w hw v (unipotentGL2 a * h) = sliceCoefC w hw v h := by
  unfold sliceCoefC
  rw [complexComponent_unipotentGL2_mul, ArchC.unip]
  exact sliceCoef_conj_unip_mul _ _ _

private theorem trace_sliceCoefR (w : InfinitePlace K) (hw : w.IsReal) (v : mixedEmbedding.mixedSpace K)
    (h : AdelicGL2 (𝓞 K) K) : (sliceCoefR w hw v h).trace = 0 := by
  unfold sliceCoefR
  exact sliceCoef_trace_conj _ (det_realComponent_ne_zero w hw h) _

private theorem trace_sliceCoefC (w : InfinitePlace K) (hw : w.IsComplex) (v : mixedEmbedding.mixedSpace K)
    (h : AdelicGL2 (𝓞 K) K) : (sliceCoefC w hw v h).trace = 0 := by
  unfold sliceCoefC
  exact sliceCoef_trace_conj _ (det_complexComponent_ne_zero w hw h) _

private theorem abs_sliceCoefR_apply_le (w : InfinitePlace K) (hw : w.IsReal) (v : mixedEmbedding.mixedSpace K)
    (h : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    |sliceCoefR w hw v h i j| ≤
      mixedEmbedding.normAtPlace w v / localHeight (archComponent K w (glArch (𝓞 K) K h)) := by
  rw [sliceCoef_height_real w hw v h, ← Real.norm_eq_abs]
  unfold sliceCoefR
  exact sliceCoef_norm_conj_apply_le _ _ i j

private theorem norm_sliceCoefC_apply_le (w : InfinitePlace K) (hw : w.IsComplex) (v : mixedEmbedding.mixedSpace K)
    (h : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    ‖sliceCoefC w hw v h i j‖ ≤
      mixedEmbedding.normAtPlace w v / localHeight (archComponent K w (glArch (𝓞 K) K h)) := by
  rw [sliceCoef_height_complex w hw v h]
  unfold sliceCoefC
  exact sliceCoef_norm_conj_apply_le _ _ i j

end SliceCoefficients

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.FiniteWhittaker"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section TermwiseDerivative

open Topology
open scoped Classical

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

open scoped Matrix

private theorem hasDerivAt_comp_coords {F : (Fin 2 → Fin 2 → ℝ) → ℂ} {s : Set (Fin 2 → Fin 2 → ℝ)} (hs : IsOpen s)
    (hF : DifferentiableOn ℝ F s) {m : ℝ → Fin 2 → Fin 2 → ℝ} {m' : Fin 2 → Fin 2 → ℝ} {t : ℝ}
    (hm : HasDerivAt m m' t) (ht : m t ∈ s) :
    HasDerivAt (fun u => F (m u)) (fderivWithin ℝ F s (m t) m') t := by
  have h1 : HasFDerivAt F (fderivWithin ℝ F s (m t)) (m t) :=
    ((hF (m t) ht).hasFDerivWithinAt).hasFDerivAt (hs.mem_nhds ht)
  first | exact h1.comp_hasDerivAt t hm | simpa using h1.comp_hasDerivAt t hm | simpa +zetaDelta using h1.comp_hasDerivAt t hm

private theorem hasDerivAt_comp_coords_complex {F : (Fin 2 → Fin 2 → ℂ) → ℂ} {s : Set (Fin 2 → Fin 2 → ℂ)}
    (hs : IsOpen s) (hF : DifferentiableOn ℝ F s) {m : ℝ → Fin 2 → Fin 2 → ℂ} {m' : Fin 2 → Fin 2 → ℂ} {t : ℝ}
    (hm : HasDerivAt m m' t) (ht : m t ∈ s) :
    HasDerivAt (fun u => F (m u)) (fderivWithin ℝ F s (m t) m') t := by
  have h1 : HasFDerivAt F (fderivWithin ℝ F s (m t)) (m t) :=
    ((hF (m t) ht).hasFDerivWithinAt).hasFDerivAt (hs.mem_nhds ht)
  first | exact h1.comp_hasDerivAt t hm | simpa using h1.comp_hasDerivAt t hm | simpa +zetaDelta using h1.comp_hasDerivAt t hm

private theorem hasDerivAt_coords_mul_left (R : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {M' : Matrix (Fin 2) (Fin 2) ℝ} {t : ℝ} (hM : HasDerivAt (fun u => Matrix.of.symm (M u)) (Matrix.of.symm M') t) :
    HasDerivAt (fun u => Matrix.of.symm (R * M u)) (Matrix.of.symm (R * M')) t := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  have hk : ∀ k, HasDerivAt (fun u => Matrix.of.symm (M u) k j) (Matrix.of.symm M' k j) t := fun k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hM k) j
  have hfun : (fun u => Matrix.of.symm (R * M u) i j) = fun u => ∑ k, R i k * Matrix.of.symm (M u) k j :=
    funext fun u => by simp only [Matrix.of_symm_apply, Matrix.mul_apply]
  have hval : Matrix.of.symm (R * M') i j = ∑ k, R i k * Matrix.of.symm M' k j := by
    simp only [Matrix.of_symm_apply, Matrix.mul_apply]
  rw [hfun, hval]
  exact HasDerivAt.fun_sum fun k _ => (hk k).const_mul (R i k)

private theorem hasDerivAt_coords_mul_left_complex (R : Matrix (Fin 2) (Fin 2) ℂ) {M : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    {M' : Matrix (Fin 2) (Fin 2) ℂ} {t : ℝ} (hM : HasDerivAt (fun u => Matrix.of.symm (M u)) (Matrix.of.symm M') t) :
    HasDerivAt (fun u => Matrix.of.symm (R * M u)) (Matrix.of.symm (R * M')) t := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  have hk : ∀ k, HasDerivAt (fun u => Matrix.of.symm (M u) k j) (Matrix.of.symm M' k j) t := fun k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hM k) j
  have hfun : (fun u => Matrix.of.symm (R * M u) i j) = fun u => ∑ k, R i k * Matrix.of.symm (M u) k j :=
    funext fun u => by simp only [Matrix.of_symm_apply, Matrix.mul_apply]
  have hval : Matrix.of.symm (R * M') i j = ∑ k, R i k * Matrix.of.symm M' k j := by
    simp only [Matrix.of_symm_apply, Matrix.mul_apply]
  rw [hfun, hval]
  exact HasDerivAt.fun_sum fun k _ => (hk k).const_mul (R i k)

private theorem linear_coords_mul_eq_sum (L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ) (g X : Matrix (Fin 2) (Fin 2) ℝ) :
    L (Matrix.of.symm (g * X)) =
      ∑ ι : Fin 2 × Fin 2, ((X ι.1 ι.2 : ℝ) : ℂ) * L (Matrix.of.symm (g * Matrix.single ι.1 ι.2 (1 : ℝ))) := by
  have hX : X = ∑ ι : Fin 2 × Fin 2, X ι.1 ι.2 • Matrix.single ι.1 ι.2 (1 : ℝ) := by
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.smul_single]
  have hsum : Matrix.of.symm (g * X) =
      ∑ ι : Fin 2 × Fin 2, X ι.1 ι.2 • Matrix.of.symm (g * Matrix.single ι.1 ι.2 (1 : ℝ)) := by
    conv_lhs => rw [hX, Finset.mul_sum]
    simp only [Matrix.mul_smul]
    rfl
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [map_smul, Complex.real_smul]

private theorem linear_coords_mul_eq_sum_complex (L : (Fin 2 → Fin 2 → ℂ) →L[ℝ] ℂ) (g X : Matrix (Fin 2) (Fin 2) ℂ) :
    L (Matrix.of.symm (g * X)) =
      ∑ ι : Fin 2 × Fin 2,
        (((X ι.1 ι.2).re : ℂ) * L (Matrix.of.symm (g * Matrix.single ι.1 ι.2 (1 : ℂ))) +
          ((X ι.1 ι.2).im : ℂ) * L (Matrix.of.symm (g * Matrix.single ι.1 ι.2 Complex.I))) := by
  have hX : X = ∑ ι : Fin 2 × Fin 2,
      ((X ι.1 ι.2).re • Matrix.single ι.1 ι.2 (1 : ℂ) + (X ι.1 ι.2).im • Matrix.single ι.1 ι.2 Complex.I) := by
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, Complex.real_smul]
    split_ifs <;> simp [Complex.re_add_im]
  have hsum : Matrix.of.symm (g * X) =
      ∑ ι : Fin 2 × Fin 2,
        ((X ι.1 ι.2).re • Matrix.of.symm (g * Matrix.single ι.1 ι.2 (1 : ℂ)) +
          (X ι.1 ι.2).im • Matrix.of.symm (g * Matrix.single ι.1 ι.2 Complex.I)) := by
    conv_lhs => rw [hX, Finset.mul_sum]
    simp only [Matrix.mul_add]
    simp only [Matrix.mul_smul, mul_smul_comm]
    rfl
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

private theorem hasDerivAt_det_fin_two {M : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {M' : Matrix (Fin 2) (Fin 2) ℝ} {t : ℝ}
    (hM : HasDerivAt (fun u => Matrix.of.symm (M u)) (Matrix.of.symm M') t) (hdet : (M t).det ≠ 0) :
    HasDerivAt (fun u => (M u).det) ((M t).det * ((M t)⁻¹ * M').trace) t := by
  have h : ∀ i j, HasDerivAt (fun u => M u i j) (M' i j) t := fun i j => by
    have := (hasDerivAt_pi.1 ((hasDerivAt_pi.1 hM) i)) j
    simpa using this
  have hd : HasDerivAt (fun u => (M u).det)
      (M' 0 0 * M t 1 1 + M t 0 0 * M' 1 1 - (M' 0 1 * M t 1 0 + M t 0 1 * M' 1 0)) t := by
    simp only [Matrix.det_fin_two]
    exact ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0))
  convert hd using 1
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two] at *
  simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, smul_eq_mul, Ring.inverse_eq_inv']
  field_simp
  ring

private theorem hasDerivAt_det_fin_two_complex {M : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {M' : Matrix (Fin 2) (Fin 2) ℂ}
    {t : ℝ} (hM : HasDerivAt (fun u => Matrix.of.symm (M u)) (Matrix.of.symm M') t) (hdet : (M t).det ≠ 0) :
    HasDerivAt (fun u => (M u).det) ((M t).det * ((M t)⁻¹ * M').trace) t := by
  have h : ∀ i j, HasDerivAt (fun u => M u i j) (M' i j) t := fun i j => by
    have := (hasDerivAt_pi.1 ((hasDerivAt_pi.1 hM) i)) j
    simpa using this
  have hd : HasDerivAt (fun u => (M u).det)
      (M' 0 0 * M t 1 1 + M t 0 0 * M' 1 1 - (M' 0 1 * M t 1 0 + M t 0 1 * M' 1 0)) t := by
    simp only [Matrix.det_fin_two]
    exact ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0))
  convert hd using 1
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two] at *
  simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, smul_eq_mul, Ring.inverse_eq_inv']
  field_simp
  ring

private theorem hasDerivAt_inv_sqrt_abs {x : ℝ → ℝ} {x' t : ℝ} (hx : HasDerivAt x x' t) (h0 : x t ≠ 0) :
    HasDerivAt (fun u => (Real.sqrt |x u|)⁻¹) (-(1 / 2 * (x' / x t)) * (Real.sqrt |x t|)⁻¹) t := by
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  ·
    have hev : (fun u => (Real.sqrt |x u|)⁻¹) =ᶠ[nhds t] fun u => (Real.sqrt (-x u))⁻¹ := by
      filter_upwards [hx.continuousAt.eventually (gt_mem_nhds hneg)] with u hu
      rw [abs_of_neg hu]
    have hm : HasDerivAt (fun u => -x u) (-x') t := hx.neg
    have hmt : -x t ≠ 0 := neg_ne_zero.2 h0
    have hsqrt : HasDerivAt (fun u => Real.sqrt (-x u)) (1 / (2 * Real.sqrt (-x t)) * -x') t := by
      have := (Real.hasDerivAt_sqrt hmt).comp t hm
      simpa [Function.comp_def] using this
    have hs0 : Real.sqrt (-x t) ≠ 0 := Real.sqrt_ne_zero'.2 (neg_pos.2 hneg)
    refine (hsqrt.inv hs0).congr_of_eventuallyEq hev |>.congr_deriv ?_
    have hsq : Real.sqrt (-x t) ^ 2 = -x t := Real.sq_sqrt (neg_pos.2 hneg).le
    rw [abs_of_neg hneg]
    field_simp
    rw [hsq]
    ring
  · have hev : (fun u => (Real.sqrt |x u|)⁻¹) =ᶠ[nhds t] fun u => (Real.sqrt (x u))⁻¹ := by
      filter_upwards [hx.continuousAt.eventually (lt_mem_nhds hpos)] with u hu
      rw [abs_of_pos hu]
    have hsqrt : HasDerivAt (fun u => Real.sqrt (x u)) (1 / (2 * Real.sqrt (x t)) * x') t := by
      have := (Real.hasDerivAt_sqrt h0).comp t hx
      simpa [Function.comp_def] using this
    have hs0 : Real.sqrt (x t) ≠ 0 := Real.sqrt_ne_zero'.2 hpos
    refine (hsqrt.inv hs0).congr_of_eventuallyEq hev |>.congr_deriv ?_
    have hsq : Real.sqrt (x t) ^ 2 = x t := Real.sq_sqrt hpos.le
    rw [abs_of_pos hpos]
    field_simp
    rw [hsq]
    ring

private theorem hasDerivAt_inv_norm {z : ℝ → ℂ} {z' : ℂ} {t : ℝ} (hz : HasDerivAt z z' t) (h0 : z t ≠ 0) :
    HasDerivAt (fun u => ‖z u‖⁻¹) (-(z' / z t).re * ‖z t‖⁻¹) t := by
  have hn0 : ‖z t‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hnorm : HasDerivAt (fun u => ‖z u‖) ((z' / z t).re * ‖z t‖) t := by
    have hsq : HasDerivAt (fun u => ‖z u‖ ^ 2) (2 * (z t * (starRingEnd ℂ) z').re) t := by
      have h := hz.norm_sq
      convert h using 1
      simp [real_inner_eq_re_inner, mul_comm]
    have hsqrt : HasDerivAt (fun u => Real.sqrt (‖z u‖ ^ 2)) (1 / (2 * Real.sqrt (‖z t‖ ^ 2))
        * (2 * (z t * (starRingEnd ℂ) z').re)) t := by
      have := (Real.hasDerivAt_sqrt (by positivity)).comp t hsq
      simpa [Function.comp_def] using this
    have heq : (fun u => Real.sqrt (‖z u‖ ^ 2)) = fun u => ‖z u‖ := by
      funext u
      exact Real.sqrt_sq (norm_nonneg _)
    rw [heq] at hsqrt
    convert hsqrt using 1
    rw [Real.sqrt_sq (norm_nonneg _)]
    have hre : (z' / z t).re * ‖z t‖ ^ 2 = (z t * (starRingEnd ℂ) z').re := by
      rw [Complex.div_re, ← Complex.normSq_eq_norm_sq]
      have hns : Complex.normSq (z t) ≠ 0 := Complex.normSq_pos.2 h0 |>.ne'
      field_simp
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    field_simp
    nlinarith [hre, sq_nonneg ‖z t‖]
  have := hnorm.inv hn0
  convert this using 1 <;> try first | with_reducible_and_instances rfl | rfl
  field_simp

private noncomputable def cplxUnit (ι : (Fin 2 × Fin 2) × Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single ι.1.1 ι.1.2 (if ι.2 = 0 then (1 : ℂ) else Complex.I)

private noncomputable def cplxCoeff (D : Matrix (Fin 2) (Fin 2) ℂ) (ι : (Fin 2 × Fin 2) × Fin 2) : ℝ :=
  if ι.2 = 0 then (D ι.1.1 ι.1.2).re else (D ι.1.1 ι.1.2).im

private theorem compAt_adelicArchGLIncl_eq_one (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin 2) (InfiniteAdeleRing K)) :
    compAt v (adelicArchGLIncl K x) = 1 := by
  show finComponent (𝓞 K) K v (glFin (𝓞 K) K (adelicArchGLIncl K x)) = 1
  rw [glFin_adelicArchGLIncl, map_one]

private theorem epsChar_mul_adelicArchGLIncl (d : JLData K S epsS ω) (g : AdelicGL2 (𝓞 K) K)
    (x : GL (Fin 2) (InfiniteAdeleRing K)) : d.epsChar (g * adelicArchGLIncl K x) = d.epsChar g :=
  epsChar_mul_of_forall_compAt_eq_one d (fun v _ => compAt_adelicArchGLIncl_eq_one v x) g

private theorem wf_mul_adelicArchGLIncl (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K)
    (x : GL (Fin 2) (InfiniteAdeleRing K)) : dF.Wf (g * adelicArchGLIncl K x) = dF.Wf g :=
  dF.finite_dependent _ _ (by rw [map_mul, glFin_adelicArchGLIncl, mul_one])

private theorem realComponent_mul_termwise (w : InfinitePlace K) (hw : w.IsReal) (g g' : AdelicGL2 (𝓞 K) K) :
    realComponent w hw (g * g') = realComponent w hw g * realComponent w hw g' := by
  simp only [realComponent_eq_map, map_mul, Units.val_mul]
  rw [← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
    map_mul]

private theorem complexComponent_mul_termwise (w : InfinitePlace K) (hw : w.IsComplex) (g g' : AdelicGL2 (𝓞 K) K) :
    complexComponent w hw (g * g') = complexComponent w hw g * complexComponent w hw g' := by
  simp only [complexComponent_eq_map, map_mul, Units.val_mul]
  rw [← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
    map_mul]

private theorem realComponent_one_termwise (w : InfinitePlace K) (hw : w.IsReal) :
    realComponent w hw (1 : AdelicGL2 (𝓞 K) K) = 1 := by
  rw [realComponent_eq_map, map_one, map_one, Units.val_one, ← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply,
    map_one]

private theorem complexComponent_one_termwise (w : InfinitePlace K) (hw : w.IsComplex) :
    complexComponent w hw (1 : AdelicGL2 (𝓞 K) K) = 1 := by
  rw [complexComponent_eq_map, map_one, map_one, Units.val_one, ← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply,
    map_one]

private noncomputable def localFactor'
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  if hw : w.IsReal then
    (dR w hw).W (realComponent w hw g) * ((Real.sqrt |(realComponent w hw g).det| : ℝ) : ℂ)⁻¹
  else
    (dC w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).W
        (complexComponent w (InfinitePlace.not_isReal_iff_isComplex.mp hw) g) *
      ((‖(complexComponent w (InfinitePlace.not_isReal_iff_isComplex.mp hw) g).det‖ : ℝ) : ℂ)⁻¹

private theorem archW'_eq_prod_localFactor'
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) (g : AdelicGL2 (𝓞 K) K) :
    archW' archR archC dR dC g = ∏ w : InfinitePlace K, localFactor' archR archC dR dC w g := by
  unfold archW' archW archNormFactor localFactor'
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  by_cases hw : w.IsReal <;> simp [hw]

private theorem localFactor'_real
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) {w : InfinitePlace K} (hw : w.IsReal)
    (g : AdelicGL2 (𝓞 K) K) :
    localFactor' archR archC dR dC w g =
      (dR w hw).W (realComponent w hw g) * ((Real.sqrt |(realComponent w hw g).det| : ℝ) : ℂ)⁻¹ := by
  simp [localFactor', hw]

private theorem localFactor'_complex
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) {w : InfinitePlace K}
    (hw : w.IsComplex) (g : AdelicGL2 (𝓞 K) K) :
    localFactor' archR archC dR dC w g =
      (dC w hw).W (complexComponent w hw g) * ((‖(complexComponent w hw g).det‖ : ℝ) : ℂ)⁻¹ := by
  have hw' : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr hw
  simp [localFactor', hw']

private theorem localFactor'_of_eq_off
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    {dR dR₁ : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw)}
    {dC dC₁ : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)} {w₀ : InfinitePlace K}
    (hR : ∀ (w : InfinitePlace K) (hw : w.IsReal), w ≠ w₀ → dR₁ w hw = dR w hw)
    (hC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), w ≠ w₀ → dC₁ w hw = dC w hw) {w : InfinitePlace K}
    (hww : w ≠ w₀) (g : AdelicGL2 (𝓞 K) K) :
    localFactor' archR archC dR₁ dC₁ w g = localFactor' archR archC dR dC w g := by
  unfold localFactor'
  by_cases hw : w.IsReal
  · simp [hw, hR w hw hww]
  · simp [hw, hC w (InfinitePlace.not_isReal_iff_isComplex.mp hw) hww]

private theorem archW'_eq_prod_erase_mul
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    {dR dR₁ : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw)}
    {dC dC₁ : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)} {w₀ : InfinitePlace K}
    (hR : ∀ (w : InfinitePlace K) (hw : w.IsReal), w ≠ w₀ → dR₁ w hw = dR w hw)
    (hC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), w ≠ w₀ → dC₁ w hw = dC w hw) (g : AdelicGL2 (𝓞 K) K) :
    archW' archR archC dR₁ dC₁ g =
      (∏ w ∈ Finset.univ.erase w₀, localFactor' archR archC dR dC w g) * localFactor' archR archC dR₁ dC₁ w₀ g := by
  rw [archW'_eq_prod_localFactor', ← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
  congr 1
  exact Finset.prod_congr rfl fun w hw => localFactor'_of_eq_off archR archC hR hC (Finset.ne_of_mem_erase hw) g

private theorem seriesTerm_mul_adelicArchGLIncl (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) (dF : FinWhittakerDatum K S Pi)
    (q : AdelicGL2 (𝓞 K) K) (x : GL (Fin 2) (InfiniteAdeleRing K)) (α : Kˣ) :
    seriesTerm d archR archC dR dC dF (q * adelicArchGLIncl K x) α =
      d.a α * d.epsChar q * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * q) *
        ∏ w : InfinitePlace K,
          localFactor' archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * q * adelicArchGLIncl K x) := by
  unfold seriesTerm
  rw [← mul_assoc (globalPoints (𝓞 K) K (diagOne α)), epsChar_mul_adelicArchGLIncl, wf_mul_adelicArchGLIncl,
    ← archW'_eq_prod_localFactor']
  ring

private noncomputable def coefR {w : InfinitePlace K} (hw : w.IsReal) (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K))
    (DR : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (realComponent w hw (adelicArchGLIncl K (Γ t)))⁻¹ * DR t

private noncomputable def coefC {w : InfinitePlace K} (hw : w.IsComplex) (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K))
    (DC : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (complexComponent w hw (adelicArchGLIncl K (Γ t)))⁻¹ * DC t

private theorem coefR_zero {w : InfinitePlace K} (hw : w.IsReal) {Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K)}
    (hΓ₀ : Γ 0 = 1) (DR : ℝ → Matrix (Fin 2) (Fin 2) ℝ) : coefR hw Γ DR 0 = DR 0 := by
  simp [coefR, hΓ₀, realComponent_one_termwise]

private theorem coefC_zero {w : InfinitePlace K} (hw : w.IsComplex) {Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K)}
    (hΓ₀ : Γ 0 = 1) (DC : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : coefC hw Γ DC 0 = DC 0 := by
  simp [coefC, hΓ₀, complexComponent_one_termwise]

private theorem hasDerivAt_localFactor'_real
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) {w : InfinitePlace K} (hw : w.IsReal)
    (dRw : Fin 2 × Fin 2 → ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ArchDatumR (archR w' hw'))
    (hat : ∀ (ι : Fin 2 × Fin 2) (g : Matrix (Fin 2) (Fin 2) ℝ), g.det ≠ 0 →
      (dRw ι w hw).W g =
        fderivWithin ℝ (ArchR.asPi (dR w hw).W) ArchR.glSet (Matrix.of.symm g)
          (Matrix.of.symm (g * Matrix.single ι.1 ι.2 (1 : ℝ))))
    (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K)) (DR : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hDR : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Matrix.of.symm (realComponent w hw (adelicArchGLIncl K (Γ s))))
      (Matrix.of.symm (DR t)) t)
    (g : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => localFactor' archR archC dR dC w (g * adelicArchGLIncl K (Γ s)))
      ((∑ ι : Fin 2 × Fin 2, ((coefR hw Γ DR t ι.1 ι.2 : ℝ) : ℂ) *
          localFactor' archR archC (dRw ι) dC w (g * adelicArchGLIncl K (Γ t))) -
        ((1 / 2 * (coefR hw Γ DR t).trace : ℝ) : ℂ) * localFactor' archR archC dR dC w (g * adelicArchGLIncl K (Γ t)))
      t := by
  set R : Matrix (Fin 2) (Fin 2) ℝ := realComponent w hw g with hRdef
  set M : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun s => realComponent w hw (adelicArchGLIncl K (Γ s)) with hMdef
  have hcomp : ∀ s, realComponent w hw (g * adelicArchGLIncl K (Γ s)) = R * M s := fun s =>
    realComponent_mul_termwise w hw _ _
  have hRdet : R.det ≠ 0 := det_realComponent_ne_zero w hw g
  have hMdet : ∀ s, (M s).det ≠ 0 := fun s => det_realComponent_ne_zero w hw _
  have hRMdet : ∀ s, (R * M s).det ≠ 0 := fun s => by rw [Matrix.det_mul]; exact mul_ne_zero hRdet (hMdet s)
  have hcurve : HasDerivAt (fun s => Matrix.of.symm (R * M s)) (Matrix.of.symm (R * DR t)) t :=
    hasDerivAt_coords_mul_left R (hDR t)
  have hmem : Matrix.of.symm (R * M t) ∈ ArchR.glSet := by
    show (Matrix.of (Matrix.of.symm (R * M t))).det ≠ 0
    simpa using hRMdet t
  have hW : HasDerivAt (fun s => (dR w hw).W (R * M s))
      (fderivWithin ℝ (ArchR.asPi (dR w hw).W) ArchR.glSet (Matrix.of.symm (R * M t)) (Matrix.of.symm (R * DR t)))
      t := by
    have h := hasDerivAt_comp_coords isOpen_glSetR
      ((dR w hw).smooth.differentiableOn (by simp)) hcurve hmem
    simpa [ArchR.asPi] using h
  have hdir : R * DR t = (R * M t) * coefR hw Γ DR t := by
    simp only [coefR]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (M t), Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hMdet t)),
      Matrix.one_mul]
  have hW' : HasDerivAt (fun s => (dR w hw).W (R * M s))
      (∑ ι : Fin 2 × Fin 2, ((coefR hw Γ DR t ι.1 ι.2 : ℝ) : ℂ) * (dRw ι w hw).W (R * M t)) t := by
    convert hW using 1
    rw [hdir, linear_coords_mul_eq_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [hat ι (R * M t) (hRMdet t)]
  have hdet : HasDerivAt (fun s => (R * M s).det) ((R * M t).det * (coefR hw Γ DR t).trace) t := by
    have h := hasDerivAt_det_fin_two (hDR t) (hMdet t)
    have h' : HasDerivAt (fun s => (R * M s).det) (R.det * ((M t).det * ((M t)⁻¹ * DR t).trace)) t := by
      simp only [Matrix.det_mul]
      exact h.const_mul R.det
    convert h' using 1
    simp only [coefR, Matrix.det_mul]
    ring
  have hnf : HasDerivAt (fun s => (Real.sqrt |(R * M s).det|)⁻¹)
      (-(1 / 2 * (coefR hw Γ DR t).trace) * (Real.sqrt |(R * M t).det|)⁻¹) t := by
    have h := hasDerivAt_inv_sqrt_abs hdet (hRMdet t)
    have hd : (R * M t).det ≠ 0 := hRMdet t
    convert h using 2
    field_simp
  have hnfC : HasDerivAt (fun s => ((Real.sqrt |(R * M s).det| : ℝ) : ℂ)⁻¹)
      (((-(1 / 2 * (coefR hw Γ DR t).trace) * (Real.sqrt |(R * M t).det|)⁻¹ : ℝ) : ℂ)) t := by
    have h := hnf.ofReal_comp
    simpa [Complex.ofReal_inv] using h
  have hprod := hW'.mul hnfC
  have hfun : (fun s : ℝ => localFactor' archR archC dR dC w (g * adelicArchGLIncl K (Γ s))) =
      fun s => (dR w hw).W (R * M s) * ((Real.sqrt |(R * M s).det| : ℝ) : ℂ)⁻¹ := by
    funext s
    rw [localFactor'_real archR archC dR dC hw, hcomp s]
  rw [hfun]
  convert hprod using 1 <;> try first | with_reducible_and_instances rfl | rfl
  have hfam : ∀ ι : Fin 2 × Fin 2, localFactor' archR archC (dRw ι) dC w (g * adelicArchGLIncl K (Γ t)) =
      (dRw ι w hw).W (R * M t) * ((Real.sqrt |(R * M t).det| : ℝ) : ℂ)⁻¹ := fun ι => by
    rw [localFactor'_real archR archC (dRw ι) dC hw, hcomp t]
  simp only [hfam, localFactor'_real archR archC dR dC hw, hcomp t, Finset.sum_mul]
  push_cast
  ring_nf
  congr 1
  exact Finset.sum_congr rfl fun ι _ => by ring

private theorem hasDerivAt_localFactor'_complex
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) {w : InfinitePlace K}
    (hw : w.IsComplex)
    (dCw : (Fin 2 × Fin 2) × Fin 2 → ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), ArchDatumC (archC w' hw'))
    (hat : ∀ (ι : (Fin 2 × Fin 2) × Fin 2) (g : Matrix (Fin 2) (Fin 2) ℂ), g.det ≠ 0 →
      (dCw ι w hw).W g =
        fderivWithin ℝ (ArchC.asPi (dC w hw).W) ArchC.glSet (Matrix.of.symm g) (Matrix.of.symm (g * cplxUnit ι)))
    (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K)) (DC : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hDC : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Matrix.of.symm (complexComponent w hw (adelicArchGLIncl K (Γ s))))
      (Matrix.of.symm (DC t)) t)
    (g : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => localFactor' archR archC dR dC w (g * adelicArchGLIncl K (Γ s)))
      ((∑ ι : (Fin 2 × Fin 2) × Fin 2, ((cplxCoeff (coefC hw Γ DC t) ι : ℝ) : ℂ) *
          localFactor' archR archC dR (dCw ι) w (g * adelicArchGLIncl K (Γ t))) -
        (((coefC hw Γ DC t).trace.re : ℝ) : ℂ) * localFactor' archR archC dR dC w (g * adelicArchGLIncl K (Γ t)))
      t := by
  set R : Matrix (Fin 2) (Fin 2) ℂ := complexComponent w hw g with hRdef
  set M : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun s => complexComponent w hw (adelicArchGLIncl K (Γ s)) with hMdef
  have hcomp : ∀ s, complexComponent w hw (g * adelicArchGLIncl K (Γ s)) = R * M s := fun s =>
    complexComponent_mul_termwise w hw _ _
  have hRdet : R.det ≠ 0 := det_complexComponent_ne_zero w hw g
  have hMdet : ∀ s, (M s).det ≠ 0 := fun s => det_complexComponent_ne_zero w hw _
  have hRMdet : ∀ s, (R * M s).det ≠ 0 := fun s => by rw [Matrix.det_mul]; exact mul_ne_zero hRdet (hMdet s)
  have hcurve : HasDerivAt (fun s => Matrix.of.symm (R * M s)) (Matrix.of.symm (R * DC t)) t :=
    hasDerivAt_coords_mul_left_complex R (hDC t)
  have hmem : Matrix.of.symm (R * M t) ∈ ArchC.glSet := by
    show (Matrix.of (Matrix.of.symm (R * M t))).det ≠ 0
    simpa using hRMdet t
  have hW : HasDerivAt (fun s => (dC w hw).W (R * M s))
      (fderivWithin ℝ (ArchC.asPi (dC w hw).W) ArchC.glSet (Matrix.of.symm (R * M t)) (Matrix.of.symm (R * DC t)))
      t := by
    have h := hasDerivAt_comp_coords_complex isOpen_glSetC
      ((dC w hw).smooth.differentiableOn (by simp)) hcurve hmem
    simpa [ArchC.asPi] using h
  have hdir : R * DC t = (R * M t) * coefC hw Γ DC t := by
    simp only [coefC]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (M t), Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hMdet t)),
      Matrix.one_mul]
  have hW' : HasDerivAt (fun s => (dC w hw).W (R * M s))
      (∑ ι : (Fin 2 × Fin 2) × Fin 2, ((cplxCoeff (coefC hw Γ DC t) ι : ℝ) : ℂ) * (dCw ι w hw).W (R * M t)) t := by
    convert hW using 1
    rw [hdir, linear_coords_mul_eq_sum_complex, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [Fin.sum_univ_two]
    simp only [cplxCoeff, cplxUnit, hat _ (R * M t) (hRMdet t), Fin.isValue, if_true, Fin.one_eq_zero_iff,
      OfNat.ofNat_ne_one, if_false]
  have hdet : HasDerivAt (fun s => (R * M s).det) ((R * M t).det * (coefC hw Γ DC t).trace) t := by
    have h := hasDerivAt_det_fin_two_complex (hDC t) (hMdet t)
    have h' : HasDerivAt (fun s => (R * M s).det) (R.det * ((M t).det * ((M t)⁻¹ * DC t).trace)) t := by
      simp only [Matrix.det_mul]
      exact h.const_mul R.det
    convert h' using 1
    simp only [coefC, Matrix.det_mul]
    ring
  have hnf : HasDerivAt (fun s => ‖(R * M s).det‖⁻¹) (-(coefC hw Γ DC t).trace.re * ‖(R * M t).det‖⁻¹) t := by
    have h := hasDerivAt_inv_norm hdet (hRMdet t)
    have hd : (R * M t).det ≠ 0 := hRMdet t
    convert h using 2
    rw [mul_div_cancel_left₀ _ hd]
  have hnfC : HasDerivAt (fun s => ((‖(R * M s).det‖ : ℝ) : ℂ)⁻¹)
      (((-(coefC hw Γ DC t).trace.re * ‖(R * M t).det‖⁻¹ : ℝ) : ℂ)) t := by
    have h := hnf.ofReal_comp
    simpa [Complex.ofReal_inv] using h
  have hprod := hW'.mul hnfC
  have hfun : (fun s : ℝ => localFactor' archR archC dR dC w (g * adelicArchGLIncl K (Γ s))) =
      fun s => (dC w hw).W (R * M s) * ((‖(R * M s).det‖ : ℝ) : ℂ)⁻¹ := by
    funext s
    rw [localFactor'_complex archR archC dR dC hw, hcomp s]
  rw [hfun]
  convert hprod using 1 <;> try first | with_reducible_and_instances rfl | rfl
  have hfam : ∀ ι, localFactor' archR archC dR (dCw ι) w (g * adelicArchGLIncl K (Γ t)) =
      (dCw ι w hw).W (R * M t) * ((‖(R * M t).det‖ : ℝ) : ℂ)⁻¹ := fun ι => by
    rw [localFactor'_complex archR archC dR (dCw ι) hw, hcomp t]
  simp only [hfam, localFactor'_complex archR archC dR dC hw, hcomp t, Finset.sum_mul]
  push_cast
  ring_nf
  congr 1
  exact Finset.sum_congr rfl fun ι _ => by ring

private theorem sum_places_split (F : InfinitePlace K → ℂ) :
    ∑ w : InfinitePlace K, F w =
      ∑ w : {w : InfinitePlace K // w.IsReal}, F w.1 + ∑ w : {w : InfinitePlace K // w.IsComplex}, F w.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace K => w.IsReal) F]
  congr 1
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun _ => rfl

private theorem prod_erase_mul_localFactor'
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    {dR₁ : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw)}
    {dC₁ : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)} {w₀ : InfinitePlace K}
    (hR : ∀ (w : InfinitePlace K) (hw : w.IsReal), w ≠ w₀ → dR₁ w hw = dR w hw)
    (hC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), w ≠ w₀ → dC₁ w hw = dC w hw) (g : AdelicGL2 (𝓞 K) K) :
    (∏ w ∈ Finset.univ.erase w₀, localFactor' archR archC dR dC w g) * localFactor' archR archC dR₁ dC₁ w₀ g =
      ∏ w : InfinitePlace K, localFactor' archR archC dR₁ dC₁ w g := by
  rw [← archW'_eq_prod_localFactor', archW'_eq_prod_erase_mul archR archC hR hC]

private noncomputable def termDeriv (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) (dF : FinWhittakerDatum K S Pi)
    (dR' : ∀ (w : InfinitePlace K), w.IsReal → Fin 2 × Fin 2 →
      ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ArchDatumR (archR w' hw'))
    (dC' : ∀ (w : InfinitePlace K), w.IsComplex → (Fin 2 × Fin 2) × Fin 2 →
      ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), ArchDatumC (archC w' hw'))
    (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K))
    (DR : ∀ (w : InfinitePlace K), w.IsReal → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (DC : ∀ (w : InfinitePlace K), w.IsComplex → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (q : AdelicGL2 (𝓞 K) K) (t : ℝ) (α : Kˣ) : ℂ :=
  (∑ w : {w : InfinitePlace K // w.IsReal}, ∑ ι : Fin 2 × Fin 2,
      ((coefR w.2 Γ (DR w.1 w.2) t ι.1 ι.2 : ℝ) : ℂ) *
        seriesTerm d archR archC (dR' w.1 w.2 ι) dC dF (q * adelicArchGLIncl K (Γ t)) α) +
    (∑ w : {w : InfinitePlace K // w.IsComplex}, ∑ ι : (Fin 2 × Fin 2) × Fin 2,
      ((cplxCoeff (coefC w.2 Γ (DC w.1 w.2) t) ι : ℝ) : ℂ) *
        seriesTerm d archR archC dR (dC' w.1 w.2 ι) dF (q * adelicArchGLIncl K (Γ t)) α) -
    (((∑ w : {w : InfinitePlace K // w.IsReal}, (1 / 2 : ℝ) * (coefR w.2 Γ (DR w.1 w.2) t).trace) +
        ∑ w : {w : InfinitePlace K // w.IsComplex}, (coefC w.2 Γ (DC w.1 w.2) t).trace.re : ℝ) : ℂ) *
      seriesTerm d archR archC dR dC dF (q * adelicArchGLIncl K (Γ t)) α

private theorem hasDerivAt_seriesTerm_family (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) (dF : FinWhittakerDatum K S Pi)
    (dR' : ∀ (w : InfinitePlace K), w.IsReal → Fin 2 × Fin 2 →
      ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ArchDatumR (archR w' hw'))
    (hR'off : ∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2) (w' : InfinitePlace K) (hw' : w'.IsReal),
      w' ≠ w → dR' w hw ι w' hw' = dR w' hw')
    (hR'at : ∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2) (g : Matrix (Fin 2) (Fin 2) ℝ), g.det ≠ 0 →
      (dR' w hw ι w hw).W g =
        fderivWithin ℝ (ArchR.asPi (dR w hw).W) ArchR.glSet (Matrix.of.symm g)
          (Matrix.of.symm (g * Matrix.single ι.1 ι.2 (1 : ℝ))))
    (dC' : ∀ (w : InfinitePlace K), w.IsComplex → (Fin 2 × Fin 2) × Fin 2 →
      ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), ArchDatumC (archC w' hw'))
    (hC'off : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2) (w' : InfinitePlace K)
      (hw' : w'.IsComplex), w' ≠ w → dC' w hw ι w' hw' = dC w' hw')
    (hC'at : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2) (g : Matrix (Fin 2) (Fin 2) ℂ),
      g.det ≠ 0 → (dC' w hw ι w hw).W g =
        fderivWithin ℝ (ArchC.asPi (dC w hw).W) ArchC.glSet (Matrix.of.symm g) (Matrix.of.symm (g * cplxUnit ι)))
    (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K))
    (DR : ∀ (w : InfinitePlace K), w.IsReal → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (DC : ∀ (w : InfinitePlace K), w.IsComplex → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hDR : ∀ (w : InfinitePlace K) (hw : w.IsReal) (t : ℝ),
      HasDerivAt (fun s : ℝ => Matrix.of.symm (realComponent w hw (adelicArchGLIncl K (Γ s))))
        (Matrix.of.symm (DR w hw t)) t)
    (hDC : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (t : ℝ),
      HasDerivAt (fun s : ℝ => Matrix.of.symm (complexComponent w hw (adelicArchGLIncl K (Γ s))))
        (Matrix.of.symm (DC w hw t)) t)
    (q : AdelicGL2 (𝓞 K) K) (t : ℝ) (α : Kˣ) :
    HasDerivAt (fun s : ℝ => seriesTerm d archR archC dR dC dF (q * adelicArchGLIncl K (Γ s)) α)
      (termDeriv d archR archC dR dC dF dR' dC' Γ DR DC q t α) t := by
  set gα : AdelicGL2 (𝓞 K) K := globalPoints (𝓞 K) K (diagOne α) * q with hgα
  set cα : ℂ := d.a α * d.epsChar q * dF.Wf gα with hcα
  have hfun : (fun s : ℝ => seriesTerm d archR archC dR dC dF (q * adelicArchGLIncl K (Γ s)) α) =
      fun s => cα * ∏ w : InfinitePlace K, localFactor' archR archC dR dC w (gα * adelicArchGLIncl K (Γ s)) := by
    funext s
    rw [seriesTerm_mul_adelicArchGLIncl]
  let Dφ : InfinitePlace K → ℂ := fun w =>
    if hw : w.IsReal then
      (∑ ι : Fin 2 × Fin 2, ((coefR hw Γ (DR w hw) t ι.1 ι.2 : ℝ) : ℂ) *
          localFactor' archR archC (dR' w hw ι) dC w (gα * adelicArchGLIncl K (Γ t))) -
        ((1 / 2 * (coefR hw Γ (DR w hw) t).trace : ℝ) : ℂ) *
          localFactor' archR archC dR dC w (gα * adelicArchGLIncl K (Γ t))
    else
      (∑ ι : (Fin 2 × Fin 2) × Fin 2,
          ((cplxCoeff (coefC (InfinitePlace.not_isReal_iff_isComplex.mp hw) Γ
              (DC w (InfinitePlace.not_isReal_iff_isComplex.mp hw)) t) ι : ℝ) : ℂ) *
            localFactor' archR archC dR (dC' w (InfinitePlace.not_isReal_iff_isComplex.mp hw) ι) w
              (gα * adelicArchGLIncl K (Γ t))) -
        (((coefC (InfinitePlace.not_isReal_iff_isComplex.mp hw) Γ
            (DC w (InfinitePlace.not_isReal_iff_isComplex.mp hw)) t).trace.re : ℝ) : ℂ) *
          localFactor' archR archC dR dC w (gα * adelicArchGLIncl K (Γ t))
  have hplace : ∀ w ∈ (Finset.univ : Finset (InfinitePlace K)),
      HasDerivAt (fun s : ℝ => localFactor' archR archC dR dC w (gα * adelicArchGLIncl K (Γ s))) (Dφ w) t := by
    intro w _
    by_cases hw : w.IsReal
    · simp only [Dφ, dif_pos hw]
      exact hasDerivAt_localFactor'_real archR archC dR dC hw (dR' w hw) (hR'at w hw) Γ (DR w hw) (hDR w hw) gα t
    · simp only [Dφ, dif_neg hw]
      exact hasDerivAt_localFactor'_complex archR archC dR dC (InfinitePlace.not_isReal_iff_isComplex.mp hw)
        (dC' w _) (hC'at w _) Γ (DC w _) (hDC w _) gα t
  have hprod := (HasDerivAt.fun_finsetProd hplace).const_mul cα
  rw [hfun]
  convert hprod using 1 <;> try first | with_reducible_and_instances rfl | rfl
  set P : ℂ := ∏ w : InfinitePlace K, localFactor' archR archC dR dC w (gα * adelicArchGLIncl K (Γ t)) with hP
  have hterm₀ : seriesTerm d archR archC dR dC dF (q * adelicArchGLIncl K (Γ t)) α = cα * P := by
    rw [seriesTerm_mul_adelicArchGLIncl]
  have htermR : ∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2),
      seriesTerm d archR archC (dR' w hw ι) dC dF (q * adelicArchGLIncl K (Γ t)) α =
        cα * ((∏ w' ∈ Finset.univ.erase w, localFactor' archR archC dR dC w' (gα * adelicArchGLIncl K (Γ t))) *
          localFactor' archR archC (dR' w hw ι) dC w (gα * adelicArchGLIncl K (Γ t))) := by
    intro w hw ι
    rw [seriesTerm_mul_adelicArchGLIncl,
      prod_erase_mul_localFactor' archR archC dR dC (fun w' hw' h => hR'off w hw ι w' hw' h) (fun _ _ _ => rfl)]
  have htermC : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2),
      seriesTerm d archR archC dR (dC' w hw ι) dF (q * adelicArchGLIncl K (Γ t)) α =
        cα * ((∏ w' ∈ Finset.univ.erase w, localFactor' archR archC dR dC w' (gα * adelicArchGLIncl K (Γ t))) *
          localFactor' archR archC dR (dC' w hw ι) w (gα * adelicArchGLIncl K (Γ t))) := by
    intro w hw ι
    rw [seriesTerm_mul_adelicArchGLIncl,
      prod_erase_mul_localFactor' archR archC dR dC (fun _ _ _ => rfl) (fun w' hw' h => hC'off w hw ι w' hw' h)]
  have hP_erase : ∀ w : InfinitePlace K,
      (∏ w' ∈ Finset.univ.erase w, localFactor' archR archC dR dC w' (gα * adelicArchGLIncl K (Γ t))) *
        localFactor' archR archC dR dC w (gα * adelicArchGLIncl K (Γ t)) = P := fun w =>
    Finset.prod_erase_mul _ _ (Finset.mem_univ w)
  set E : InfinitePlace K → ℂ := fun w =>
    ∏ w' ∈ Finset.univ.erase w, localFactor' archR archC dR dC w' (gα * adelicArchGLIncl K (Γ t)) with hE
  have hreal : ∀ w : {w : InfinitePlace K // w.IsReal}, cα * (E w.1 • Dφ w.1) =
      (∑ ι : Fin 2 × Fin 2, ((coefR w.2 Γ (DR w.1 w.2) t ι.1 ι.2 : ℝ) : ℂ) *
          seriesTerm d archR archC (dR' w.1 w.2 ι) dC dF (q * adelicArchGLIncl K (Γ t)) α) -
        ((1 / 2 * (coefR w.2 Γ (DR w.1 w.2) t).trace : ℝ) : ℂ) *
          seriesTerm d archR archC dR dC dF (q * adelicArchGLIncl K (Γ t)) α := by
    intro w
    simp only [Dφ, dif_pos w.2, htermR w.1 w.2, hterm₀, smul_eq_mul]
    rw [mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun ι _ => by ring
    · rw [← hP_erase w.1]
      ring
  have hcplx : ∀ w : {w : InfinitePlace K // w.IsComplex}, cα * (E w.1 • Dφ w.1) =
      (∑ ι : (Fin 2 × Fin 2) × Fin 2, ((cplxCoeff (coefC w.2 Γ (DC w.1 w.2) t) ι : ℝ) : ℂ) *
          seriesTerm d archR archC dR (dC' w.1 w.2 ι) dF (q * adelicArchGLIncl K (Γ t)) α) -
        (((coefC w.2 Γ (DC w.1 w.2) t).trace.re : ℝ) : ℂ) *
          seriesTerm d archR archC dR dC dF (q * adelicArchGLIncl K (Γ t)) α := by
    intro w
    have hw' : ¬ w.1.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr w.2
    simp only [Dφ, dif_neg hw', htermC w.1 w.2, hterm₀, smul_eq_mul]
    rw [mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun ι _ => by ring
    · rw [← hP_erase w.1]
      ring
  rw [Finset.mul_sum, sum_places_split (fun w => cα * (E w • Dφ w))]
  simp only [hreal, hcplx, termDeriv, Finset.sum_sub_distrib]
  push_cast
  simp only [add_mul, Finset.sum_mul]
  ring

private theorem exists_majorant_of_family (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR₁ : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC₁ : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (q : AdelicGL2 (𝓞 K) K) :
    ∃ V ∈ 𝓝 q, ∃ b : Kˣ → ℝ, Summable b ∧ (∀ α, 0 ≤ b α) ∧
      ∀ g ∈ V, ∀ α : Kˣ, ‖seriesTerm d archR archC dR₁ dC₁ dF g α‖ ≤ b α := by
  have R := exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice K Pi S archR archC epsS ω
    hω hωb d dR₁ dC₁ dF hnice
  obtain ⟨V, hV, b, hb, hb0, hle⟩ := R.2.2.2.1 d.a (d.bounded.imp fun _ h α => (h α).1)
    (fun α h => (d.floor α h).1) id continuous_id q
  exact ⟨V, hV, b, hb, hb0, fun g hg α => hle g hg α⟩

private theorem continuousAt_coefR {w : InfinitePlace K} (hw : w.IsReal) (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K))
    (DR : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hDR : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Matrix.of.symm (realComponent w hw (adelicArchGLIncl K (Γ s))))
      (Matrix.of.symm (DR t)) t)
    (hDRc : ContinuousAt DR 0) : ContinuousAt (coefR hw Γ DR) 0 := by
  have hM : ContinuousAt (fun s : ℝ => realComponent w hw (adelicArchGLIncl K (Γ s))) 0 := (hDR 0).continuousAt
  have hdet : (realComponent w hw (adelicArchGLIncl K (Γ 0))).det ≠ 0 := det_realComponent_ne_zero w hw _
  have hinv : ContinuousAt (fun s : ℝ => (realComponent w hw (adelicArchGLIncl K (Γ s)))⁻¹) 0 := by
    refine (continuousAt_matrix_inv _ ?_).comp hM
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  exact hinv.mul hDRc

private theorem continuousAt_coefC {w : InfinitePlace K} (hw : w.IsComplex)
    (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K)) (DC : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hDC : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Matrix.of.symm (complexComponent w hw (adelicArchGLIncl K (Γ s))))
      (Matrix.of.symm (DC t)) t)
    (hDCc : ContinuousAt DC 0) : ContinuousAt (coefC hw Γ DC) 0 := by
  have hM : ContinuousAt (fun s : ℝ => complexComponent w hw (adelicArchGLIncl K (Γ s))) 0 := (hDC 0).continuousAt
  have hdet : (complexComponent w hw (adelicArchGLIncl K (Γ 0))).det ≠ 0 := det_complexComponent_ne_zero w hw _
  have hinv : ContinuousAt (fun s : ℝ => (complexComponent w hw (adelicArchGLIncl K (Γ s)))⁻¹) 0 := by
    refine (continuousAt_matrix_inv _ ?_).comp hM
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  exact hinv.mul hDCc

private theorem eventually_entries_le_of_continuousAt {𝕜 : Type} [NormedField 𝕜] {A : ℝ → Matrix (Fin 2) (Fin 2) 𝕜}
    (hA : ContinuousAt A 0) : ∃ B : ℝ, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i j, ‖A s i j‖ ≤ B := by
  refine ⟨∑ i : Fin 2, ∑ j : Fin 2, (‖A 0 i j‖ + 1), ?_⟩
  have hij : ∀ i j, ∀ᶠ s in 𝓝 (0 : ℝ), ‖A s i j‖ ≤ ‖A 0 i j‖ + 1 := by
    intro i j
    have hentry : Continuous fun B : Matrix (Fin 2) (Fin 2) 𝕜 => B i j :=
      (continuous_apply j).comp (continuous_apply i)
    have h : ContinuousAt (fun s => A s i j) 0 := hentry.continuousAt.comp hA
    have h' : ContinuousAt (fun s => ‖A s i j‖) 0 := h.norm
    exact h'.eventually (ge_mem_nhds (lt_add_one _))
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j] with s hs i j
  calc ‖A s i j‖ ≤ ‖A 0 i j‖ + 1 := hs i j
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, (‖A 0 i j‖ + 1) := by
      have h1 : ‖A 0 i j‖ + 1 ≤ ∑ j' : Fin 2, (‖A 0 i j'‖ + 1) :=
        Finset.single_le_sum (f := fun j' => ‖A 0 i j'‖ + 1) (fun j' _ => by positivity) (Finset.mem_univ j)
      exact h1.trans (Finset.single_le_sum (f := fun i' => ∑ j' : Fin 2, (‖A 0 i' j'‖ + 1))
        (fun i' _ => by positivity) (Finset.mem_univ i))

open scoped Classical in
private theorem hasDerivAt_jlSeries'_mul_adelicArchGLIncl {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Pi : HeckeEigensystem K ℂ} {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (dR' : ∀ (w : InfinitePlace K), w.IsReal → Fin 2 × Fin 2 →
      ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ArchDatumR (archR w' hw'))
    (hR'off : ∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2) (w' : InfinitePlace K) (hw' : w'.IsReal),
      w' ≠ w → dR' w hw ι w' hw' = dR w' hw')
    (hR'at : ∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2) (g : Matrix (Fin 2) (Fin 2) ℝ), g.det ≠ 0 →
      (dR' w hw ι w hw).W g =
        fderivWithin ℝ (ArchR.asPi (dR w hw).W) ArchR.glSet (Matrix.of.symm g)
          (Matrix.of.symm (g * Matrix.single ι.1 ι.2 (1 : ℝ))))
    (dC' : ∀ (w : InfinitePlace K), w.IsComplex → (Fin 2 × Fin 2) × Fin 2 →
      ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), ArchDatumC (archC w' hw'))
    (hC'off : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2) (w' : InfinitePlace K)
      (hw' : w'.IsComplex), w' ≠ w → dC' w hw ι w' hw' = dC w' hw')
    (hC'at : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2) (g : Matrix (Fin 2) (Fin 2) ℂ),
      g.det ≠ 0 → (dC' w hw ι w hw).W g =
        fderivWithin ℝ (ArchC.asPi (dC w hw).W) ArchC.glSet (Matrix.of.symm g) (Matrix.of.symm (g * cplxUnit ι)))
    (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K)) (hΓ₀ : Γ 0 = 1)
    (hΓc : ContinuousAt (fun s : ℝ => adelicArchGLIncl K (Γ s)) 0)
    (DR : ∀ (w : InfinitePlace K), w.IsReal → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (DC : ∀ (w : InfinitePlace K), w.IsComplex → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hDR : ∀ (w : InfinitePlace K) (hw : w.IsReal) (t : ℝ),
      HasDerivAt (fun s : ℝ => Matrix.of.symm (realComponent w hw (adelicArchGLIncl K (Γ s))))
        (Matrix.of.symm (DR w hw t)) t)
    (hDC : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (t : ℝ),
      HasDerivAt (fun s : ℝ => Matrix.of.symm (complexComponent w hw (adelicArchGLIncl K (Γ s))))
        (Matrix.of.symm (DC w hw t)) t)
    (hDRc : ∀ (w : InfinitePlace K) (hw : w.IsReal), ContinuousAt (DR w hw) 0)
    (hDCc : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ContinuousAt (DC w hw) 0)
    (q : AdelicGL2 (𝓞 K) K) :
    HasDerivAt (fun t : ℝ => jlSeries' d archR archC dR dC dF (q * adelicArchGLIncl K (Γ t)))
      ((∑ w : {w : InfinitePlace K // w.IsReal}, ∑ ι : Fin 2 × Fin 2,
          ((DR w.1 w.2 0 ι.1 ι.2 : ℝ) : ℂ) * jlSeries' d archR archC (dR' w.1 w.2 ι) dC dF q) +
        (∑ w : {w : InfinitePlace K // w.IsComplex}, ∑ ι : (Fin 2 × Fin 2) × Fin 2,
          ((cplxCoeff (DC w.1 w.2 0) ι : ℝ) : ℂ) * jlSeries' d archR archC dR (dC' w.1 w.2 ι) dF q) -
        (((∑ w : {w : InfinitePlace K // w.IsReal}, (1 / 2 : ℝ) * (DR w.1 w.2 0).trace) +
            ∑ w : {w : InfinitePlace K // w.IsComplex}, (DC w.1 w.2 0).trace.re : ℝ) : ℂ) *
          jlSeries' d archR archC dR dC dF q) 0 := by
  have hmove : ContinuousAt (fun s : ℝ => q * adelicArchGLIncl K (Γ s)) 0 := continuousAt_const.mul hΓc
  have hmove₀ : q * adelicArchGLIncl K (Γ 0) = q := by rw [hΓ₀, map_one, mul_one]
  obtain ⟨V₀, hV₀, b₀, hb₀, hb₀0, hle₀⟩ := exists_majorant_of_family hω hωb d archR archC dR dC dF hnice q
  have hR : ∀ i : {w : InfinitePlace K // w.IsReal} × (Fin 2 × Fin 2), ∃ V ∈ 𝓝 q, ∃ b : Kˣ → ℝ, Summable b ∧
      (∀ α, 0 ≤ b α) ∧ ∀ g ∈ V, ∀ α : Kˣ, ‖seriesTerm d archR archC (dR' i.1.1 i.1.2 i.2) dC dF g α‖ ≤ b α :=
    fun i => exists_majorant_of_family hω hωb d archR archC _ dC dF hnice q
  have hC : ∀ i : {w : InfinitePlace K // w.IsComplex} × ((Fin 2 × Fin 2) × Fin 2), ∃ V ∈ 𝓝 q, ∃ b : Kˣ → ℝ,
      Summable b ∧ (∀ α, 0 ≤ b α) ∧
        ∀ g ∈ V, ∀ α : Kˣ, ‖seriesTerm d archR archC dR (dC' i.1.1 i.1.2 i.2) dF g α‖ ≤ b α :=
    fun i => exists_majorant_of_family hω hωb d archR archC dR _ dF hnice q
  choose VR hVR bR hbR hbR0 hleR using hR
  choose VC hVC bC hbC hbC0 hleC using hC
  have hBR : ∀ w : {w : InfinitePlace K // w.IsReal}, ∃ B : ℝ, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i j,
      ‖coefR w.2 Γ (DR w.1 w.2) s i j‖ ≤ B := fun w =>
    eventually_entries_le_of_continuousAt (continuousAt_coefR w.2 Γ (DR w.1 w.2) (hDR w.1 w.2) (hDRc w.1 w.2))
  have hBC : ∀ w : {w : InfinitePlace K // w.IsComplex}, ∃ B : ℝ, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i j,
      ‖coefC w.2 Γ (DC w.1 w.2) s i j‖ ≤ B := fun w =>
    eventually_entries_le_of_continuousAt (continuousAt_coefC w.2 Γ (DC w.1 w.2) (hDC w.1 w.2) (hDCc w.1 w.2))
  choose BR hBR using hBR
  choose BC hBC using hBC
  have hV : (⋂ i, VR i) ∩ (⋂ i, VC i) ∩ V₀ ∈ 𝓝 q :=
    Filter.inter_mem (Filter.inter_mem (Filter.iInter_mem.2 hVR) (Filter.iInter_mem.2 hVC)) hV₀
  have hgood : ∀ᶠ s in 𝓝 (0 : ℝ),
      (q * adelicArchGLIncl K (Γ s) ∈ (⋂ i, VR i) ∩ (⋂ i, VC i) ∩ V₀) ∧
        (∀ w : {w : InfinitePlace K // w.IsReal}, ∀ i j, ‖coefR w.2 Γ (DR w.1 w.2) s i j‖ ≤ BR w) ∧
        ∀ w : {w : InfinitePlace K // w.IsComplex}, ∀ i j, ‖coefC w.2 Γ (DC w.1 w.2) s i j‖ ≤ BC w := by
    have h₁ : ∀ᶠ s in 𝓝 (0 : ℝ), q * adelicArchGLIncl K (Γ s) ∈ (⋂ i, VR i) ∩ (⋂ i, VC i) ∩ V₀ :=
      hmove.preimage_mem_nhds (by rwa [hmove₀])
    exact h₁.and ((Filter.eventually_all.2 hBR).and (Filter.eventually_all.2 hBC))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hgood
  set u : Kˣ → ℝ := fun α =>
    (∑ i : {w : InfinitePlace K // w.IsReal} × (Fin 2 × Fin 2), BR i.1 * bR i α) +
      (∑ i : {w : InfinitePlace K // w.IsComplex} × ((Fin 2 × Fin 2) × Fin 2), BC i.1 * bC i α) +
      ((∑ w : {w : InfinitePlace K // w.IsReal}, BR w) + ∑ w : {w : InfinitePlace K // w.IsComplex}, 2 * BC w) *
        b₀ α with hu
  have hu_sum : Summable u :=
    ((summable_sum fun i _ => (hbR i).mul_left (BR i.1)).add
      (summable_sum fun i _ => (hbC i).mul_left (BC i.1))).add (hb₀.mul_left _)
  have hderiv_le : ∀ s ∈ Metric.ball (0 : ℝ) ε, ∀ α : Kˣ,
      ‖termDeriv d archR archC dR dC dF dR' dC' Γ DR DC q s α‖ ≤ u α := by
    intro s hs α
    obtain ⟨⟨hsR, hsC⟩, hs₀⟩ := (hball (by simpa [Real.dist_eq] using hs)).1
    obtain ⟨-, hcR, hcC⟩ := hball (by simpa [Real.dist_eq] using hs)
    simp only [Set.mem_iInter] at hsR hsC
    have hA : ‖∑ w : {w : InfinitePlace K // w.IsReal}, ∑ ι : Fin 2 × Fin 2,
        ((coefR w.2 Γ (DR w.1 w.2) s ι.1 ι.2 : ℝ) : ℂ) *
          seriesTerm d archR archC (dR' w.1 w.2 ι) dC dF (q * adelicArchGLIncl K (Γ s)) α‖ ≤
        ∑ i : {w : InfinitePlace K // w.IsReal} × (Fin 2 × Fin 2), BR i.1 * bR i α := by
      rw [Fintype.sum_prod_type]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun ι _ => ?_))
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (hcR w ι.1 ι.2) (hleR (w, ι) _ (hsR (w, ι)) α) (norm_nonneg _)
        ((norm_nonneg _).trans (hcR w ι.1 ι.2))
    have hB : ‖∑ w : {w : InfinitePlace K // w.IsComplex}, ∑ ι : (Fin 2 × Fin 2) × Fin 2,
        ((cplxCoeff (coefC w.2 Γ (DC w.1 w.2) s) ι : ℝ) : ℂ) *
          seriesTerm d archR archC dR (dC' w.1 w.2 ι) dF (q * adelicArchGLIncl K (Γ s)) α‖ ≤
        ∑ i : {w : InfinitePlace K // w.IsComplex} × ((Fin 2 × Fin 2) × Fin 2), BC i.1 * bC i α := by
      rw [Fintype.sum_prod_type]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun ι _ => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hcoef : |cplxCoeff (coefC w.2 Γ (DC w.1 w.2) s) ι| ≤ BC w := by
        unfold cplxCoeff
        split_ifs
        · exact (Complex.abs_re_le_norm _).trans (hcC w ι.1.1 ι.1.2)
        · exact (Complex.abs_im_le_norm _).trans (hcC w ι.1.1 ι.1.2)
      exact mul_le_mul hcoef (hleC (w, ι) _ (hsC (w, ι)) α) (norm_nonneg _) ((abs_nonneg _).trans hcoef)
    have htr : ‖((((∑ w : {w : InfinitePlace K // w.IsReal}, (1 / 2 : ℝ) * (coefR w.2 Γ (DR w.1 w.2) s).trace) +
          ∑ w : {w : InfinitePlace K // w.IsComplex}, (coefC w.2 Γ (DC w.1 w.2) s).trace.re : ℝ)) : ℂ)‖ ≤
        (∑ w : {w : InfinitePlace K // w.IsReal}, BR w) + ∑ w : {w : InfinitePlace K // w.IsComplex}, 2 * BC w := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
        rw [abs_mul, Matrix.trace_fin_two, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have h1 := hcR w 0 0
        have h2 := hcR w 1 1
        rw [Real.norm_eq_abs] at h1 h2
        calc 1 / 2 * |coefR w.2 Γ (DR w.1 w.2) s 0 0 + coefR w.2 Γ (DR w.1 w.2) s 1 1|
            ≤ 1 / 2 * (BR w + BR w) := by gcongr; exact (abs_add_le _ _).trans (add_le_add h1 h2)
          _ = BR w := by ring
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
        rw [Matrix.trace_fin_two]
        refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
        linarith [hcC w 0 0, hcC w 1 1]
    have hT : ‖seriesTerm d archR archC dR dC dF (q * adelicArchGLIncl K (Γ s)) α‖ ≤ b₀ α := hle₀ _ hs₀ α
    unfold termDeriv
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add hA hB))
      (mul_le_mul htr hT (norm_nonneg _) ?_)).trans_eq rfl
    have h0 : (0 : ℝ) ≤ ‖((((∑ w : {w : InfinitePlace K // w.IsReal}, (1 / 2 : ℝ) * (coefR w.2 Γ (DR w.1 w.2) s).trace)
        + ∑ w : {w : InfinitePlace K // w.IsComplex}, (coefC w.2 Γ (DC w.1 w.2) s).trace.re : ℝ)) : ℂ)‖ :=
      norm_nonneg _
    exact h0.trans htr
  have hsum₀ : Summable fun α : Kˣ => seriesTerm d archR archC dR dC dF (q * adelicArchGLIncl K (Γ 0)) α := by
    rw [hmove₀]
    exact Summable.of_norm_bounded hb₀ fun α => hle₀ q (mem_of_mem_nhds hV₀) α
  have htsum : HasDerivAt (fun s : ℝ => ∑' α : Kˣ, seriesTerm d archR archC dR dC dF (q * adelicArchGLIncl K (Γ s)) α)
      (∑' α : Kˣ, termDeriv d archR archC dR dC dF dR' dC' Γ DR DC q 0 α) 0 :=
    hasDerivAt_tsum_of_isPreconnected hu_sum Metric.isOpen_ball (by rw [Real.ball_eq_Ioo]; exact isPreconnected_Ioo)
      (fun α s _ => hasDerivAt_seriesTerm_family d archR archC dR dC dF dR' hR'off hR'at dC' hC'off hC'at Γ DR DC
        hDR hDC q s α)
      (fun α s hs => hderiv_le s hs α) (Metric.mem_ball_self hε) hsum₀ (Metric.mem_ball_self hε)
  have hfun : (fun s : ℝ => jlSeries' d archR archC dR dC dF (q * adelicArchGLIncl K (Γ s))) =
      fun s => ∑' α : Kˣ, seriesTerm d archR archC dR dC dF (q * adelicArchGLIncl K (Γ s)) α := by
    funext s
    exact jlSeries'_eq_tsum_seriesTerm d archR archC dR dC dF _
  rw [hfun]
  convert htsum using 1
  have hsR : ∀ w : {w : InfinitePlace K // w.IsReal}, ∀ ι : Fin 2 × Fin 2,
      Summable fun α : Kˣ => seriesTerm d archR archC (dR' w.1 w.2 ι) dC dF q α := fun w ι =>
    Summable.of_norm_bounded (hbR (w, ι)) fun α => hleR (w, ι) q (mem_of_mem_nhds (hVR (w, ι))) α
  have hsC : ∀ w : {w : InfinitePlace K // w.IsComplex}, ∀ ι : (Fin 2 × Fin 2) × Fin 2,
      Summable fun α : Kˣ => seriesTerm d archR archC dR (dC' w.1 w.2 ι) dF q α := fun w ι =>
    Summable.of_norm_bounded (hbC (w, ι)) fun α => hleC (w, ι) q (mem_of_mem_nhds (hVC (w, ι))) α
  have hs₀ : Summable fun α : Kˣ => seriesTerm d archR archC dR dC dF q α := by
    simpa [hmove₀] using hsum₀
  have hR0 : ∀ w : {w : InfinitePlace K // w.IsReal}, coefR w.2 Γ (DR w.1 w.2) 0 = DR w.1 w.2 0 := fun w =>
    coefR_zero w.2 hΓ₀ _
  have hC0 : ∀ w : {w : InfinitePlace K // w.IsComplex}, coefC w.2 Γ (DC w.1 w.2) 0 = DC w.1 w.2 0 := fun w =>
    coefC_zero w.2 hΓ₀ _
  simp only [termDeriv, hmove₀, hR0, hC0, jlSeries'_eq_tsum_seriesTerm]
  have hA_s : Summable fun α : Kˣ => ∑ w : {w : InfinitePlace K // w.IsReal}, ∑ ι : Fin 2 × Fin 2,
      ((DR w.1 w.2 0 ι.1 ι.2 : ℝ) : ℂ) * seriesTerm d archR archC (dR' w.1 w.2 ι) dC dF q α :=
    summable_sum fun w _ => summable_sum fun ι _ => (hsR w ι).mul_left _
  have hB_s : Summable fun α : Kˣ => ∑ w : {w : InfinitePlace K // w.IsComplex}, ∑ ι : (Fin 2 × Fin 2) × Fin 2,
      ((cplxCoeff (DC w.1 w.2 0) ι : ℝ) : ℂ) * seriesTerm d archR archC dR (dC' w.1 w.2 ι) dF q α :=
    summable_sum fun w _ => summable_sum fun ι _ => (hsC w ι).mul_left _
  have hC_s : Summable fun α : Kˣ =>
      (((∑ w : {w : InfinitePlace K // w.IsReal}, (1 / 2 : ℝ) * (DR w.1 w.2 0).trace) +
          ∑ w : {w : InfinitePlace K // w.IsComplex}, (DC w.1 w.2 0).trace.re : ℝ) : ℂ) *
        seriesTerm d archR archC dR dC dF q α :=
    hs₀.mul_left _
  rw [(hA_s.add hB_s).tsum_sub hC_s, hA_s.tsum_add hB_s, tsum_mul_left,
    Summable.tsum_finsetSum fun w _ => summable_sum fun ι _ => (hsR w ι).mul_left _,
    Summable.tsum_finsetSum fun w _ => summable_sum fun ι _ => (hsC w ι).mul_left _]
  congr 2
  · exact Finset.sum_congr rfl fun w _ => by
      rw [Summable.tsum_finsetSum fun ι _ => (hsR w ι).mul_left _]
      exact Finset.sum_congr rfl fun ι _ => (tsum_mul_left).symm
  · exact Finset.sum_congr rfl fun w _ => by
      rw [Summable.tsum_finsetSum fun ι _ => (hsC w ι).mul_left _]
      exact Finset.sum_congr rfl fun ι _ => (tsum_mul_left).symm

private theorem cplxCoeff_cplxUnit (ι ι' : (Fin 2 × Fin 2) × Fin 2) :
    cplxCoeff (cplxUnit ι) ι' = if ι' = ι then 1 else 0 := by
  obtain ⟨⟨i, j⟩, k⟩ := ι
  obtain ⟨⟨i', j'⟩, k'⟩ := ι'
  by_cases hpos : i = i' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := hpos
    fin_cases k <;> fin_cases k' <;> simp [cplxCoeff, cplxUnit]
  · have hne : ((i', j'), k') ≠ ((i, j), k) := fun h => hpos ⟨by simp_all, by simp_all⟩
    rw [if_neg hne]
    simp only [cplxCoeff, cplxUnit]
    rw [Matrix.single_apply_of_ne i j _ i' j' hpos]
    simp

private theorem re_trace_cplxUnit (ι : (Fin 2 × Fin 2) × Fin 2) :
    (cplxUnit ι).trace.re = if ι.1.1 = ι.1.2 ∧ ι.2 = 0 then 1 else 0 := by
  obtain ⟨⟨i, j⟩, k⟩ := ι
  by_cases hij : i = j
  · subst hij
    fin_cases k <;> simp [cplxUnit, Matrix.trace_single_eq_same]
  · simp [cplxUnit, hij]

private theorem trace_single_one (ι : Fin 2 × Fin 2) :
    (Matrix.single ι.1 ι.2 (1 : ℝ)).trace = if ι.1 = ι.2 then 1 else 0 := by
  by_cases h : ι.1 = ι.2
  · rw [if_pos h]
    obtain ⟨i, j⟩ := ι
    simp only at h
    subst h
    exact Matrix.trace_single_eq_same _ _
  · rw [if_neg h]
    exact Matrix.trace_single_eq_of_ne _ _ _ h

private theorem exists_complexFamilies
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) :
    ∃ dC' : ∀ (w : InfinitePlace K), w.IsComplex → (Fin 2 × Fin 2) × Fin 2 →
        ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), ArchDatumC (archC w' hw'),
      (∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2) (w' : InfinitePlace K)
        (hw' : w'.IsComplex), w' ≠ w → dC' w hw ι w' hw' = dC w' hw') ∧
      ∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2) (g : Matrix (Fin 2) (Fin 2) ℂ),
        g.det ≠ 0 → (dC' w hw ι w hw).W g =
          fderivWithin ℝ (ArchC.asPi (dC w hw).W) ArchC.glSet (Matrix.of.symm g)
            (Matrix.of.symm (g * cplxUnit ι)) := by
  choose pick hpick using fun (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2) =>
    ArchDatumC.exists_W_eq_fderivWithin_mul (archC w hw) (dC w hw) (cplxUnit ι)
  refine ⟨fun w hw ι => Function.update (fun w' (hw' : w'.IsComplex) => dC w' hw') w (fun _ => pick w hw ι),
    ?_, ?_⟩
  · intro w hw ι w' hw' hne
    simp [Function.update_of_ne hne]
  · intro w hw ι g hg
    simp only [Function.update_self]
    exact hpick w hw ι g hg

private theorem exists_realFamilies
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw)) {w : InfinitePlace K} (hw : w.IsReal)
    (ι : Fin 2 × Fin 2) (dRι : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ArchDatumR (archR w' hw'))
    (hoff : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), w' ≠ w → dRι w' hw' = dR w' hw')
    (hat : ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      (dRι w hw).W g =
        fderivWithin ℝ (ArchR.asPi (dR w hw).W) ArchR.glSet (Matrix.of.symm g)
          (Matrix.of.symm (g * Matrix.single ι.1 ι.2 (1 : ℝ)))) :
    ∃ dR' : ∀ (w : InfinitePlace K), w.IsReal → Fin 2 × Fin 2 →
        ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ArchDatumR (archR w' hw'),
      dR' w hw ι = dRι ∧
      (∀ (w₁ : InfinitePlace K) (hw₁ : w₁.IsReal) (ι₁ : Fin 2 × Fin 2) (w' : InfinitePlace K) (hw' : w'.IsReal),
        w' ≠ w₁ → dR' w₁ hw₁ ι₁ w' hw' = dR w' hw') ∧
      ∀ (w₁ : InfinitePlace K) (hw₁ : w₁.IsReal) (ι₁ : Fin 2 × Fin 2) (g : Matrix (Fin 2) (Fin 2) ℝ), g.det ≠ 0 →
        (dR' w₁ hw₁ ι₁ w₁ hw₁).W g =
          fderivWithin ℝ (ArchR.asPi (dR w₁ hw₁).W) ArchR.glSet (Matrix.of.symm g)
            (Matrix.of.symm (g * Matrix.single ι₁.1 ι₁.2 (1 : ℝ))) := by
  choose pick hpick using fun (w₁ : InfinitePlace K) (hw₁ : w₁.IsReal) (ι₁ : Fin 2 × Fin 2) =>
    ArchDatumR.exists_W_eq_fderivWithin_mul (archR w₁ hw₁) (dR w₁ hw₁) (Matrix.single ι₁.1 ι₁.2 (1 : ℝ))
  refine ⟨fun w₁ hw₁ ι₁ => if w₁ = w ∧ ι₁ = ι then dRι else
    Function.update (fun w' (hw' : w'.IsReal) => dR w' hw') w₁ (fun _ => pick w₁ hw₁ ι₁), ?_, ?_, ?_⟩
  · simp
  · intro w₁ hw₁ ι₁ w' hw' hne
    dsimp only
    by_cases h : w₁ = w ∧ ι₁ = ι
    · rw [if_pos h]
      exact hoff w' hw' fun hw'' => hne (hw''.trans h.1.symm)
    · rw [if_neg h]
      simp [Function.update_of_ne hne]
  · intro w₁ hw₁ ι₁ g hg
    dsimp only
    by_cases h : w₁ = w ∧ ι₁ = ι
    · obtain ⟨rfl, rfl⟩ := h
      rw [if_pos (And.intro rfl rfl)]
      exact hat g hg
    · rw [if_neg h]
      simp only [Function.update_self]
      exact hpick w₁ hw₁ ι₁ g hg

private theorem exists_realFamilies_plain
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw)) :
    ∃ dR' : ∀ (w : InfinitePlace K), w.IsReal → Fin 2 × Fin 2 →
        ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ArchDatumR (archR w' hw'),
      (∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2) (w' : InfinitePlace K) (hw' : w'.IsReal),
        w' ≠ w → dR' w hw ι w' hw' = dR w' hw') ∧
      ∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2) (g : Matrix (Fin 2) (Fin 2) ℝ), g.det ≠ 0 →
        (dR' w hw ι w hw).W g =
          fderivWithin ℝ (ArchR.asPi (dR w hw).W) ArchR.glSet (Matrix.of.symm g)
            (Matrix.of.symm (g * Matrix.single ι.1 ι.2 (1 : ℝ))) := by
  choose pick hpick using fun (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2) =>
    ArchDatumR.exists_W_eq_fderivWithin_mul (archR w hw) (dR w hw) (Matrix.single ι.1 ι.2 (1 : ℝ))
  refine ⟨fun w hw ι => Function.update (fun w' (hw' : w'.IsReal) => dR w' hw') w (fun _ => pick w hw ι), ?_, ?_⟩
  · intro w hw ι w' hw' hne
    simp [Function.update_of_ne hne]
  · intro w hw ι g hg
    simp only [Function.update_self]
    exact hpick w hw ι g hg

private theorem exists_complexFamilies_with
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) {w : InfinitePlace K}
    (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2)
    (dCι : ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), ArchDatumC (archC w' hw'))
    (hoff : ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), w' ≠ w → dCι w' hw' = dC w' hw')
    (hat : ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.det ≠ 0 →
      (dCι w hw).W g =
        fderivWithin ℝ (ArchC.asPi (dC w hw).W) ArchC.glSet (Matrix.of.symm g) (Matrix.of.symm (g * cplxUnit ι))) :
    ∃ dC' : ∀ (w : InfinitePlace K), w.IsComplex → (Fin 2 × Fin 2) × Fin 2 →
        ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), ArchDatumC (archC w' hw'),
      dC' w hw ι = dCι ∧
      (∀ (w₁ : InfinitePlace K) (hw₁ : w₁.IsComplex) (ι₁ : (Fin 2 × Fin 2) × Fin 2) (w' : InfinitePlace K)
        (hw' : w'.IsComplex), w' ≠ w₁ → dC' w₁ hw₁ ι₁ w' hw' = dC w' hw') ∧
      ∀ (w₁ : InfinitePlace K) (hw₁ : w₁.IsComplex) (ι₁ : (Fin 2 × Fin 2) × Fin 2) (g : Matrix (Fin 2) (Fin 2) ℂ),
        g.det ≠ 0 → (dC' w₁ hw₁ ι₁ w₁ hw₁).W g =
          fderivWithin ℝ (ArchC.asPi (dC w₁ hw₁).W) ArchC.glSet (Matrix.of.symm g)
            (Matrix.of.symm (g * cplxUnit ι₁)) := by
  choose pick hpick using fun (w₁ : InfinitePlace K) (hw₁ : w₁.IsComplex) (ι₁ : (Fin 2 × Fin 2) × Fin 2) =>
    ArchDatumC.exists_W_eq_fderivWithin_mul (archC w₁ hw₁) (dC w₁ hw₁) (cplxUnit ι₁)
  refine ⟨fun w₁ hw₁ ι₁ => if w₁ = w ∧ ι₁ = ι then dCι else
    Function.update (fun w' (hw' : w'.IsComplex) => dC w' hw') w₁ (fun _ => pick w₁ hw₁ ι₁), ?_, ?_, ?_⟩
  · simp
  · intro w₁ hw₁ ι₁ w' hw' hne
    dsimp only
    by_cases h : w₁ = w ∧ ι₁ = ι
    · rw [if_pos h]
      exact hoff w' hw' fun hw'' => hne (hw''.trans h.1.symm)
    · rw [if_neg h]
      simp [Function.update_of_ne hne]
  · intro w₁ hw₁ ι₁ g hg
    dsimp only
    by_cases h : w₁ = w ∧ ι₁ = ι
    · obtain ⟨rfl, rfl⟩ := h
      rw [if_pos (And.intro rfl rfl)]
      exact hat g hg
    · rw [if_neg h]
      simp only [Function.update_self]
      exact hpick w₁ hw₁ ι₁ g hg

open scoped Classical in
private theorem hasDerivAt_jlSeries'_mul_adelicArchGLIncl_unitR {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Pi : HeckeEigensystem K ℂ} {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    {w : InfinitePlace K} (hw : w.IsReal) (ι : Fin 2 × Fin 2)
    (dRι : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ArchDatumR (archR w' hw'))
    (hoff : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), w' ≠ w → dRι w' hw' = dR w' hw')
    (hat : ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      (dRι w hw).W g =
        fderivWithin ℝ (ArchR.asPi (dR w hw).W) ArchR.glSet (Matrix.of.symm g)
          (Matrix.of.symm (g * Matrix.single ι.1 ι.2 (1 : ℝ))))
    (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K)) (hΓ₀ : Γ 0 = 1)
    (hΓc : ContinuousAt (fun s : ℝ => adelicArchGLIncl K (Γ s)) 0)
    (D : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hD₀ : D 0 = Matrix.single ι.1 ι.2 (1 : ℝ)) (hDc : ContinuousAt D 0)
    (hDw : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Matrix.of.symm (realComponent w hw (adelicArchGLIncl K (Γ s))))
      (Matrix.of.symm (D t)) t)
    (hR : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), w' ≠ w →
      ∀ s : ℝ, realComponent w' hw' (adelicArchGLIncl K (Γ s)) = 1)
    (hC : ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex),
      ∀ s : ℝ, complexComponent w' hw' (adelicArchGLIncl K (Γ s)) = 1)
    (q : AdelicGL2 (𝓞 K) K) :
    HasDerivAt (fun t : ℝ => jlSeries' d archR archC dR dC dF (q * adelicArchGLIncl K (Γ t)))
      (jlSeries' d archR archC dRι dC dF q -
        (if ι.1 = ι.2 then (1 / 2 : ℂ) else 0) * jlSeries' d archR archC dR dC dF q) 0 := by
  obtain ⟨dR', hkey, hR'off, hR'at⟩ := exists_realFamilies archR dR hw ι dRι hoff hat
  obtain ⟨dC', hC'off, hC'at⟩ := exists_complexFamilies archC dC
  set DR : ∀ (w' : InfinitePlace K), w'.IsReal → ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun w' _ => if w' = w then D else fun _ => 0 with hDRdef
  set DC : ∀ (w' : InfinitePlace K), w'.IsComplex → ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun _ _ _ => 0 with hDCdef
  have hDR : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal) (t : ℝ),
      HasDerivAt (fun s : ℝ => Matrix.of.symm (realComponent w' hw' (adelicArchGLIncl K (Γ s))))
        (Matrix.of.symm (DR w' hw' t)) t := by
    intro w' hw' t
    by_cases h : w' = w
    · subst h
      simp only [hDRdef, if_true]
      exact hDw t
    · simp only [hDRdef, if_neg h]
      have hfun : (fun s : ℝ => Matrix.of.symm (realComponent w' hw' (adelicArchGLIncl K (Γ s)))) =
          fun _ => Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ) := funext fun s => by rw [hR w' hw' h s]
      rw [hfun]
      exact hasDerivAt_const t _
  have hDC : ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex) (t : ℝ),
      HasDerivAt (fun s : ℝ => Matrix.of.symm (complexComponent w' hw' (adelicArchGLIncl K (Γ s))))
        (Matrix.of.symm (DC w' hw' t)) t := by
    intro w' hw' t
    have hfun : (fun s : ℝ => Matrix.of.symm (complexComponent w' hw' (adelicArchGLIncl K (Γ s)))) =
        fun _ => Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ) := funext fun s => by rw [hC w' hw' s]
    rw [hfun]
    exact hasDerivAt_const t _
  have hDRc : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ContinuousAt (DR w' hw') 0 := by
    intro w' hw'
    by_cases h : w' = w
    · subst h
      simpa only [hDRdef, if_true] using hDc
    · simp only [hDRdef, if_neg h]
      exact continuousAt_const
  have hDCc : ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), ContinuousAt (DC w' hw') 0 := fun _ _ =>
    continuousAt_const
  have h := hasDerivAt_jlSeries'_mul_adelicArchGLIncl hω hωb d archR archC dR dC dF hnice dR' hR'off hR'at dC' hC'off
    hC'at Γ hΓ₀ hΓc DR DC hDR hDC hDRc hDCc q
  convert h using 1
  have hDR0 : ∀ w' : {w' : InfinitePlace K // w'.IsReal},
      DR w'.1 w'.2 0 = if w'.1 = w then Matrix.single ι.1 ι.2 (1 : ℝ) else 0 := by
    intro w'
    by_cases hh : w'.1 = w <;> simp [hDRdef, hh, hD₀]
  have hcplx0 : ∀ ι' : (Fin 2 × Fin 2) × Fin 2, cplxCoeff (0 : Matrix (Fin 2) (Fin 2) ℂ) ι' = 0 := fun ι' => by
    simp [cplxCoeff]
  have hsumR : ∀ w' : {w' : InfinitePlace K // w'.IsReal},
      (∑ ι' : Fin 2 × Fin 2,
          ((DR w'.1 w'.2 0 ι'.1 ι'.2 : ℝ) : ℂ) * jlSeries' d archR archC (dR' w'.1 w'.2 ι') dC dF q) =
        if w'.1 = w then jlSeries' d archR archC dRι dC dF q else 0 := by
    intro w'
    rw [hDR0 w']
    by_cases hh : w'.1 = w
    · obtain ⟨w', hw''⟩ := w'
      simp only at hh
      subst hh
      rw [if_pos rfl, if_pos rfl, Finset.sum_eq_single ι]
      · rw [Matrix.single_apply_same, hkey]
        simp
      · intro ι' _ hne
        rw [Matrix.single_apply_of_ne ι.1 ι.2 (1 : ℝ) ι'.1 ι'.2 fun hh' => hne (Prod.ext hh'.1.symm hh'.2.symm)]
        simp
      · intro habs
        exact absurd (Finset.mem_univ ι) habs
    · rw [if_neg hh, if_neg hh]
      simp
  have htrR : ∀ w' : {w' : InfinitePlace K // w'.IsReal},
      (1 / 2 : ℝ) * (DR w'.1 w'.2 0).trace = if w'.1 = w then (1 / 2 : ℝ) * (if ι.1 = ι.2 then 1 else 0) else 0 := by
    intro w'
    rw [hDR0 w']
    by_cases hh : w'.1 = w
    · rw [if_pos hh, if_pos hh, trace_single_one]
    · rw [if_neg hh, if_neg hh]
      simp
  simp only [hsumR, htrR, hDCdef, hcplx0, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, Matrix.trace_zero,
    Complex.zero_re, add_zero]
  have hcollapse : ∀ {M : Type} [AddCommMonoid M] (x : M),
      (∑ w' : {w' : InfinitePlace K // w'.IsReal}, (if w'.1 = w then x else 0)) = x := by
    intro M _ x
    rw [Finset.sum_eq_single ⟨w, hw⟩]
    · simp
    · intro w' _ hne
      exact if_neg fun hh => hne (Subtype.ext hh)
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  rw [hcollapse, hcollapse]
  push_cast
  split_ifs <;> simp

open scoped Classical in
private theorem hasDerivAt_jlSeries'_mul_adelicArchGLIncl_unitC {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Pi : HeckeEigensystem K ℂ} {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    {w : InfinitePlace K} (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2)
    (dCι : ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), ArchDatumC (archC w' hw'))
    (hoff : ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), w' ≠ w → dCι w' hw' = dC w' hw')
    (hat : ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.det ≠ 0 →
      (dCι w hw).W g =
        fderivWithin ℝ (ArchC.asPi (dC w hw).W) ArchC.glSet (Matrix.of.symm g) (Matrix.of.symm (g * cplxUnit ι)))
    (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K)) (hΓ₀ : Γ 0 = 1)
    (hΓc : ContinuousAt (fun s : ℝ => adelicArchGLIncl K (Γ s)) 0)
    (D : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (hD₀ : D 0 = cplxUnit ι) (hDc : ContinuousAt D 0)
    (hDw : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Matrix.of.symm (complexComponent w hw (adelicArchGLIncl K (Γ s))))
      (Matrix.of.symm (D t)) t)
    (hR : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ∀ s : ℝ, realComponent w' hw' (adelicArchGLIncl K (Γ s)) = 1)
    (hC : ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), w' ≠ w →
      ∀ s : ℝ, complexComponent w' hw' (adelicArchGLIncl K (Γ s)) = 1)
    (q : AdelicGL2 (𝓞 K) K) :
    HasDerivAt (fun t : ℝ => jlSeries' d archR archC dR dC dF (q * adelicArchGLIncl K (Γ t)))
      (jlSeries' d archR archC dR dCι dF q -
        (if ι.1.1 = ι.1.2 ∧ ι.2 = 0 then (1 : ℂ) else 0) * jlSeries' d archR archC dR dC dF q) 0 := by
  obtain ⟨dR', hR'off, hR'at⟩ := exists_realFamilies_plain archR dR
  obtain ⟨dC', hkey, hC'off, hC'at⟩ := exists_complexFamilies_with archC dC hw ι dCι hoff hat
  set DR : ∀ (w' : InfinitePlace K), w'.IsReal → ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun _ _ _ => 0 with hDRdef
  set DC : ∀ (w' : InfinitePlace K), w'.IsComplex → ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun w' _ => if w' = w then D else fun _ => 0 with hDCdef
  have hDR : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal) (t : ℝ),
      HasDerivAt (fun s : ℝ => Matrix.of.symm (realComponent w' hw' (adelicArchGLIncl K (Γ s))))
        (Matrix.of.symm (DR w' hw' t)) t := by
    intro w' hw' t
    have hfun : (fun s : ℝ => Matrix.of.symm (realComponent w' hw' (adelicArchGLIncl K (Γ s)))) =
        fun _ => Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ) := funext fun s => by rw [hR w' hw' s]
    rw [hfun]
    exact hasDerivAt_const t _
  have hDC : ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex) (t : ℝ),
      HasDerivAt (fun s : ℝ => Matrix.of.symm (complexComponent w' hw' (adelicArchGLIncl K (Γ s))))
        (Matrix.of.symm (DC w' hw' t)) t := by
    intro w' hw' t
    by_cases h : w' = w
    · subst h
      simp only [hDCdef, if_true]
      exact hDw t
    · simp only [hDCdef, if_neg h]
      have hfun : (fun s : ℝ => Matrix.of.symm (complexComponent w' hw' (adelicArchGLIncl K (Γ s)))) =
          fun _ => Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ) := funext fun s => by rw [hC w' hw' h s]
      rw [hfun]
      exact hasDerivAt_const t _
  have hDRc : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ContinuousAt (DR w' hw') 0 := fun _ _ =>
    continuousAt_const
  have hDCc : ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), ContinuousAt (DC w' hw') 0 := by
    intro w' hw'
    by_cases h : w' = w
    · subst h
      simpa only [hDCdef, if_true] using hDc
    · simp only [hDCdef, if_neg h]
      exact continuousAt_const
  have h := hasDerivAt_jlSeries'_mul_adelicArchGLIncl hω hωb d archR archC dR dC dF hnice dR' hR'off hR'at dC' hC'off
    hC'at Γ hΓ₀ hΓc DR DC hDR hDC hDRc hDCc q
  convert h using 1
  have hDC0 : ∀ w' : {w' : InfinitePlace K // w'.IsComplex}, DC w'.1 w'.2 0 = if w'.1 = w then cplxUnit ι else 0 := by
    intro w'
    by_cases hh : w'.1 = w <;> simp [hDCdef, hh, hD₀]
  have hsumC : ∀ w' : {w' : InfinitePlace K // w'.IsComplex},
      (∑ ι' : (Fin 2 × Fin 2) × Fin 2,
          ((cplxCoeff (DC w'.1 w'.2 0) ι' : ℝ) : ℂ) * jlSeries' d archR archC dR (dC' w'.1 w'.2 ι') dF q) =
        if w'.1 = w then jlSeries' d archR archC dR dCι dF q else 0 := by
    intro w'
    rw [hDC0 w']
    by_cases hh : w'.1 = w
    · obtain ⟨w', hw''⟩ := w'
      simp only at hh
      subst hh
      rw [if_pos rfl, if_pos rfl]
      simp only [cplxCoeff_cplxUnit]
      rw [Finset.sum_eq_single ι]
      · rw [if_pos rfl, hkey]
        simp
      · intro ι' _ hne
        rw [if_neg hne]
        simp
      · intro habs
        exact absurd (Finset.mem_univ ι) habs
    · rw [if_neg hh, if_neg hh]
      simp [cplxCoeff]
  have htrC : ∀ w' : {w' : InfinitePlace K // w'.IsComplex},
      (DC w'.1 w'.2 0).trace.re = if w'.1 = w then (if ι.1.1 = ι.1.2 ∧ ι.2 = 0 then (1 : ℝ) else 0) else 0 := by
    intro w'
    rw [hDC0 w']
    by_cases hh : w'.1 = w
    · rw [if_pos hh, if_pos hh, re_trace_cplxUnit]
    · rw [if_neg hh, if_neg hh]
      simp
  simp only [hsumC, htrC, hDRdef, Matrix.zero_apply, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero,
    Matrix.trace_zero, mul_zero, zero_add]
  have hcollapse : ∀ {M : Type} [AddCommMonoid M] (x : M),
      (∑ w' : {w' : InfinitePlace K // w'.IsComplex}, (if w'.1 = w then x else 0)) = x := by
    intro M _ x
    rw [Finset.sum_eq_single ⟨w, hw⟩]
    · simp
    · intro w' _ hne
      exact if_neg fun hh => hne (Subtype.ext hh)
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  rw [hcollapse, hcollapse]
  push_cast
  split_ifs <;> simp

end TermwiseDerivative

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.FiniteWhittaker"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section ULevel

open scoped WithZero Classical

private theorem theForm_mul_eq_of_upperLeft {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K (∏ v : ↥S, v.1.asIdeal ^ d.m v) ⊓ finiteAdelicGL2Subgroup K)
    (h00 : ∀ v : ↥S, Valued.v (componentMatrix v.1 u 0 0 - 1) ≤ WithZero.exp (-(d.m v : ℤ)))
    (g : AdelicGL2 (𝓞 K) K) :
    theForm d archR archC dR dC dF (g * u) = theForm d archR archC dR dC dF g := by
  classical
  have hWf : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K,
      dF.Wf (g * u) = dF.Wf g := fun g u hu => FiniteWhittaker.wf_mul_of_mem_integral dF g hu
  set N : Ideal (𝓞 K) := ∏ v : ↥S, v.1.asIdeal ^ d.m v with hNdef
  have hN : N ≠ ⊥ := by
    rw [hNdef, Submodule.zero_eq_bot.symm, Finset.prod_ne_zero_iff]
    exact fun v _ => pow_ne_zero _ (by rw [Submodule.zero_eq_bot]; exact v.1.ne_bot)
  have hNv : ∀ v : ↥S, idealBound (𝓞 K) N v.1 ≤ WithZero.exp (-(d.m v : ℤ)) := fun v =>
    idealBound_le_of_pow_dvd hN (Finset.dvd_prod_of_mem (fun w : ↥S => w.1.asIdeal ^ d.m w) (Finset.mem_univ v))
  have h := theForm_mul_of_mem_levelOne d archR archC dR dC dF hinv hWf hNv Finset.univ u hu
    (fun v hv => absurd (Finset.mem_univ v) hv) g
  rw [h, Finset.prod_eq_one (fun v _ => kChar_componentMatrix_eq_one d v (hNv v) (Subgroup.mem_inf.mp hu).1 (h00 v)),
    one_mul]

private theorem valuation_sub_one_le_of_det_eq_one {v : HeightOneSpectrum (𝓞 K)}
    {M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} {e : WithZero (Multiplicative ℤ)}
    (h00 : Valued.v (M 0 0) ≤ 1) (h01 : Valued.v (M 0 1) ≤ 1) (h10 : Valued.v (M 1 0) ≤ e)
    (h11 : Valued.v (M 1 1 - 1) ≤ e) (hdet : M.det = 1) : Valued.v (M 0 0 - 1) ≤ e := by
  have e1 : M 0 0 - 1 = M 0 0 * (1 - M 1 1) + M 0 1 * M 1 0 := by
    rw [Matrix.det_fin_two] at hdet
    linear_combination hdet
  rw [e1]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul, Valuation.map_sub_swap]
    calc Valued.v (M 0 0) * Valued.v (M 1 1 - 1) ≤ 1 * e := mul_le_mul' h00 h11
      _ = e := one_mul _
  · rw [map_mul]
    calc Valued.v (M 0 1) * Valued.v (M 1 0) ≤ 1 * e := mul_le_mul' h01 h10
      _ = e := one_mul _

private theorem theForm_mul_eq_of_det_eq_one {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K (∏ v : ↥S, v.1.asIdeal ^ d.m v) ⊓ finiteAdelicGL2Subgroup K)
    (hdet : Matrix.GeneralLinearGroup.det u = 1) (g : AdelicGL2 (𝓞 K) K) :
    theForm d archR archC dR dC dF (g * u) = theForm d archR archC dR dC dF g := by
  classical
  set N : Ideal (𝓞 K) := ∏ v : ↥S, v.1.asIdeal ^ d.m v with hNdef
  have hN : N ≠ ⊥ := by
    rw [hNdef, Submodule.zero_eq_bot.symm, Finset.prod_ne_zero_iff]
    exact fun v _ => pow_ne_zero _ (by rw [Submodule.zero_eq_bot]; exact v.1.ne_bot)
  have hNv : ∀ v : ↥S, idealBound (𝓞 K) N v.1 ≤ WithZero.exp (-(d.m v : ℤ)) := fun v =>
    idealBound_le_of_pow_dvd hN (Finset.dvd_prod_of_mem (fun w : ↥S => w.1.asIdeal ^ d.m w) (Finset.mem_univ v))
  refine theForm_mul_eq_of_upperLeft d archR archC dR dC dF hinv hu (fun v => ?_) g
  have hlv : AdelicDock.IsLocalLevelOne (𝓞 K) K v.1 N (componentMatrix v.1 u) :=
    isLocalLevelOne_componentMatrix (Subgroup.mem_inf.mp hu).1 v.1
  have hle : ∀ i j, Valued.v (componentMatrix v.1 u i j) ≤ 1 := fun i j =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hlv.integral i j)
  have hdet' : (componentMatrix v.1 u).det = 1 := by
    rw [componentMatrix_eq_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one, map_one]
  exact valuation_sub_one_le_of_det_eq_one (hle 0 0) (hle 0 1) (hlv.lowerLeft.trans (hNv v))
    (hlv.lowerRight.trans (hNv v)) hdet'

end ULevel

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section UnitCurves

section Generic

variable {𝕜 : Type} [Field 𝕜]

private theorem one_add_smul_single_mul (i j : Fin 2) (a b : 𝕜) :
    (1 + a • Matrix.single i j (1 : 𝕜)) * (1 + b • Matrix.single i j (1 : 𝕜))
      = 1 + (a + b + if i = j then a * b else 0) • Matrix.single i j (1 : 𝕜) := by
  by_cases hij : i = j
  · subst hij
    simp only [if_true, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.single_mul_single_same, add_smul, mul_one, mul_comm]
    abel
  ·
    have hz : Matrix.single i j (1 : 𝕜) * Matrix.single i j (1 : 𝕜) = 0 :=
      Matrix.single_mul_single_of_ne (1 : 𝕜) i j i (Ne.symm hij) (1 : 𝕜)
    simp only [hij, if_false, add_zero, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hz,
      smul_zero, add_smul]
    abel

private def InvLaw (diag : Prop) [Decidable diag] (φ : ℝ → 𝕜) : Prop :=
  ∀ t, φ t + φ (-t) + (if diag then φ t * φ (-t) else 0) = 0

private def unitCurveOf (i j : Fin 2) (φ : ℝ → 𝕜) (hφ : InvLaw (i = j) φ) (t : ℝ) : GL (Fin 2) 𝕜 :=
  Units.mk (1 + φ t • Matrix.single i j (1 : 𝕜)) (1 + φ (-t) • Matrix.single i j (1 : 𝕜))
    (by rw [one_add_smul_single_mul, hφ t, zero_smul, add_zero])
    (by
      rw [one_add_smul_single_mul]
      have h := hφ t
      rw [add_comm (φ t) (φ (-t)), mul_comm] at h
      rw [h, zero_smul, add_zero])

private theorem coe_unitCurveOf (i j : Fin 2) (φ : ℝ → 𝕜) (hφ : InvLaw (i = j) φ) (t : ℝ) :
    ((unitCurveOf i j φ hφ t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) = 1 + φ t • Matrix.single i j (1 : 𝕜) :=
  rfl

private theorem coe_unitCurveOf_inv (i j : Fin 2) (φ : ℝ → 𝕜) (hφ : InvLaw (i = j) φ) (t : ℝ) :
    (((unitCurveOf i j φ hφ t)⁻¹ : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜)
      = 1 + φ (-t) • Matrix.single i j (1 : 𝕜) :=
  rfl

private theorem unitCurveOf_zero (i j : Fin 2) (φ : ℝ → 𝕜) (hφ : InvLaw (i = j) φ) (h0 : φ 0 = 0) :
    unitCurveOf i j φ hφ 0 = 1 := by
  apply Units.ext
  rw [coe_unitCurveOf, h0, zero_smul, add_zero, Units.val_one]

private theorem continuous_unitCurveOf [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] (i j : Fin 2) (φ : ℝ → 𝕜)
    (hφ : InvLaw (i = j) φ) (hc : Continuous φ) : Continuous (unitCurveOf i j φ hφ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simp only [Function.comp_def, coe_unitCurveOf]
    exact continuous_const.add (hc.smul continuous_const)
  · simp only [coe_unitCurveOf_inv]
    exact continuous_const.add ((hc.comp continuous_neg).smul continuous_const)

end Generic

section Derivative

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]

private theorem hasDerivAt_unitCurveOf (i j : Fin 2) (φ : ℝ → 𝕜)
    (hφ : InvLaw (i = j) φ) {φ' : ℝ → 𝕜} (hd : ∀ t, HasDerivAt φ (φ' t) t) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Matrix.of.symm ((unitCurveOf i j φ hφ s : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜))
      (Matrix.of.symm (φ' t • Matrix.single i j (1 : 𝕜))) t := by
  rw [hasDerivAt_pi]
  intro a
  rw [hasDerivAt_pi]
  intro b
  simp only [coe_unitCurveOf, Matrix.of_symm_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact ((hd t).mul_const (Matrix.single i j (1 : 𝕜) a b)).const_add ((1 : Matrix (Fin 2) (Fin 2) 𝕜) a b)

end Derivative

private noncomputable def realScalar (diag : Prop) [Decidable diag] (t : ℝ) : ℝ :=
  if diag then Real.exp t - 1 else t

private theorem realScalar_invLaw (diag : Prop) [Decidable diag] : InvLaw diag (realScalar diag) := by
  intro t
  unfold realScalar
  split_ifs
  · have h : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [h]
  · ring

private theorem realScalar_zero (diag : Prop) [Decidable diag] : realScalar diag 0 = 0 := by
  unfold realScalar; split_ifs <;> simp

private theorem hasDerivAt_realScalar (diag : Prop) [Decidable diag] (t : ℝ) :
    HasDerivAt (realScalar diag) (if diag then Real.exp t else 1) t := by
  unfold realScalar
  split_ifs
  · simpa using (Real.hasDerivAt_exp t).sub_const 1
  · exact hasDerivAt_id' t

private noncomputable def cplxScalar (diag : Prop) [Decidable diag] (u : ℂ) (t : ℝ) : ℂ :=
  if diag then Complex.exp (u * t) - 1 else u * t

private theorem cplxScalar_invLaw (diag : Prop) [Decidable diag] (u : ℂ) : InvLaw diag (cplxScalar diag u) := by
  intro t
  unfold cplxScalar
  split_ifs
  · have h : Complex.exp (u * t) * Complex.exp (u * (-t : ℝ)) = 1 := by
      rw [← Complex.exp_add, Complex.ofReal_neg, mul_neg, add_neg_cancel, Complex.exp_zero]
    linear_combination h
  · push_cast; ring

private theorem cplxScalar_zero (diag : Prop) [Decidable diag] (u : ℂ) : cplxScalar diag u 0 = 0 := by
  unfold cplxScalar; split_ifs <;> simp

private theorem hasDerivAt_cplxScalar (diag : Prop) [Decidable diag] (u : ℂ) (t : ℝ) :
    HasDerivAt (cplxScalar diag u) (if diag then u * Complex.exp (u * t) else u) t := by
  unfold cplxScalar
  split_ifs
  ·
    have h : HasDerivAt (fun z : ℂ => Complex.exp (u * z) - 1) (u * Complex.exp (u * t)) (t : ℂ) := by
      have h1 := (Complex.hasDerivAt_exp (u * t)).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).const_mul u)
      simpa [mul_comm] using h1.sub_const 1
    exact h.comp_ofReal
  · simpa using ((hasDerivAt_id t).ofReal_comp).const_mul u

end UnitCurves
section Placement

private theorem realComponent_archGLIncl_of_ne {w w' : InfinitePlace K} (hw' : w'.IsReal) (hne : w' ≠ w)
    (k : GL (Fin 2) w.Completion) :
    realComponent w' hw' (adelicArchGLIncl K (AutomorphicForm.archGLIncl K w k)) = 1 := by
  rw [realComponent_eq_map, glArch_adelicArchGLIncl, archComponent_archGLIncl_of_ne K hne, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

private theorem complexComponent_archGLIncl_of_ne {w w' : InfinitePlace K} (hw' : w'.IsComplex) (hne : w' ≠ w)
    (k : GL (Fin 2) w.Completion) :
    complexComponent w' hw' (adelicArchGLIncl K (AutomorphicForm.archGLIncl K w k)) = 1 := by
  rw [complexComponent_eq_map, glArch_adelicArchGLIncl, archComponent_archGLIncl_of_ne K hne, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

private theorem coe_adelicArchGLIncl_apply (k : GL (Fin 2) (InfiniteAdeleRing K)) (i j : Fin 2) :
    ((adelicArchGLIncl K k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      (((k : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) :=
  rfl

private theorem continuous_adelicArchGLIncl_comp {Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K)} (hΓ : Continuous Γ) :
    Continuous fun t : ℝ => adelicArchGLIncl K (Γ t) := by
  have hval : ∀ (Δ : ℝ → GL (Fin 2) (InfiniteAdeleRing K)), Continuous Δ →
      Continuous fun t : ℝ =>
        ((adelicArchGLIncl K (Δ t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    intro Δ hΔ
    refine continuous_matrix fun i j => ?_
    simp only [coe_adelicArchGLIncl_apply]
    have hm : Continuous fun t : ℝ => ((Δ t : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := Units.continuous_val.comp hΔ
    exact (((continuous_apply j).comp ((continuous_apply i).comp hm)).prodMk continuous_const)
  refine Units.continuous_iff.2 ⟨hval Γ hΓ, ?_⟩
  have : (fun t : ℝ => (((adelicArchGLIncl K (Γ t))⁻¹ : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) =
      fun t : ℝ => ((adelicArchGLIncl K ((Γ t)⁻¹) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    funext fun t => by rw [map_inv]
  rw [this]
  exact hval (fun t => (Γ t)⁻¹) (Units.continuous_iff.2 ⟨Units.continuous_coe_inv.comp hΓ,
    by simpa only [inv_inv, Function.comp_def] using Units.continuous_val.comp hΓ⟩)

private theorem continuous_archGLIncl_comp (w : InfinitePlace K) {κ : ℝ → GL (Fin 2) w.Completion}
    (hκ : Continuous κ) : Continuous fun t : ℝ => AutomorphicForm.archGLIncl K w (κ t) := by
  have hval : ∀ (κ' : ℝ → GL (Fin 2) w.Completion), Continuous κ' →
      Continuous fun t : ℝ => ((AutomorphicForm.archGLIncl K w (κ' t) : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
    intro κ' hκ'
    refine continuous_matrix fun i j => ?_
    show Continuous fun t : ℝ => AutomorphicForm.archMatrixUpdate K w (κ' t : Matrix (Fin 2) (Fin 2) w.Completion) i j
    refine continuous_pi fun v => ?_
    have hm : Continuous fun t : ℝ => ((κ' t : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) :=
      Units.continuous_val.comp hκ'
    by_cases hv : v = w
    · subst hv
      simp only [AutomorphicForm.archMatrixUpdate_apply_self]
      exact (continuous_apply j).comp ((continuous_apply i).comp hm)
    · simp only [AutomorphicForm.archMatrixUpdate_apply_of_ne K w _ i j hv]
      exact continuous_const
  refine Units.continuous_iff.2 ⟨hval κ hκ, ?_⟩
  have : (fun t : ℝ => (((AutomorphicForm.archGLIncl K w (κ t))⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) =
      fun t : ℝ => ((AutomorphicForm.archGLIncl K w ((κ t)⁻¹) : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    funext fun t => by rw [map_inv]
  rw [this]
  exact hval (fun t => (κ t)⁻¹) (Units.continuous_iff.2 ⟨Units.continuous_coe_inv.comp hκ,
    by simpa only [inv_inv, Function.comp_def] using Units.continuous_val.comp hκ⟩)

private theorem continuous_glMap_comp {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] [IsTopologicalRing S] (f : R →+* S) (hf : Continuous f) {c : ℝ → GL (Fin 2) R}
    (hc : Continuous c) : Continuous fun t : ℝ => Matrix.GeneralLinearGroup.map f (c t) := by
  have hval : ∀ (c' : ℝ → GL (Fin 2) R), Continuous c' →
      Continuous fun t : ℝ =>
        ((Matrix.GeneralLinearGroup.map f (c' t) : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) := by
    intro c' hc'
    refine continuous_matrix fun i j => ?_
    show Continuous fun t : ℝ => f (((c' t : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j)
    have hm : Continuous fun t : ℝ => ((c' t : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) :=
      Units.continuous_val.comp hc'
    exact hf.comp ((continuous_apply j).comp ((continuous_apply i).comp hm))
  refine Units.continuous_iff.2 ⟨hval c hc, ?_⟩
  have : (fun t : ℝ => (((Matrix.GeneralLinearGroup.map f (c t))⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)) =
      fun t : ℝ => ((Matrix.GeneralLinearGroup.map f ((c t)⁻¹) : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) :=
    funext fun t => by rw [map_inv]
  rw [this]
  exact hval (fun t => (c t)⁻¹) (Units.continuous_iff.2 ⟨Units.continuous_coe_inv.comp hc,
    by simpa only [inv_inv, Function.comp_def] using Units.continuous_val.comp hc⟩)

private theorem realComponent_place {w : InfinitePlace K} (hw : w.IsReal) (c : GL (Fin 2) ℝ) :
    realComponent w hw (adelicArchGLIncl K (AutomorphicForm.archGLIncl K w (Matrix.GeneralLinearGroup.map
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom c))) =
      (c : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [realComponent_eq_map, glArch_adelicArchGLIncl, archComponent_archGLIncl_self]
  ext i j
  exact (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).apply_symm_apply _

private theorem complexComponent_place {w : InfinitePlace K} (hw : w.IsComplex) (c : GL (Fin 2) ℂ) :
    complexComponent w hw (adelicArchGLIncl K (AutomorphicForm.archGLIncl K w (Matrix.GeneralLinearGroup.map
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom c))) =
      (c : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [complexComponent_eq_map, glArch_adelicArchGLIncl, archComponent_archGLIncl_self]
  ext i j
  exact (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).apply_symm_apply _

private theorem continuous_realIso_symm {w : InfinitePlace K} (hw : w.IsReal) :
    Continuous (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm :=
  (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous

private theorem continuous_complexIso_symm {w : InfinitePlace K} (hw : w.IsComplex) :
    Continuous (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm :=
  (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous

private theorem isReal_ne_of_isComplex {w w' : InfinitePlace K} (hw : w.IsReal) (hw' : w'.IsComplex) : w' ≠ w :=
  fun h => (NumberField.InfinitePlace.not_isReal_iff_isComplex.2 hw') (h ▸ hw)

private theorem continuous_realScalar (diag : Prop) [Decidable diag] : Continuous (realScalar diag) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_realScalar diag t).continuousAt

private theorem continuous_cplxScalar (diag : Prop) [Decidable diag] (u : ℂ) : Continuous (cplxScalar diag u) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_cplxScalar diag u t).continuousAt

end Placement

section UnitCurveExistence

private theorem exists_unit_curve_real {w : InfinitePlace K} (hw : w.IsReal) (ι : Fin 2 × Fin 2) :
    ∃ (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K)) (D : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
      Γ 0 = 1 ∧
      ContinuousAt (fun s : ℝ => adelicArchGLIncl K (Γ s)) 0 ∧
      D 0 = Matrix.single ι.1 ι.2 (1 : ℝ) ∧
      ContinuousAt D 0 ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => Matrix.of.symm (realComponent w hw (adelicArchGLIncl K (Γ s))))
        (Matrix.of.symm (D t)) t) ∧
      (∀ (w' : InfinitePlace K) (hw' : w'.IsReal), w' ≠ w →
        ∀ s : ℝ, realComponent w' hw' (adelicArchGLIncl K (Γ s)) = 1) ∧
      (∀ (w' : InfinitePlace K) (hw' : w'.IsComplex),
        ∀ s : ℝ, complexComponent w' hw' (adelicArchGLIncl K (Γ s)) = 1) := by
  classical
  set φ : ℝ → ℝ := realScalar (ι.1 = ι.2) with hφdef
  set c : ℝ → GL (Fin 2) ℝ := unitCurveOf ι.1 ι.2 φ (realScalar_invLaw _) with hcdef
  set ρ := (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom with hρdef
  refine ⟨fun t => AutomorphicForm.archGLIncl K w (Matrix.GeneralLinearGroup.map ρ (c t)),
    fun t => (if ι.1 = ι.2 then Real.exp t else 1) • Matrix.single ι.1 ι.2 (1 : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h0 : c 0 = 1 := unitCurveOf_zero _ _ _ _ (realScalar_zero _)
    simp only [h0, map_one]
  · refine (continuous_adelicArchGLIncl_comp (continuous_archGLIncl_comp w (continuous_glMap_comp ρ
      (continuous_realIso_symm hw) ?_))).continuousAt
    exact continuous_unitCurveOf _ _ _ _ (continuous_realScalar _)
  · simp
  · refine Continuous.continuousAt ?_
    split_ifs
    · exact Real.continuous_exp.smul continuous_const
    · exact continuous_const
  · intro t
    have hfun : (fun s : ℝ => Matrix.of.symm (realComponent w hw (adelicArchGLIncl K
        (AutomorphicForm.archGLIncl K w (Matrix.GeneralLinearGroup.map ρ (c s)))))) =
        fun s : ℝ => Matrix.of.symm ((c s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
      funext fun s => by rw [realComponent_place]
    rw [hfun]
    exact hasDerivAt_unitCurveOf _ _ _ _ (hasDerivAt_realScalar _) t
  · intro w' hw' hne s
    exact realComponent_archGLIncl_of_ne hw' hne _
  · intro w' hw' s
    exact complexComponent_archGLIncl_of_ne hw' (isReal_ne_of_isComplex hw hw') _

private theorem exists_unit_curve_complex {w : InfinitePlace K} (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2) :
    ∃ (Γ : ℝ → GL (Fin 2) (InfiniteAdeleRing K)) (D : ℝ → Matrix (Fin 2) (Fin 2) ℂ),
      Γ 0 = 1 ∧
      ContinuousAt (fun s : ℝ => adelicArchGLIncl K (Γ s)) 0 ∧
      D 0 = cplxUnit ι ∧
      ContinuousAt D 0 ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => Matrix.of.symm (complexComponent w hw (adelicArchGLIncl K (Γ s))))
        (Matrix.of.symm (D t)) t) ∧
      (∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ∀ s : ℝ, realComponent w' hw' (adelicArchGLIncl K (Γ s)) = 1) ∧
      (∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), w' ≠ w →
        ∀ s : ℝ, complexComponent w' hw' (adelicArchGLIncl K (Γ s)) = 1) := by
  classical
  set u : ℂ := if ι.2 = 0 then (1 : ℂ) else Complex.I with hudef
  set φ : ℝ → ℂ := cplxScalar (ι.1.1 = ι.1.2) u with hφdef
  set c : ℝ → GL (Fin 2) ℂ := unitCurveOf ι.1.1 ι.1.2 φ (cplxScalar_invLaw _ u) with hcdef
  set ρ := (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom with hρdef
  refine ⟨fun t => AutomorphicForm.archGLIncl K w (Matrix.GeneralLinearGroup.map ρ (c t)),
    fun t => (if ι.1.1 = ι.1.2 then u * Complex.exp (u * t) else u) • Matrix.single ι.1.1 ι.1.2 (1 : ℂ),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h0 : c 0 = 1 := unitCurveOf_zero _ _ _ _ (cplxScalar_zero _ _)
    simp only [h0, map_one]
  · refine (continuous_adelicArchGLIncl_comp (continuous_archGLIncl_comp w (continuous_glMap_comp ρ
      (continuous_complexIso_symm hw) ?_))).continuousAt
    exact continuous_unitCurveOf _ _ _ _ (continuous_cplxScalar _ u)
  ·
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, ite_self, cplxUnit, hudef]
    ext i j
    simp [Matrix.single_apply]
  · refine Continuous.continuousAt ?_
    split_ifs
    · exact (continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
        Complex.continuous_ofReal))).smul continuous_const
    · exact continuous_const
  · intro t
    have hfun : (fun s : ℝ => Matrix.of.symm (complexComponent w hw (adelicArchGLIncl K
        (AutomorphicForm.archGLIncl K w (Matrix.GeneralLinearGroup.map ρ (c s)))))) =
        fun s : ℝ => Matrix.of.symm ((c s : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
      funext fun s => by rw [complexComponent_place]
    rw [hfun]
    exact hasDerivAt_unitCurveOf _ _ _ _ (hasDerivAt_cplxScalar _ u) t
  · intro w' hw' s
    exact realComponent_archGLIncl_of_ne hw' (fun h => (isReal_ne_of_isComplex hw' hw) h.symm) _
  · intro w' hw' hne s
    exact complexComponent_archGLIncl_of_ne hw' hne _

end UnitCurveExistence

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

private theorem mem_kZeroSet_mul_adelicArchGLIncl (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ↥S → ℕ)
    {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ kZeroSet S m) (x : GL (Fin 2) (InfiniteAdeleRing K)) :
    g * AutomorphicForm.adelicArchGLIncl K x ∈ kZeroSet S m := by
  rw [mem_kZeroSet_iff] at hg ⊢
  intro v
  have hc : componentMatrix v.1 (g * AutomorphicForm.adelicArchGLIncl K x) = componentMatrix v.1 g :=
    componentMatrix_eq_of_glFin_eq (by rw [map_mul, AutomorphicForm.glFin_adelicArchGLIncl, mul_one]) v.1
  unfold MemZK0At
  rw [hc]
  exact hg v
private theorem invOn_of_forall_hasDerivAt (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ↥S → ℕ)
    {F F' : AdelicGL2 (𝓞 K) K → ℂ} {c : ℝ → GL (Fin 2) (InfiniteAdeleRing K)}
    (hF' : ∀ q : AdelicGL2 (𝓞 K) K,
      HasDerivAt (fun t : ℝ => F (q * AutomorphicForm.adelicArchGLIncl K (c t))) (F' q) 0)
    (hinv : InvOn (kZeroSet S m) F) : InvOn (kZeroSet S m) F' := by
  intro γ g hg hγg
  have hcurve : (fun t : ℝ =>
        F (globalPoints (𝓞 K) K γ * g * AutomorphicForm.adelicArchGLIncl K (c t)))
      = fun t : ℝ => F (g * AutomorphicForm.adelicArchGLIncl K (c t)) := by
    funext t
    rw [mul_assoc]
    exact hinv γ _ (mem_kZeroSet_mul_adelicArchGLIncl S m hg _)
      (by rw [← mul_assoc]; exact mem_kZeroSet_mul_adelicArchGLIncl S m hγg _)
  have hγ := hF' (globalPoints (𝓞 K) K γ * g)
  rw [hcurve] at hγ
  exact hγ.unique (hF' g)

private theorem InvOn.add_mul {D : Set (AdelicGL2 (𝓞 K) K)} {f g : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : InvOn D f) (hg : InvOn D g) (c : ℂ) : InvOn D (fun q => f q + c * g q) := by
  intro γ x hx hγx
  show f _ + c * g _ = f x + c * g x
  rw [hf γ x hx hγx, hg γ x hx hγx]

private theorem invOn_jlSeries'_realFamilies
    {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (dR' :
        ∀ (w : InfinitePlace K), w.IsReal → Fin 2 × Fin 2 →
        ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ArchDatumR (archR w' hw'))
    (hoff :
      ∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2) (w' : InfinitePlace K) (hw' : w'.IsReal),
      w' ≠ w → dR' w hw ι w' hw' = dR w' hw')
    (hat :
      ∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2) (g : Matrix (Fin 2) (Fin 2) ℝ), g.det ≠ 0 →
      (dR' w hw ι w hw).W g =
      fderivWithin ℝ (ArchR.asPi (dR w hw).W) ArchR.glSet (Matrix.of.symm g)
      (Matrix.of.symm (g * Matrix.single ι.1 ι.2 (1 : ℝ)))) :
    ∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2),
      ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
      globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
      jlSeries' d archR archC (dR' w hw ι) dC dF (globalPoints (𝓞 K) K γ * g) =
        jlSeries' d archR archC (dR' w hw ι) dC dF g := by
  intro w hw ι
  obtain ⟨Γ, Dv, hΓ₀, hΓc, hD₀, hDc, hDw, hR, hC⟩ := exists_unit_curve_real hw ι
  have hder : ∀ q : AdelicGL2 (𝓞 K) K,
      HasDerivAt (fun t : ℝ => jlSeries' d archR archC dR dC dF (q * adelicArchGLIncl K (Γ t)))
        (jlSeries' d archR archC (dR' w hw ι) dC dF q -
          (if ι.1 = ι.2 then (1 / 2 : ℂ) else 0) * jlSeries' d archR archC dR dC dF q) 0 :=
    fun q => hasDerivAt_jlSeries'_mul_adelicArchGLIncl_unitR hω hωb d archR archC dR dC dF hnice hw ι
      (dR' w hw ι) (hoff w hw ι) (hat w hw ι) Γ hΓ₀ hΓc Dv hD₀ hDc hDw hR hC q
  have hF : InvOn (kZeroSet S d.m) (jlSeries' d archR archC dR dC dF) := hinv
  have hF' : InvOn (kZeroSet S d.m) (fun q => jlSeries' d archR archC (dR' w hw ι) dC dF q -
    (if ι.1 = ι.2 then (1 / 2 : ℂ) else 0) * jlSeries' d archR archC dR dC dF q) :=
    invOn_of_forall_hasDerivAt S d.m hder hF
  have hsum := InvOn.add_mul hF' hF ((if ι.1 = ι.2 then (1 / 2 : ℂ) else 0))
  intro γ g hg hγg
  simpa only [sub_add_cancel] using hsum γ g hg hγg

private theorem invOn_jlSeries'_complexFamilies
    {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (dC' :
        ∀ (w : InfinitePlace K), w.IsComplex → (Fin 2 × Fin 2) × Fin 2 →
        ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), ArchDatumC (archC w' hw'))
    (hoff :
      ∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2) (w' : InfinitePlace K)
      (hw' : w'.IsComplex), w' ≠ w → dC' w hw ι w' hw' = dC w' hw')
    (hat :
      ∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2) (g : Matrix (Fin 2) (Fin 2) ℂ),
      g.det ≠ 0 → (dC' w hw ι w hw).W g =
      fderivWithin ℝ (ArchC.asPi (dC w hw).W) ArchC.glSet (Matrix.of.symm g)
      (Matrix.of.symm (g * cplxUnit ι))) :
    ∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2),
      ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
      globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
      jlSeries' d archR archC dR (dC' w hw ι) dF (globalPoints (𝓞 K) K γ * g) =
        jlSeries' d archR archC dR (dC' w hw ι) dF g := by
  intro w hw ι
  obtain ⟨Γ, Dv, hΓ₀, hΓc, hD₀, hDc, hDw, hR, hC⟩ := exists_unit_curve_complex hw ι
  have hder : ∀ q : AdelicGL2 (𝓞 K) K,
      HasDerivAt (fun t : ℝ => jlSeries' d archR archC dR dC dF (q * adelicArchGLIncl K (Γ t)))
        (jlSeries' d archR archC dR (dC' w hw ι) dF q -
          (if ι.1.1 = ι.1.2 ∧ ι.2 = 0 then (1 : ℂ) else 0) * jlSeries' d archR archC dR dC dF q) 0 :=
    fun q => hasDerivAt_jlSeries'_mul_adelicArchGLIncl_unitC hω hωb d archR archC dR dC dF hnice hw ι
      (dC' w hw ι) (hoff w hw ι) (hat w hw ι) Γ hΓ₀ hΓc Dv hD₀ hDc hDw hR hC q
  have hF : InvOn (kZeroSet S d.m) (jlSeries' d archR archC dR dC dF) := hinv
  have hF' : InvOn (kZeroSet S d.m) (fun q => jlSeries' d archR archC dR (dC' w hw ι) dF q -
    (if ι.1.1 = ι.1.2 ∧ ι.2 = 0 then (1 : ℂ) else 0) * jlSeries' d archR archC dR dC dF q) :=
    invOn_of_forall_hasDerivAt S d.m hder hF
  have hsum := InvOn.add_mul hF' hF ((if ι.1.1 = ι.1.2 ∧ ι.2 = 0 then (1 : ℂ) else 0))
  intro γ g hg hγg
  simpa only [sub_add_cancel] using hsum γ g hg hγg

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section CellRepresentatives

private theorem memZK0At_of_glFin_eq (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) {a b : AdelicGL2 (𝓞 K) K}
    (h : glFin (𝓞 K) K a = glFin (𝓞 K) K b) (ha : MemZK0At v n a) : MemZK0At v n b := by
  have hc : componentMatrix v b = componentMatrix v a := by
    unfold componentMatrix
    rw [h]
  unfold MemZK0At
  rw [hc]
  exact ha

private theorem exists_finset_globalPoints_mul_mem_kZeroSet (S : Finset (HeightOneSpectrum (𝓞 K)))
    (m : ↥S → ℕ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ R : Finset (GL (Fin 2) K), ∀ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g ∈ finiteIntegralGL2 (𝓞 K) K →
      ∀ x ∈ T, ∃ γ ∈ R, globalPoints (𝓞 K) K γ * (g * x) ∈ kZeroSet S m := by
  classical
  choose γ hγ using fun p : AdelicGL2 (𝓞 K) K => kZeroSet_meets S m p
  have key : ∀ x : AdelicGL2 (𝓞 K) K, ∃ Rx : Finset (GL (Fin 2) K),
      ∀ k ∈ AutomorphicForm.adelicMaximalCompact K, ∃ γ' ∈ Rx, globalPoints (𝓞 K) K γ' * (k * x) ∈ kZeroSet S m := by
    intro x
    have hcomp : IsCompact ((· * x) '' (AutomorphicForm.adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K))) :=
      (AutomorphicForm.isCompact_adelicMaximalCompact K).image (continuous_mul_const x)
    have hUo : ∀ p : AdelicGL2 (𝓞 K) K, IsOpen ((globalPoints (𝓞 K) K (γ p) * ·) ⁻¹' kZeroSet S m) := fun p =>
      (isOpen_kZeroSet S m).preimage (continuous_const_mul _)
    obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover (fun p => (globalPoints (𝓞 K) K (γ p) * ·) ⁻¹' kZeroSet S m) hUo
      fun q _ => Set.mem_iUnion.2 ⟨q, hγ q⟩
    refine ⟨t.image γ, fun k hk => ?_⟩
    obtain ⟨p, hpt, hkp⟩ := Set.mem_iUnion₂.1 (ht ⟨k, hk, rfl⟩)
    exact ⟨γ p, Finset.mem_image_of_mem γ hpt, hkp⟩
  choose Rx hRx using key
  refine ⟨T.biUnion Rx, fun g hg x hx => ?_⟩
  have hk : AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K g) ∈ AutomorphicForm.adelicMaximalCompact K :=
    AutomorphicForm.mem_adelicMaximalCompact_iff.2
      ⟨by rw [AdelicDock.glFin_finEmbed]; exact hg,
        fun w => by rw [AdelicDock.glArch_finEmbed, map_one]; exact AutomorphicForm.WindowedSiegel.isRowIsometry_one⟩
  obtain ⟨γ', hγ'R, hγ'k⟩ := hRx x _ hk
  refine ⟨γ', Finset.mem_biUnion.2 ⟨x, hx, hγ'R⟩, ?_⟩
  have hfin : glFin (𝓞 K) K (globalPoints (𝓞 K) K γ' * (AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K g) * x)) =
      glFin (𝓞 K) K (globalPoints (𝓞 K) K γ' * (g * x)) := by
    simp only [map_mul, AdelicDock.glFin_finEmbed]
  rw [mem_kZeroSet_iff] at hγ'k ⊢
  exact fun v => memZK0At_of_glFin_eq v.1 (m v) hfin (hγ'k v)

end CellRepresentatives

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section CellHeights

open AutomorphicForm.WindowedSiegel

section CellHeightsPerPlace

variable {E : Type*} [NormedField E]

private theorem cellHeights_norm_add_sq_le (x y : E) : ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
  calc ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
    _ ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem cellHeights_rowNormSq_mul_le (A B : Matrix (Fin 2) (Fin 2) E) :
    rowNormSq (A * B) ≤ 2 * (‖A 1 0‖ ^ 2 * topNormSq B + ‖A 1 1‖ ^ 2 * rowNormSq B) := by
  have h0 : (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
  have e0 := cellHeights_norm_add_sq_le (A 1 0 * B 0 0) (A 1 1 * B 1 0)
  have e1 := cellHeights_norm_add_sq_le (A 1 0 * B 0 1) (A 1 1 * B 1 1)
  rw [norm_mul, norm_mul, mul_pow, mul_pow] at e0 e1
  unfold rowNormSq topNormSq
  rw [h0, h1]
  nlinarith [e0, e1]

private theorem cellHeights_topNormSq_eq (g : GL (Fin 2) E) :
    topNormSq (g : Matrix (Fin 2) (Fin 2) E) =
      (xWindowSq g + localHeight g ^ 2) * rowNormSq (g : Matrix (Fin 2) (Fin 2) E) := by
  have hr : rowNormSq (g : Matrix (Fin 2) (Fin 2) E) ≠ 0 := (rowNormSq_pos g).ne'
  have hx : topNormSq (g : Matrix (Fin 2) (Fin 2) E) / rowNormSq (g : Matrix (Fin 2) (Fin 2) E) =
      xWindowSq g + localHeight g ^ 2 := by
    unfold xWindowSq
    ring
  rwa [div_eq_iff hr] at hx

private theorem cellHeights_core {a b r r' D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 < r) (hr' : 0 < r')
    (hD : r' ≤ r * D) : b * (a / r) ≤ b * a / r' * D := by
  have key : b * a * r' ≤ b * a * D * r := by
    have h := mul_le_mul_of_nonneg_left hD (mul_nonneg hb ha)
    nlinarith [h]
  calc b * (a / r) = b * a / r := by ring
    _ ≤ b * a * D / r' := by rw [div_le_div_iff₀ hr hr']; exact key
    _ = b * a / r' * D := by ring

private theorem cellHeights_dominate {p q xw h c u : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : 0 < c) (hg : c ≤ h)
    (hx : xw ≤ u ^ 2) :
    2 * (p * (xw + h ^ 2) + q) ≤ 2 * (p * (u ^ 2 / c ^ 2 + 1) + q / c ^ 2) * h ^ 2 := by
  have h1 : 1 ≤ h ^ 2 / c ^ 2 := (one_le_div₀ (pow_pos hc 2)).2 (pow_le_pow_left₀ hc.le hg 2)
  have hu : u ^ 2 ≤ u ^ 2 / c ^ 2 * h ^ 2 := by
    calc u ^ 2 ≤ u ^ 2 * (h ^ 2 / c ^ 2) := le_mul_of_one_le_right (sq_nonneg u) h1
      _ = u ^ 2 / c ^ 2 * h ^ 2 := by ring
  have hq' : q ≤ q / c ^ 2 * h ^ 2 := by
    calc q ≤ q * (h ^ 2 / c ^ 2) := le_mul_of_one_le_right hq h1
      _ = q / c ^ 2 * h ^ 2 := by ring
  nlinarith [mul_le_mul_of_nonneg_left (hx.trans hu) hp, hq']

private noncomputable def cellHeightsWeight (γ g : GL (Fin 2) E) : ℝ :=
  2 * (‖(γ : Matrix (Fin 2) (Fin 2) E) 1 0‖ ^ 2 * (xWindowSq g + localHeight g ^ 2) +
    ‖(γ : Matrix (Fin 2) (Fin 2) E) 1 1‖ ^ 2)

private theorem cellHeights_det_mul_le (γ g : GL (Fin 2) E) :
    ‖(γ : Matrix (Fin 2) (Fin 2) E).det‖ * localHeight g ≤ localHeight (γ * g) * cellHeightsWeight γ g := by
  have hcoe : ((γ * g : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      (γ : Matrix (Fin 2) (Fin 2) E) * (g : Matrix (Fin 2) (Fin 2) E) := rfl
  have hD : rowNormSq ((γ * g : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) ≤
      rowNormSq (g : Matrix (Fin 2) (Fin 2) E) * cellHeightsWeight γ g := by
    rw [hcoe]
    refine (cellHeights_rowNormSq_mul_le _ _).trans (le_of_eq ?_)
    rw [cellHeights_topNormSq_eq g]
    unfold cellHeightsWeight
    ring
  have hr := rowNormSq_pos g
  have hr' := rowNormSq_pos (γ * g)
  have hdet : ‖((γ * g : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).det‖ =
      ‖(γ : Matrix (Fin 2) (Fin 2) E).det‖ * ‖(g : Matrix (Fin 2) (Fin 2) E).det‖ := by
    rw [hcoe, Matrix.det_mul, norm_mul]
  have h1 : localHeight g =
      ‖(g : Matrix (Fin 2) (Fin 2) E).det‖ / rowNormSq (g : Matrix (Fin 2) (Fin 2) E) := rfl
  have h2 : localHeight (γ * g) = ‖((γ * g : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).det‖ /
      rowNormSq ((γ * g : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) := rfl
  have hcore := cellHeights_core (norm_nonneg (g : Matrix (Fin 2) (Fin 2) E).det)
    (norm_nonneg (γ : Matrix (Fin 2) (Fin 2) E).det) hr hr' hD
  rw [h1, h2, hdet]
  exact hcore

private theorem cellHeights_le_mul_right (M B : GL (Fin 2) E) :
    localHeight M * ‖(B : Matrix (Fin 2) (Fin 2) E).det‖ ≤
      localHeight (M * B) *
        (2 * (topNormSq (B : Matrix (Fin 2) (Fin 2) E) + rowNormSq (B : Matrix (Fin 2) (Fin 2) E))) := by
  have hcoe : ((M * B : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      (M : Matrix (Fin 2) (Fin 2) E) * (B : Matrix (Fin 2) (Fin 2) E) := rfl
  have hr := rowNormSq_pos M
  have hr' := rowNormSq_pos (M * B)
  have htop : 0 ≤ topNormSq (B : Matrix (Fin 2) (Fin 2) E) := by unfold topNormSq; positivity
  have hrowB := (rowNormSq_pos B).le
  have h10 : ‖(M : Matrix (Fin 2) (Fin 2) E) 1 0‖ ^ 2 ≤ rowNormSq (M : Matrix (Fin 2) (Fin 2) E) := by
    unfold rowNormSq; exact le_add_of_nonneg_right (sq_nonneg _)
  have h11 : ‖(M : Matrix (Fin 2) (Fin 2) E) 1 1‖ ^ 2 ≤ rowNormSq (M : Matrix (Fin 2) (Fin 2) E) := by
    unfold rowNormSq; exact le_add_of_nonneg_left (sq_nonneg _)
  have hD : rowNormSq ((M * B : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) ≤
      rowNormSq (M : Matrix (Fin 2) (Fin 2) E) *
        (2 * (topNormSq (B : Matrix (Fin 2) (Fin 2) E) + rowNormSq (B : Matrix (Fin 2) (Fin 2) E))) := by
    rw [hcoe]
    refine (cellHeights_rowNormSq_mul_le _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_right h10 htop, mul_le_mul_of_nonneg_right h11 hrowB]
  have hdet : ‖((M * B : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).det‖ =
      ‖(M : Matrix (Fin 2) (Fin 2) E).det‖ * ‖(B : Matrix (Fin 2) (Fin 2) E).det‖ := by
    rw [hcoe, Matrix.det_mul, norm_mul]
  have h1 : localHeight M =
      ‖(M : Matrix (Fin 2) (Fin 2) E).det‖ / rowNormSq (M : Matrix (Fin 2) (Fin 2) E) := rfl
  have h2 : localHeight (M * B) = ‖((M * B : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).det‖ /
      rowNormSq ((M * B : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) := rfl
  have hcore := cellHeights_core (norm_nonneg (M : Matrix (Fin 2) (Fin 2) E).det)
    (norm_nonneg (B : Matrix (Fin 2) (Fin 2) E).det) hr hr' hD
  rw [h1, h2, hdet]
  calc ‖(M : Matrix (Fin 2) (Fin 2) E).det‖ / rowNormSq (M : Matrix (Fin 2) (Fin 2) E) *
        ‖(B : Matrix (Fin 2) (Fin 2) E).det‖
      = ‖(B : Matrix (Fin 2) (Fin 2) E).det‖ *
          (‖(M : Matrix (Fin 2) (Fin 2) E).det‖ / rowNormSq (M : Matrix (Fin 2) (Fin 2) E)) := mul_comm _ _
    _ ≤ ‖(B : Matrix (Fin 2) (Fin 2) E).det‖ * ‖(M : Matrix (Fin 2) (Fin 2) E).det‖ /
          rowNormSq ((M * B : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) *
          (2 * (topNormSq (B : Matrix (Fin 2) (Fin 2) E) + rowNormSq (B : Matrix (Fin 2) (Fin 2) E))) := hcore
    _ = _ := by ring

private theorem cellHeights_exists_right (B : GL (Fin 2) E) :
    ∃ Kb : ℝ, 0 < Kb ∧ ∀ M : GL (Fin 2) E,
      localHeight M ≤ Kb * localHeight (M * B) ∧ localHeight (M * B) ≤ Kb * localHeight M := by
  have hdB : 0 < ‖(B : Matrix (Fin 2) (Fin 2) E).det‖ :=
    norm_pos_iff.2 (Matrix.GeneralLinearGroup.det_ne_zero B)
  have hdBi : 0 < ‖((B⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).det‖ :=
    norm_pos_iff.2 (Matrix.GeneralLinearGroup.det_ne_zero B⁻¹)
  have hβB :
      0 ≤ 2 * (topNormSq (B : Matrix (Fin 2) (Fin 2) E) + rowNormSq (B : Matrix (Fin 2) (Fin 2) E)) := by
    unfold topNormSq rowNormSq; positivity
  have hβBi : 0 ≤ 2 * (topNormSq ((B⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) +
      rowNormSq ((B⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E)) := by
    unfold topNormSq rowNormSq; positivity
  have hq1 := div_nonneg hβB hdB.le
  have hq2 := div_nonneg hβBi hdBi.le
  refine ⟨2 * (topNormSq (B : Matrix (Fin 2) (Fin 2) E) + rowNormSq (B : Matrix (Fin 2) (Fin 2) E)) /
      ‖(B : Matrix (Fin 2) (Fin 2) E).det‖ +
    2 * (topNormSq ((B⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) +
      rowNormSq ((B⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E)) /
      ‖((B⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).det‖ + 1, by linarith, fun M => ?_⟩
  have hM := cellHeights_le_mul_right M B
  have hMi := cellHeights_le_mul_right (M * B) B⁻¹
  rw [mul_inv_cancel_right] at hMi
  have ht0 := (localHeight_pos (M * B)).le
  have hm0 := (localHeight_pos M).le
  have e1 : localHeight M ≤ localHeight (M * B) *
      (2 * (topNormSq (B : Matrix (Fin 2) (Fin 2) E) + rowNormSq (B : Matrix (Fin 2) (Fin 2) E)) /
        ‖(B : Matrix (Fin 2) (Fin 2) E).det‖) := by
    rw [mul_div_assoc', le_div_iff₀ hdB]
    exact hM
  have e2 : localHeight (M * B) ≤ localHeight M *
      (2 * (topNormSq ((B⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) +
        rowNormSq ((B⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E)) /
        ‖((B⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).det‖) := by
    rw [mul_div_assoc', le_div_iff₀ hdBi]
    exact hMi
  constructor
  · nlinarith [e1, mul_nonneg ht0 hq2, ht0]
  · nlinarith [e2, mul_nonneg hm0 hq1, hm0]

private theorem cellHeights_exists_upper (γ : GL (Fin 2) E) {c : ℝ} (hc : 0 < c) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧
      ∀ g : GL (Fin 2) E, c ≤ localHeight g → localHeight (γ * g) ≤ Cu * localHeight g := by
  by_cases hγ : (γ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0
  ·
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero γ
    rw [Matrix.det_fin_two, hγ, mul_zero, sub_zero] at hdet
    have ht : (γ : Matrix (Fin 2) (Fin 2) E) 1 1 ≠ 0 := (mul_ne_zero_iff.1 hdet).2
    refine ⟨‖(γ : Matrix (Fin 2) (Fin 2) E) 0 0‖ / ‖(γ : Matrix (Fin 2) (Fin 2) E) 1 1‖, by positivity, fun g _ => ?_⟩
    exact (AutomorphicForm.SiegelCoordinates.localHeight_upper_entries_mul (s := γ) ht rfl hγ rfl g).le
  ·
    obtain ⟨A, hA0, hAs⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ g : GL (Fin 2) E, localHeight (γ * g) * localHeight g ≤ A :=
      ⟨_, by positivity, fun g => AutomorphicForm.SiegelCoordinates.localHeight_mul_mul_localHeight_le γ g hγ⟩
    refine ⟨A / c ^ 2, by positivity, fun g hg => ?_⟩
    have hX := (localHeight_pos (γ * g)).le
    have hgA := hAs g
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc 2)]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hX) hc.le,
      mul_le_mul_of_nonneg_right hgA hc.le, mul_le_mul_of_nonneg_left hg hA0]

private theorem cellHeights_exists_lower (γ : GL (Fin 2) E) {c : ℝ} (u : ℝ) (hc : 0 < c) :
    ∃ Cl : ℝ, 0 < Cl ∧ ∀ g : GL (Fin 2) E, c ≤ localHeight g → xWindowSq g ≤ u ^ 2 →
      1 ≤ localHeight (γ * g) * localHeight g * Cl := by
  have hδ : 0 < ‖(γ : Matrix (Fin 2) (Fin 2) E).det‖ := norm_pos_iff.2 (Matrix.GeneralLinearGroup.det_ne_zero γ)
  obtain ⟨E', hE'0, hE'⟩ : ∃ E' : ℝ, 0 ≤ E' ∧ ∀ g : GL (Fin 2) E, c ≤ localHeight g → xWindowSq g ≤ u ^ 2 →
      cellHeightsWeight γ g ≤ E' * localHeight g ^ 2 := by
    refine ⟨2 * (‖(γ : Matrix (Fin 2) (Fin 2) E) 1 0‖ ^ 2 * (u ^ 2 / c ^ 2 + 1) +
      ‖(γ : Matrix (Fin 2) (Fin 2) E) 1 1‖ ^ 2 / c ^ 2), by positivity, fun g hg hx => ?_⟩
    unfold cellHeightsWeight
    exact cellHeights_dominate (sq_nonneg _) (sq_nonneg _) hc hg hx
  refine ⟨(E' + 1) / ‖(γ : Matrix (Fin 2) (Fin 2) E).det‖, div_pos (by linarith) hδ, fun g hg hx => ?_⟩
  have hX := localHeight_pos (γ * g)
  have hh := localHeight_pos g
  have F1 := cellHeights_det_mul_le γ g
  have F2 := hE' g hg hx
  have key : ‖(γ : Matrix (Fin 2) (Fin 2) E).det‖ * localHeight g ≤
      localHeight (γ * g) * localHeight g * (E' + 1) * localHeight g := by
    nlinarith [F1, mul_le_mul_of_nonneg_left F2 hX.le, mul_nonneg hX.le (mul_nonneg hh.le hh.le)]
  have key' : ‖(γ : Matrix (Fin 2) (Fin 2) E).det‖ ≤ localHeight (γ * g) * localHeight g * (E' + 1) :=
    le_of_mul_le_mul_right key hh
  rw [mul_div_assoc', le_div_iff₀ hδ, one_mul]
  exact key'

private theorem cellHeights_exists_pair (A B : GL (Fin 2) E) {c : ℝ} (u : ℝ) (hc : 0 < c) :
    ∃ Cw : ℝ, 0 < Cw ∧ ∀ S : GL (Fin 2) E, c ≤ localHeight S → xWindowSq S ≤ u ^ 2 →
      localHeight (A * (S * B)) ≤ Cw * localHeight (S * B) ∧
        1 ≤ localHeight (A * (S * B)) * localHeight (S * B) * Cw := by
  obtain ⟨Kb, hKb, hB⟩ := cellHeights_exists_right B
  obtain ⟨Cu, hCu, hup⟩ := cellHeights_exists_upper A hc
  obtain ⟨Cl, hCl, hlow⟩ := cellHeights_exists_lower A u hc
  refine ⟨Kb * Kb * Cu + Kb * Kb * Cl + 1, by positivity, fun S hS hX => ?_⟩
  obtain ⟨hm1, hm2⟩ := hB (A * S)
  rw [mul_assoc] at hm1 hm2
  obtain ⟨hb1, -⟩ := hB S
  have hu := hup S hS
  have hl := hlow S hS hX
  have ht0 := localHeight_pos (A * (S * B))
  have ha0 := localHeight_pos (S * B)
  have hb0 := localHeight_pos S
  constructor
  · have s1 : localHeight (A * (S * B)) ≤ Kb * (Cu * localHeight S) :=
      hm2.trans (mul_le_mul_of_nonneg_left hu hKb.le)
    have s2 : localHeight (A * (S * B)) ≤ Kb * (Cu * (Kb * localHeight (S * B))) :=
      s1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1 hCu) hKb.le)
    nlinarith [s2, mul_nonneg (mul_nonneg (mul_nonneg hKb.le hKb.le) hCl.le) ha0.le, ha0.le]
  · have p1 : localHeight (A * S) * localHeight S ≤ Kb * localHeight (A * (S * B)) * localHeight S :=
      mul_le_mul_of_nonneg_right hm1 hb0.le
    have p2 : Kb * localHeight (A * (S * B)) * localHeight S ≤
        Kb * localHeight (A * (S * B)) * (Kb * localHeight (S * B)) :=
      mul_le_mul_of_nonneg_left hb1 (mul_pos hKb ht0).le
    have p3 : localHeight (A * S) * localHeight S * Cl ≤
        Kb * localHeight (A * (S * B)) * (Kb * localHeight (S * B)) * Cl :=
      mul_le_mul_of_nonneg_right (p1.trans p2) hCl.le
    nlinarith [hl, p3, mul_nonneg (mul_nonneg ht0.le ha0.le) (mul_nonneg (mul_nonneg hKb.le hKb.le) hCu),
      mul_nonneg ht0.le ha0.le]

end CellHeightsPerPlace

private theorem cellHeights_exists_place_const (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K)
    {c : ℝ} (u : ℝ) (hc : 0 < c) :
    ∃ Cw : ℝ, 0 < Cw ∧ ∀ s : AdelicGL2 (𝓞 K) K,
      c ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) →
        xWindowSq (archComponent K w (glArch (𝓞 K) K s)) ≤ u ^ 2 →
        localHeight (archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K γ * (s * x)))) ≤
            Cw * localHeight (archComponent K w (glArch (𝓞 K) K (s * x))) ∧
          1 ≤ localHeight (archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K γ * (s * x)))) *
            localHeight (archComponent K w (glArch (𝓞 K) K (s * x))) * Cw := by
  obtain ⟨Cw, hCw, h⟩ :=
    cellHeights_exists_pair (archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K γ)))
      (archComponent K w (glArch (𝓞 K) K x)) u hc
  refine ⟨Cw, hCw, fun s hs hx => ?_⟩
  simp only [map_mul]
  exact h _ hs hx

private theorem exists_height_comparison_of_finset (R : Finset (GL (Fin 2) K)) {c u d₁ d₂ : ℝ} (hc : 0 < c)
    (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ γ ∈ R, ∀ g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
      ∀ w : InfinitePlace K,
        localHeight (archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K γ * g))) ≤
            C * localHeight (archComponent K w (glArch (𝓞 K) K g)) ^ k ∧
          (localHeight (archComponent K w (glArch (𝓞 K) K g)) ^ k)⁻¹ / C ≤
            localHeight (archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K γ * g))) := by
  choose Cf hCf0 hCf using fun (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) =>
    cellHeights_exists_place_const γ x w u hc
  have hsum : 0 ≤ ∑ γ' ∈ R, ∑ x' ∈ T, ∑ w' : InfinitePlace K, Cf γ' x' w' :=
    Finset.sum_nonneg fun γ' _ => Finset.sum_nonneg fun x' _ =>
      Finset.sum_nonneg fun w' _ => (hCf0 γ' x' w').le
  refine ⟨1 + ∑ γ' ∈ R, ∑ x' ∈ T, ∑ w' : InfinitePlace K, Cf γ' x' w', by linarith, 1, fun γ hγR g hg w => ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image] at hg
  obtain ⟨x, hxT, s, hs, rfl⟩ := hg
  obtain ⟨-, hsh, hsx, -⟩ := hs
  obtain ⟨hup, hlow⟩ := hCf γ x w s (hsh w) (hsx w)
  have h3 : Cf γ x w ≤ ∑ w' : InfinitePlace K, Cf γ x w' :=
    Finset.single_le_sum (f := fun w' => Cf γ x w') (fun w' _ => (hCf0 γ x w').le) (Finset.mem_univ w)
  have h2 : ∑ w' : InfinitePlace K, Cf γ x w' ≤ ∑ x' ∈ T, ∑ w' : InfinitePlace K, Cf γ x' w' :=
    Finset.single_le_sum (f := fun x' => ∑ w' : InfinitePlace K, Cf γ x' w')
      (fun x' _ => Finset.sum_nonneg fun w' _ => (hCf0 γ x' w').le) hxT
  have h1 : ∑ x' ∈ T, ∑ w' : InfinitePlace K, Cf γ x' w' ≤ ∑ γ' ∈ R, ∑ x' ∈ T, ∑ w' : InfinitePlace K, Cf γ' x' w' :=
    Finset.single_le_sum (f := fun γ' => ∑ x' ∈ T, ∑ w' : InfinitePlace K, Cf γ' x' w')
      (fun γ' _ => Finset.sum_nonneg fun x' _ => Finset.sum_nonneg fun w' _ => (hCf0 γ' x' w').le)
      hγR
  have hCfC : Cf γ x w ≤ 1 + ∑ γ' ∈ R, ∑ x' ∈ T, ∑ w' : InfinitePlace K, Cf γ' x' w' := by linarith
  have ha0 := localHeight_pos (archComponent K w (glArch (𝓞 K) K (s * x)))
  have ht0 := localHeight_pos (archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K γ * (s * x))))
  simp only [pow_one]
  refine ⟨hup.trans (mul_le_mul_of_nonneg_right hCfC ha0.le), ?_⟩
  rw [inv_eq_one_div, div_div, div_le_iff₀ (mul_pos ha0 (by linarith))]
  nlinarith [hlow, mul_le_mul_of_nonneg_left hCfC (mul_nonneg ht0.le ha0.le)]

end CellHeights

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "NumberField.AdelicVolume LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section RepsOfWindow

private theorem archDetNorm_mul (w : InfinitePlace K) (a b : AdelicGL2 (𝓞 K) K) :
    archDetNorm w (a * b) = archDetNorm w a * archDetNorm w b := by
  simp only [archDetNorm, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

private theorem exists_reps_of_window (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ↥S → ℕ) {c u d₁ d₂ : ℝ}
    (hc : 0 < c) (hd₁ : 0 < d₁) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ (R : Finset (GL (Fin 2) K)) (C : ℝ), 0 < C ∧
      ∃ (k : ℕ) (Kc : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))), IsCompact Kc ∧
        ∃ d₁' d₂' : ℝ, 0 < d₁' ∧
          (∀ h ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, ∃ γ ∈ R,
            globalPoints (𝓞 K) K γ * h ∈ kZeroSet S m ∧
              ∀ w : InfinitePlace K,
                localHeight (archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K γ * h))) ≤
                    C * localHeight (archComponent K w (glArch (𝓞 K) K h)) ^ k ∧
                  (localHeight (archComponent K w (glArch (𝓞 K) K h)) ^ k)⁻¹ / C ≤
                    localHeight (archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K γ * h)))) ∧
          (∀ γ ∈ R, ∀ h ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
            glFin (𝓞 K) K (globalPoints (𝓞 K) K γ * h) ∈ Kc ∧
              ∀ w : InfinitePlace K, archDetNorm w (globalPoints (𝓞 K) K γ * h) ∈ Set.Icc d₁' d₂') := by
  obtain ⟨R, hR⟩ := exists_finset_globalPoints_mul_mem_kZeroSet S m T
  obtain ⟨C, hC, k, hk⟩ := exists_height_comparison_of_finset R (u := u) (d₁ := d₁) (d₂ := d₂) hc T
  obtain ⟨Kc, hKc, hKmem⟩ : ∃ Kc : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)), IsCompact Kc ∧
      ∀ γ ∈ R, ∀ x ∈ T, ∀ s ∈ centreCutSiegelSet K c u d₁ d₂,
        glFin (𝓞 K) K (globalPoints (𝓞 K) K γ * (s * x)) ∈ Kc := by
    refine ⟨⋃ γ ∈ R, ⋃ x ∈ T, (fun y => glFin (𝓞 K) K (globalPoints (𝓞 K) K γ) * y * glFin (𝓞 K) K x) ''
      (finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))), ?_, ?_⟩
    · refine Finset.isCompact_biUnion R fun γ _ => Finset.isCompact_biUnion T fun x _ => ?_
      exact (isCompact_finiteLevelZero (𝓞 K) K ⊤).image ((continuous_const.mul continuous_id).mul continuous_const)
    · intro γ hγ x hx s hs
      refine Set.mem_iUnion₂.2 ⟨γ, hγ, Set.mem_iUnion₂.2 ⟨x, hx, glFin (𝓞 K) K s, ?_, ?_⟩⟩
      · exact (mem_centreCutSiegelSet_iff.1 hs).1
      · simp only [map_mul, mul_assoc]
  obtain ⟨F, hF1, hFpos, hFmem⟩ : ∃ F : Finset ℝ, (1 : ℝ) ∈ F ∧ (∀ y ∈ F, 0 < y) ∧
      ∀ γ ∈ R, ∀ x ∈ T, ∀ w : InfinitePlace K,
        archDetNorm w (globalPoints (𝓞 K) K γ) * archDetNorm w x ∈ F := by
    refine ⟨insert 1 ((R ×ˢ T ×ˢ (Finset.univ : Finset (InfinitePlace K))).image
      fun p => archDetNorm p.2.2 (globalPoints (𝓞 K) K p.1) * archDetNorm p.2.2 p.2.1),
      Finset.mem_insert_self _ _, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact one_pos
      · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy
        exact mul_pos (archDetNorm_pos _ _) (archDetNorm_pos _ _)
    · intro γ hγ x hx w
      exact Finset.mem_insert_of_mem (Finset.mem_image.2
        ⟨(γ, x, w), Finset.mem_product.2 ⟨hγ, Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩⟩, rfl⟩)
  have hne : F.Nonempty := ⟨1, hF1⟩
  refine ⟨R, C, hC, k, Kc, hKc, F.min' hne * d₁, F.max' hne * d₂, mul_pos (hFpos _ (F.min'_mem hne)) hd₁, ?_, ?_⟩
  · intro h hh
    obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_iUnion₂.1 hh
    obtain ⟨γ, hγ, hmem⟩ := hR s (mem_centreCutSiegelSet_iff.1 hs).1 x hx
    exact ⟨γ, hγ, hmem, hk γ hγ _ hh⟩
  · intro γ hγ h hh
    obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_iUnion₂.1 hh
    refine ⟨hKmem γ hγ x hx s hs, fun w => ?_⟩
    have hdet := (mem_centreCutSiegelSet_iff.1 hs).2.2.2 w
    have hf := hFmem γ hγ x hx w
    have hkey : archDetNorm w (globalPoints (𝓞 K) K γ * (s * x))
        = (archDetNorm w (globalPoints (𝓞 K) K γ) * archDetNorm w x) * archDetNorm w s := by
      simp only [archDetNorm_mul]
      ring
    show archDetNorm w (globalPoints (𝓞 K) K γ * (s * x)) ∈ Set.Icc _ _
    rw [hkey]
    exact ⟨mul_le_mul (F.min'_le _ hf) hdet.1 hd₁.le (hFpos _ hf).le,
      mul_le_mul (F.le_max' _ hf) hdet.2 (archDetNorm_pos _ _).le (hFpos _ (F.max'_mem hne)).le⟩

end RepsOfWindow

end LanglandsTunnell.Converse.CuspSynthesis

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

private noncomputable def finShift (y : FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K :=
  ((0 : InfiniteAdeleRing K), y)

private theorem algebraMap_mul_mem_integralFiniteAdeles (a : 𝓞 K) {r : FiniteAdeleRing (𝓞 K) K}
    (hr : r ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a * r ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  intro v
  rw [NumberField.AdelicLevel.coe_mul_apply]
  exact mul_mem (NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers v a) (hr v)

private theorem exists_algebraMap_mul_mem (y : FiniteAdeleRing (𝓞 K) K) :
    ∃ b : 𝓞 K, b ≠ 0 ∧
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b * y ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  obtain ⟨b, hb, hby⟩ := NumberField.AdelicBox.exists_mul_mem_integralFiniteAdeles (R := 𝓞 K) (K := K) y
  exact ⟨b, hb, fun v => hby v⟩

private theorem exists_algebraMap_mul_mem_of_finset (S : Finset (FiniteAdeleRing (𝓞 K) K)) :
    ∃ b : 𝓞 K, b ≠ 0 ∧ ∀ y ∈ S,
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b * y ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun y hy => absurd hy (Finset.notMem_empty y)⟩
  | insert z S _ ih =>
    obtain ⟨b₁, hb₁, h₁⟩ := ih
    obtain ⟨b₂, hb₂, h₂⟩ := exists_algebraMap_mul_mem (K := K) z
    refine ⟨b₁ * b₂, mul_ne_zero hb₁ hb₂, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hyS
    · rw [map_mul, mul_assoc]
      exact algebraMap_mul_mem_integralFiniteAdeles b₁ h₂
    · rw [map_mul, mul_comm (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b₁), mul_assoc]
      exact algebraMap_mul_mem_integralFiniteAdeles b₂ (h₁ y hyS)

private theorem algebraMap_mul_mem_idealBall {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) {n : 𝓞 K} (hn : n ∈ N)
    {z : FiniteAdeleRing (𝓞 K) K} (hz : z ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) n * z ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K N := by
  classical
  intro v
  have hnv : Valued.v ((algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) n) v) = v.intValuation n :=
    NumberField.AdelicLevel.valued_algebraMap v n
  rw [NumberField.AdelicLevel.coe_mul_apply, Valuation.map_mul, hnv]
  have hz1 : Valued.v (z v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz v)
  refine (mul_le_of_le_one_right' hz1).trans ?_
  rw [NumberField.AdelicLevel.idealBound_of_ne_bot hN]
  by_cases hn0 : n = 0
  · subst hn0
    simp
  rw [HeightOneSpectrum.intValuation_if_neg v hn0, WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  have hspan := Associates.mk_le_mk_iff_dvd.2 (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem N).2 hn))
  have hne : Associates.mk (Ideal.span {n} : Ideal (𝓞 K)) ≠ 0 :=
    Associates.mk_ne_zero.2 (Ideal.span_singleton_eq_bot.not.2 hn0)
  exact Associates.count_le_count_of_le hne (HeightOneSpectrum.associates_irreducible v) hspan

private theorem glFin_unipotentGL2_finShift (y : FiniteAdeleRing (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 (finShift y)) = unipotentGL2 y := by
  ext i j
  rw [NumberField.AdelicLevel.glFin_apply]
  fin_cases i <;> fin_cases j <;> rfl

private theorem glArch_unipotentGL2_finShift (y : FiniteAdeleRing (𝓞 K) K) :
    glArch (𝓞 K) K (unipotentGL2 (finShift y)) = 1 := by
  ext i j
  rw [NumberField.AdelicLevel.glArch_apply]
  fin_cases i <;> fin_cases j <;> rfl

private theorem unipotentGL2_coe_eq (y : FiniteAdeleRing (𝓞 K) K) :
    (unipotentGL2 y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
      = 1 + y • Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : FiniteAdeleRing (𝓞 K) K) := by
  rw [unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single, Matrix.one_apply]

private theorem conj_unipotentGL2_coe (k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (y : FiniteAdeleRing (𝓞 K) K) :
    ((k⁻¹ * unipotentGL2 y * k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
      = 1 + y • (((k⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
          * Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : FiniteAdeleRing (𝓞 K) K)
          * (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
  rw [Units.val_mul, Units.val_mul, unipotentGL2_coe_eq, mul_add, add_mul, mul_one, Units.inv_mul,
    Matrix.mul_smul, Matrix.smul_mul]

private theorem single_entry_mem (i j : Fin 2) :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : FiniteAdeleRing (𝓞 K) K) i j
      ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single, NumberField.AdelicLevel.one_mem_integralFiniteAdeles,
      NumberField.AdelicLevel.zero_mem_integralFiniteAdeles]

private theorem mul_entry_mem_integralFiniteAdeles {A C : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hA : ∀ i j, A i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hC : ∀ i j, C i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K) (i j : Fin 2) :
    (A * C) i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact NumberField.AdelicLevel.add_mem_integralFiniteAdeles
    (NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hA i 0) (hC 0 j))
    (NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hA i 1) (hC 1 j))

private theorem isLevelOneMatrix_one_add {N : Ideal (𝓞 K)} {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hm : ∀ i j, m i j ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K N) :
    IsLevelOneMatrix (𝓞 K) K N (1 + m) where
  integral i j := by
    rw [Matrix.add_apply]
    refine NumberField.AdelicLevel.add_mem_integralFiniteAdeles ?_
      (NumberField.AdelicLevel.idealBall_subset_integralFiniteAdeles N (hm i j))
    rw [Matrix.one_apply]
    split_ifs
    · exact NumberField.AdelicLevel.one_mem_integralFiniteAdeles
    · exact NumberField.AdelicLevel.zero_mem_integralFiniteAdeles
  lowerLeft := by
    rw [Matrix.add_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), zero_add]
    exact hm 1 0
  lowerRight := by
    rw [Matrix.add_apply, Matrix.one_apply_eq, add_sub_cancel_left]
    exact hm 1 1

private theorem exists_conjugation_ideal (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K))
    (hN : N ≠ ⊥) :
    ∃ a : 𝓞 K, a ≠ 0 ∧
      ∀ g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
        ∀ r ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K,
          g⁻¹ * unipotentGL2 (finShift (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a * r)) * g
              ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧
            ∀ v : HeightOneSpectrum (𝓞 K),
              Valued.v (componentMatrix v
                  (g⁻¹ * unipotentGL2 (finShift (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a * r)) * g) 0 0 - 1)
                ≤ NumberField.AdelicLevel.idealBound (𝓞 K) N v := by
  classical
  obtain ⟨n₀, hn₀N, hn₀⟩ := (Submodule.ne_bot_iff N).1 hN
  set S : Finset (FiniteAdeleRing (𝓞 K) K) := T.biUnion fun x =>
    (Finset.univ : Finset (Fin 2 × Fin 2)).image
        (fun p => (glFin (𝓞 K) K x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) p.1 p.2) ∪
      (Finset.univ : Finset (Fin 2 × Fin 2)).image
        (fun p => (((glFin (𝓞 K) K x)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) p.1 p.2)
  obtain ⟨b, hb, hbS⟩ := exists_algebraMap_mul_mem_of_finset (K := K) S
  refine ⟨n₀ * (b * b), mul_ne_zero hn₀ (mul_ne_zero hb hb), ?_⟩
  intro g hg r hr
  obtain ⟨x, hxT, s, hs, rfl⟩ := by
    simpa only [Set.mem_iUnion, Set.mem_image, exists_prop] using hg
  have hsInt := NumberField.AdelicLevel.mem_finiteIntegralGL2_iff.1 (mem_centreCutSiegelSet_iff.1 hs).1
  have hxcl : ∀ i j,
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b * (glFin (𝓞 K) K x : Matrix (Fin 2) (Fin 2) _) i j
          ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K ∧
        algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b *
            (((glFin (𝓞 K) K x)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) i j
          ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    intro i j
    constructor
    · exact hbS _ (Finset.mem_biUnion.2 ⟨x, hxT, Finset.mem_union.2 (Or.inl
        (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩)
    · exact hbS _ (Finset.mem_biUnion.2 ⟨x, hxT, Finset.mem_union.2 (Or.inr
        (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩)
  set kx : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) := glFin (𝓞 K) K x
  set ks : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) := glFin (𝓞 K) K s
  set E : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) := Matrix.single (0 : Fin 2) (1 : Fin 2) 1 with hE
  set C : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) :=
    ((ks⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) * E * (ks : Matrix (Fin 2) (Fin 2) _)
    with hC
  have hEint : ∀ i j, E i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    intro i j
    rw [hE]
    exact single_entry_mem i j
  have hCint : ∀ i j, C i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    intro i j
    rw [hC]
    exact mul_entry_mem_integralFiniteAdeles (mul_entry_mem_integralFiniteAdeles hsInt.2 hEint) hsInt.1 i j
  have hgfin : glFin (𝓞 K) K (s * x) = ks * kx := map_mul _ _ _
  set M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) :=
    (((ks * kx)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) * E *
      ((ks * kx : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) with hM
  have hMeq : M = ((kx⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) * C *
      (kx : Matrix (Fin 2) (Fin 2) _) := by
    simp only [hM, hC, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  have hMcl : ∀ i j, algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) (b * b) * M i j
      ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    intro i j
    have hterm : ∀ l : Fin 2, algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) (b * b) *
        ((((kx⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) * C :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i l *
          (kx : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) l j)
        ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
      intro l
      have h := NumberField.AdelicLevel.mul_mem_integralFiniteAdeles
        (NumberField.AdelicLevel.add_mem_integralFiniteAdeles
          (NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hxcl i 0).2 (hCint 0 l))
          (NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hxcl i 1).2 (hCint 1 l)))
        (hxcl l j).1
      convert h using 1
      rw [Matrix.mul_apply, Fin.sum_univ_two, map_mul]
      ring
    rw [hMeq, Matrix.mul_apply, Fin.sum_univ_two, mul_add]
    exact NumberField.AdelicLevel.add_mem_integralFiniteAdeles (hterm 0) (hterm 1)
  have hball : ∀ r' ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K, ∀ i j,
      ((algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) (n₀ * (b * b)) * r') • M) i j
        ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K N := by
    intro r' hr' i j
    have h := algebraMap_mul_mem_idealBall hN hn₀N
      (NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hMcl i j) hr')
    convert h using 1
    rw [Matrix.smul_apply, smul_eq_mul, map_mul]
    ring
  have hlevel : ∀ r' ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K,
      IsLevelOneMatrix (𝓞 K) K N
        (1 + (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) (n₀ * (b * b)) * r') • M) :=
    fun r' hr' => isLevelOneMatrix_one_add (hball r' hr')
  have hnegr : -r ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    simpa using NumberField.AdelicLevel.sub_mem_integralFiniteAdeles
      NumberField.AdelicLevel.zero_mem_integralFiniteAdeles hr
  have hinv : ∀ y : FiniteAdeleRing (𝓞 K) K,
      ((ks * kx)⁻¹ * unipotentGL2 y * (ks * kx))⁻¹ = (ks * kx)⁻¹ * unipotentGL2 (-y) * (ks * kx) := by
    intro y
    have h1 : unipotentGL2 y * unipotentGL2 (-y) = 1 := by
      rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero]
    have h2 : ((ks * kx)⁻¹ * unipotentGL2 y * (ks * kx)) * ((ks * kx)⁻¹ * unipotentGL2 (-y) * (ks * kx))
        = (ks * kx)⁻¹ * (unipotentGL2 y * unipotentGL2 (-y)) * (ks * kx) := by
      group
    rw [h1, mul_one, inv_mul_cancel] at h2
    exact inv_eq_of_mul_eq_one_right h2
  refine ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  ·
    rw [NumberField.AdelicLevel.mem_levelOne_iff, map_mul, map_mul, map_inv, glFin_unipotentGL2_finShift, hgfin,
      NumberField.AdelicLevel.mem_finiteLevelOne_iff]
    refine ⟨?_, ?_⟩
    · rw [conj_unipotentGL2_coe]
      exact hlevel r hr
    · rw [hinv, conj_unipotentGL2_coe, ← mul_neg]
      exact hlevel (-r) hnegr
  ·
    rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_mul, map_inv, glArch_unipotentGL2_finShift, mul_one,
      inv_mul_cancel]
  ·
    intro v
    unfold componentMatrix
    rw [NumberField.AdelicLevel.finComponent_apply, map_mul, map_mul, map_inv, glFin_unipotentGL2_finShift, hgfin,
      conj_unipotentGL2_coe, Matrix.add_apply, Matrix.one_apply_eq, NumberField.AdelicLevel.coe_add_apply,
      NumberField.AdelicLevel.coe_one_apply, add_sub_cancel_left]
    exact hball r hr 0 0 v

private theorem finShift_eq_pair (y : FiniteAdeleRing (𝓞 K) K) :
    finShift y = (((0 : InfiniteAdeleRing K), y) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
  rfl

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.FiniteWhittaker"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section TranslateSumLeft

private theorem translateSum_globalPoints_mul
    {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    {n : ℕ} (ks : Fin n → AdelicGL2 (𝓞 K) K) (cs : Fin n → ℂ) :
    ∀ (γ : GL (Fin 2) K) (h : AdelicGL2 (𝓞 K) K),
      translateSum d archR archC dR dC dF ks cs (globalPoints (𝓞 K) K γ * h) =
        translateSum d archR archC dR dC dF ks cs h := by
  have hinv' : InvOn (kZeroSet S d.m) (jlSeries' d archR archC dR dC dF) := hinv
  intro γ h
  show (∑ i, cs i * theForm d archR archC dR dC dF (globalPoints (𝓞 K) K γ * h * ks i)) =
    ∑ i, cs i * theForm d archR archC dR dC dF (h * ks i)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, theForm_eq, extend_mul_left hinv' γ (h * ks i)]

end TranslateSumLeft

end LanglandsTunnell.Converse.CuspSynthesis

open NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section LatticeReduction

omit [NumberField K] in
open NumberField.InfinitePlace in
private theorem normAtPlace_ringEquiv_mixedSpace_apply (w : InfinitePlace K) (z : InfiniteAdeleRing K) :
    mixedEmbedding.normAtPlace w (InfiniteAdeleRing.ringEquiv_mixedSpace K z) = ‖z w‖ := by
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) (z w)
  · rw [mixedEmbedding.normAtPlace_apply_of_isComplex hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (z w)

open scoped Classical in
private theorem normAtPlace_le_norm_mixedSpace (w : InfinitePlace K) (x : mixedEmbedding.mixedSpace K) :
    mixedEmbedding.normAtPlace w x ≤ ‖x‖ := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => mixedEmbedding.normAtPlace w x) (Finset.mem_univ w)

private theorem exists_bound_forall_exists_add_algebraMap_mul_norm_le (a : 𝓞 K) (ha : a ≠ 0) :
    ∃ R : ℝ, ∀ y : InfiniteAdeleRing K, ∃ m : 𝓞 K,
      ∀ w : InfinitePlace K, ‖(y + algebraMap K (InfiniteAdeleRing K) (algebraMap (𝓞 K) K (a * m))) w‖ ≤ R := by
  classical
  have ha' : algebraMap (𝓞 K) K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
  have hI0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K a) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha'
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
    (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.fractionalIdealLatticeBasis K (Units.mk0 _ hI0)))
  refine ⟨C, fun y => ?_⟩
  set b := mixedEmbedding.fractionalIdealLatticeBasis K (Units.mk0 _ hI0) with hb
  set Y : mixedEmbedding.mixedSpace K := InfiniteAdeleRing.ringEquiv_mixedSpace K y with hY
  obtain ⟨x, hxI, hx⟩ := (mixedEmbedding.mem_span_fractionalIdealLatticeBasis K (Units.mk0 _ hI0)).1
    (ZSpan.floor b Y).2
  change x ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K a) at hxI
  rw [FractionalIdeal.mem_spanSingleton] at hxI
  obtain ⟨m, hm⟩ := hxI
  refine ⟨-m, fun w => ?_⟩
  have hxm : algebraMap K (InfiniteAdeleRing K) (algebraMap (𝓞 K) K (a * -m)) =
      -algebraMap K (InfiniteAdeleRing K) x := by
    simp only [← hm, Algebra.smul_def, map_mul, map_neg]
    ring
  rw [hxm, ← sub_eq_add_neg, ← normAtPlace_ringEquiv_mixedSpace_apply w (y - algebraMap K (InfiniteAdeleRing K) x),
    map_sub,    ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, hx, ← hY, ← ZSpan.fract_apply]
  exact (normAtPlace_le_norm_mixedSpace w _).trans (hC _ (ZSpan.fract_mem_fundamentalDomain b Y))

end LatticeReduction

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel
p2m_open "AutomorphicForm.SiegelCovering LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section WindowShift

variable {𝕜 : Type} [RCLike 𝕜]

open ComplexConjugate

private theorem lagrange_identity (a b c d : 𝕜) :
    ‖a * conj c + b * conj d‖ ^ 2 + ‖a * d - b * c‖ ^ 2 = (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  simp only [RCLike.norm_sq_eq_def, map_add, map_sub, RCLike.mul_re, RCLike.mul_im, RCLike.conj_re,
    RCLike.conj_im]
  ring

private theorem window_eq_sq (a b c d : 𝕜) (hN : 0 < ‖c‖ ^ 2 + ‖d‖ ^ 2) :
    (‖a‖ ^ 2 + ‖b‖ ^ 2) / (‖c‖ ^ 2 + ‖d‖ ^ 2) - (‖a * d - b * c‖ / (‖c‖ ^ 2 + ‖d‖ ^ 2)) ^ 2
      = (‖a * conj c + b * conj d‖ / (‖c‖ ^ 2 + ‖d‖ ^ 2)) ^ 2 := by
  have hL := lagrange_identity a b c d
  have hN' : ‖c‖ ^ 2 + ‖d‖ ^ 2 ≠ 0 := hN.ne'
  field_simp
  linear_combination (-1 : ℝ) * hL

private theorem norm_inner_shift_le (a b c d t : 𝕜) :
    ‖(a + t * c) * conj c + (b + t * d) * conj d‖
      ≤ ‖a * conj c + b * conj d‖ + ‖t‖ * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h1 : (a + t * c) * conj c + (b + t * d) * conj d
      = (a * conj c + b * conj d) + t * (c * conj c + d * conj d) := by ring
  rw [h1]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg t)
  calc ‖c * conj c + d * conj d‖ ≤ ‖c * conj c‖ + ‖d * conj d‖ := norm_add_le _ _
    _ = ‖c‖ ^ 2 + ‖d‖ ^ 2 := by rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]; ring

private theorem window_shift_le {a b c d t : 𝕜} {u R : ℝ} (hN : 0 < ‖c‖ ^ 2 + ‖d‖ ^ 2)
    (hw : (‖a‖ ^ 2 + ‖b‖ ^ 2) / (‖c‖ ^ 2 + ‖d‖ ^ 2) - (‖a * d - b * c‖ / (‖c‖ ^ 2 + ‖d‖ ^ 2)) ^ 2 ≤ u ^ 2)
    (ht : ‖t‖ ≤ R) :
    (‖a + t * c‖ ^ 2 + ‖b + t * d‖ ^ 2) / (‖c‖ ^ 2 + ‖d‖ ^ 2)
        - (‖(a + t * c) * d - (b + t * d) * c‖ / (‖c‖ ^ 2 + ‖d‖ ^ 2)) ^ 2
      ≤ (|u| + R) ^ 2 := by
  rw [window_eq_sq a b c d hN] at hw
  rw [window_eq_sq (a + t * c) (b + t * d) c d hN]
  set N := ‖c‖ ^ 2 + ‖d‖ ^ 2 with hNdef
  have hx : ‖a * conj c + b * conj d‖ / N ≤ |u| := by
    have h0 : 0 ≤ ‖a * conj c + b * conj d‖ / N := div_nonneg (norm_nonneg _) hN.le
    have h := sq_le_sq.1 hw
    rwa [abs_of_nonneg h0] at h
  have hR : 0 ≤ R := (norm_nonneg t).trans ht
  have hshift : ‖(a + t * c) * conj c + (b + t * d) * conj d‖ / N ≤ |u| + R := by
    calc ‖(a + t * c) * conj c + (b + t * d) * conj d‖ / N
        ≤ (‖a * conj c + b * conj d‖ + ‖t‖ * N) / N :=
          div_le_div_of_nonneg_right (norm_inner_shift_le a b c d t) hN.le
      _ = ‖a * conj c + b * conj d‖ / N + ‖t‖ := by field_simp
      _ ≤ |u| + R := add_le_add hx ht
  exact pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hN.le) hshift 2

end WindowShift

section ThroughHom

private theorem window_shift_le_of_hom {L : Type} [NormedField L] (f : L →+* ℂ) (hf : ∀ x : L, ‖f x‖ = ‖x‖)
    {a b c d t : L} {u R : ℝ} (hN : 0 < ‖c‖ ^ 2 + ‖d‖ ^ 2)
    (hw : (‖a‖ ^ 2 + ‖b‖ ^ 2) / (‖c‖ ^ 2 + ‖d‖ ^ 2) - (‖a * d - b * c‖ / (‖c‖ ^ 2 + ‖d‖ ^ 2)) ^ 2 ≤ u ^ 2)
    (ht : ‖t‖ ≤ R) :
    (‖a + t * c‖ ^ 2 + ‖b + t * d‖ ^ 2) / (‖c‖ ^ 2 + ‖d‖ ^ 2)
        - (‖(a + t * c) * d - (b + t * d) * c‖ / (‖c‖ ^ 2 + ‖d‖ ^ 2)) ^ 2
      ≤ (|u| + R) ^ 2 := by
  have h := @window_shift_le ℂ _ (f a) (f b) (f c) (f d) (f t) u R
  simp only [← map_mul, ← map_add, ← map_sub, hf] at h
  exact h hN hw ht

end ThroughHom

section PerPlace

open AutomorphicForm AutomorphicForm.WindowedSiegel

variable {L : Type} [NormedField L]

private theorem unipotentGL2_mul_val (t : L) (H : GL (Fin 2) L) :
    ((unipotentGL2 t * H : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = !![(H : Matrix (Fin 2) (Fin 2) L) 0 0 + t * (H : Matrix (Fin 2) (Fin 2) L) 1 0,
            (H : Matrix (Fin 2) (Fin 2) L) 0 1 + t * (H : Matrix (Fin 2) (Fin 2) L) 1 1;
          (H : Matrix (Fin 2) (Fin 2) L) 1 0, (H : Matrix (Fin 2) (Fin 2) L) 1 1] := by
  rw [Units.val_mul, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem rowNormSq_unipotentGL2_mul (t : L) (H : GL (Fin 2) L) :
    rowNormSq ((unipotentGL2 t * H : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = rowNormSq (H : Matrix (Fin 2) (Fin 2) L) := by
  rw [unipotentGL2_mul_val]
  simp [rowNormSq]

private theorem det_unipotentGL2_mul (t : L) (H : GL (Fin 2) L) :
    ((unipotentGL2 t * H : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = (H : Matrix (Fin 2) (Fin 2) L).det := by
  rw [Units.val_mul, Matrix.det_mul, unipotentGL2_coe]
  simp [Matrix.det_fin_two_of]

private theorem localHeight_unipotentGL2_mul (t : L) (H : GL (Fin 2) L) :
    localHeight (unipotentGL2 t * H) = localHeight H := by
  unfold localHeight
  rw [det_unipotentGL2_mul, rowNormSq_unipotentGL2_mul]

private theorem xWindowSq_unipotentGL2_mul_le (f : L →+* ℂ) (hf : ∀ x : L, ‖f x‖ = ‖x‖) {t : L} {H : GL (Fin 2) L}
    {u R : ℝ} (hN : 0 < rowNormSq (H : Matrix (Fin 2) (Fin 2) L)) (hH : xWindowSq H ≤ u ^ 2) (ht : ‖t‖ ≤ R) :
    xWindowSq (unipotentGL2 t * H) ≤ (|u| + R) ^ 2 := by
  unfold xWindowSq localHeight at hH ⊢
  rw [unipotentGL2_mul_val]
  unfold rowNormSq at hN
  unfold topNormSq rowNormSq at hH ⊢
  rw [Matrix.det_fin_two] at hH ⊢
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hH hN ⊢
  exact window_shift_le_of_hom f hf hN hH ht

end PerPlace

section Adelic

open NumberField.AdelicVolume

private theorem archComponent_glArch_unipotentGL2_mul (w : InfinitePlace K) (a : AdeleRing (𝓞 K) K)
    (g : AdelicGL2 (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K (unipotentGL2 a * g))
      = unipotentGL2 (a.1 w) * archComponent K w (glArch (𝓞 K) K g) := by
  rw [map_mul, map_mul, glArch_unipotentGL2]
  congr 1
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [archComponent_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem localHeight_archComponent_unipotentGL2_mul (w : InfinitePlace K) (a : AdeleRing (𝓞 K) K)
    (g : AdelicGL2 (𝓞 K) K) :
    localHeight (archComponent K w (glArch (𝓞 K) K (unipotentGL2 a * g)))
      = localHeight (archComponent K w (glArch (𝓞 K) K g)) := by
  rw [archComponent_glArch_unipotentGL2_mul, localHeight_unipotentGL2_mul]

private theorem archDetNorm_unipotentGL2_mul (w : InfinitePlace K) (a : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    archDetNorm w (unipotentGL2 a * g) = archDetNorm w g := by
  unfold archDetNorm
  rw [archComponent_glArch_unipotentGL2_mul, det_unipotentGL2_mul]

private theorem glFin_unipotentGL2_mul_of_snd_eq_zero {a : AdeleRing (𝓞 K) K} (ha : a.2 = 0) (g : AdelicGL2 (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 a * g) = glFin (𝓞 K) K g := by
  rw [map_mul, glFin_unipotentGL2, ha, unipotentGL2_zero, one_mul]

private theorem unipotentGL2_mul_mem_window_of_norm_le (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) {R : ℝ}
    {y : InfiniteAdeleRing K} (hy : ∀ w : InfinitePlace K, ‖y w‖ ≤ R)
    {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ (pinsOf c u d₁ d₂ T).D) :
    unipotentGL2 (R := AdeleRing (𝓞 K) K)
        (((y, 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g ∈
      (pinsOf c (|u| + R) d₁ d₂ T).D := by
  have hg' : g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂ := hg
  show _ ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c (|u| + R) d₁ d₂
  obtain ⟨x, hxT, s, hs, rfl⟩ := by
    simpa only [Set.mem_iUnion, Set.mem_image, exists_prop] using hg'
  obtain ⟨h1, h2, h3, h4⟩ := mem_centreCutSiegelSet_iff.1 hs
  refine Set.mem_iUnion₂.2 ⟨x, hxT,
    unipotentGL2 (R := AdeleRing (𝓞 K) K)
        (((y, 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * s, ?_,
    mul_assoc _ _ _⟩
  refine mem_centreCutSiegelSet_iff.2 ⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩
  · rw [glFin_unipotentGL2_mul_of_snd_eq_zero]
    · exact h1
    · rfl
  · rw [localHeight_archComponent_unipotentGL2_mul]
    exact h2 w
  · rw [archComponent_glArch_unipotentGL2_mul]
    exact xWindowSq_unipotentGL2_mul_le (InfinitePlace.Completion.extensionEmbedding w)
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _))
      (rowNormSq_pos _) (h3 w) (hy w)
  · rw [archDetNorm_unipotentGL2_mul]
    exact h4 w

end Adelic

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

namespace ProfileArith

private theorem rpow_neg_mul_le_of_le {x σ σ' : ℝ} (hx : 0 < x) (hσ' : σ' ≤ σ) {n : ℕ} (hn : σ - σ' ≤ n)
    (M : ℕ) :
    x ^ (-σ') * (1 + x) ^ (-((M + n : ℕ) : ℝ)) ≤ x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) := by
  have h1x : 0 < 1 + x := by linarith
  have hpow : x ^ (σ - σ') ≤ (1 + x) ^ (n : ℝ) := by
    calc x ^ (σ - σ') ≤ (1 + x) ^ (σ - σ') :=
          Real.rpow_le_rpow hx.le (by linarith) (by linarith)
      _ ≤ (1 + x) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hn
  have hsplit : x ^ (-σ') = x ^ (-σ) * x ^ (σ - σ') := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have hsplit' : (1 + x) ^ (-((M + n : ℕ) : ℝ)) = (1 + x) ^ (-(M : ℝ)) * ((1 + x) ^ (n : ℝ))⁻¹ := by
    rw [← Real.rpow_neg h1x.le, ← Real.rpow_add h1x]; congr 1; push_cast; ring
  rw [hsplit, hsplit']
  have hpos : 0 < (1 + x) ^ (n : ℝ) := Real.rpow_pos_of_pos h1x _
  have hxσ : 0 ≤ x ^ (-σ) := (Real.rpow_pos_of_pos hx _).le
  have hM : 0 ≤ (1 + x) ^ (-(M : ℝ)) := (Real.rpow_pos_of_pos h1x _).le
  calc x ^ (-σ) * x ^ (σ - σ') * ((1 + x) ^ (-(M : ℝ)) * ((1 + x) ^ (n : ℝ))⁻¹)
      = x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) * (x ^ (σ - σ') / (1 + x) ^ (n : ℝ)) := by ring
    _ ≤ x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) * 1 := by
          gcongr
          exact (div_le_one hpos).mpr hpow
    _ = x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) := mul_one _

private theorem le_profile_of_le_small {F x s B x₁ : ℝ} (hx : 0 < x) (hxx₁ : x ≤ x₁) (hB : 0 ≤ B) (M : ℕ)
    (h : F ≤ B * x ^ (-s)) :
    F ≤ B * (1 + x₁) ^ (M : ℝ) * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := by
  have h1x : 0 < 1 + x := by linarith
  have h1x₁ : 0 < 1 + x₁ := by linarith
  have hxs : 0 ≤ x ^ (-s) := (Real.rpow_pos_of_pos hx _).le
  have hratio : 1 ≤ (1 + x₁) ^ (M : ℝ) * (1 + x) ^ (-(M : ℝ)) := by
    rw [Real.rpow_neg h1x.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos h1x _), one_mul]
    exact Real.rpow_le_rpow h1x.le (by linarith) (Nat.cast_nonneg M)
  calc F ≤ B * x ^ (-s) := h
    _ = B * x ^ (-s) * 1 := (mul_one _).symm
    _ ≤ B * x ^ (-s) * ((1 + x₁) ^ (M : ℝ) * (1 + x) ^ (-(M : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg hB hxs)
    _ = B * (1 + x₁) ^ (M : ℝ) * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := by ring

private theorem rpow_neg_add_le_large {x s : ℝ} (hx : 1 ≤ x) (M : ℕ) :
    x ^ (-(s + M)) ≤ (2 : ℝ) ^ (M : ℝ) * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have h1x : 0 < 1 + x := by linarith
  have hsplit : x ^ (-(s + M)) = x ^ (-s) * x ^ (-(M : ℝ)) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hkey : x ^ (-(M : ℝ)) ≤ (2 : ℝ) ^ (M : ℝ) * (1 + x) ^ (-(M : ℝ)) := by
    have h2x : (1 + x) ^ (M : ℝ) ≤ (2 * x) ^ (M : ℝ) :=
      Real.rpow_le_rpow h1x.le (by linarith) (Nat.cast_nonneg M)
    rw [Real.mul_rpow (by norm_num) hx0.le] at h2x
    rw [Real.rpow_neg hx0.le, Real.rpow_neg h1x.le]
    have hxM : 0 < x ^ (M : ℝ) := Real.rpow_pos_of_pos hx0 _
    have h1xM : 0 < (1 + x) ^ (M : ℝ) := Real.rpow_pos_of_pos h1x _
    rw [← div_eq_mul_inv, le_div_iff₀ h1xM, inv_mul_eq_div, div_le_iff₀ hxM]
    linarith
  rw [hsplit]
  have hxs : 0 ≤ x ^ (-s) := (Real.rpow_pos_of_pos hx0 _).le
  calc x ^ (-s) * x ^ (-(M : ℝ)) ≤ x ^ (-s) * ((2 : ℝ) ^ (M : ℝ) * (1 + x) ^ (-(M : ℝ))) :=
        mul_le_mul_of_nonneg_left hkey hxs
    _ = (2 : ℝ) ^ (M : ℝ) * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := by ring

private theorem one_le_add_inv {Y : ℝ} (hY : 0 < Y) : 1 ≤ Y + Y⁻¹ := by
  have hYi : 0 < Y⁻¹ := inv_pos.mpr hY
  rcases le_or_gt 1 Y with h1 | h1
  · linarith
  · have : 1 < Y⁻¹ := (one_lt_inv₀ hY).mpr h1
    linarith

private theorem rpow_le_weight {Y b e : ℝ} (hY : 0 < Y) (hbe : |b| ≤ e) : Y ^ b ≤ (Y + Y⁻¹) ^ e := by
  have hw1 : 1 ≤ Y + Y⁻¹ := one_le_add_inv hY
  have hYi : 0 < Y⁻¹ := inv_pos.mpr hY
  have hYw : Y ≤ Y + Y⁻¹ := le_add_of_nonneg_right hYi.le
  have hYiw : Y⁻¹ ≤ Y + Y⁻¹ := le_add_of_nonneg_left hY.le
  rcases le_or_gt 0 b with hb | hb
  · have hbe' : b ≤ e := le_trans (le_abs_self b) hbe
    calc Y ^ b ≤ (Y + Y⁻¹) ^ b := Real.rpow_le_rpow hY.le hYw hb
      _ ≤ (Y + Y⁻¹) ^ e := Real.rpow_le_rpow_of_exponent_le hw1 hbe'
  · have hnb : 0 ≤ -b := by linarith
    have hbe' : -b ≤ e := le_trans (neg_le_abs b) hbe
    have hsplit : Y ^ b = (Y⁻¹) ^ (-b) := by
      rw [Real.inv_rpow hY.le, ← Real.rpow_neg hY.le, neg_neg]
    calc Y ^ b = (Y⁻¹) ^ (-b) := hsplit
      _ ≤ (Y + Y⁻¹) ^ (-b) := Real.rpow_le_rpow hYi.le hYiw hnb
      _ ≤ (Y + Y⁻¹) ^ e := Real.rpow_le_rpow_of_exponent_le hw1 hbe'

private theorem one_add_inv_rpow_le {Y : ℝ} (hY : 0 < Y) (M : ℕ) :
    (1 + Y⁻¹) ^ (M : ℝ) ≤ (2 : ℝ) ^ (M : ℝ) * (Y + Y⁻¹) ^ (M : ℝ) := by
  have hw1 : 1 ≤ Y + Y⁻¹ := one_le_add_inv hY
  have hYi : 0 < Y⁻¹ := inv_pos.mpr hY
  have hle : 1 + Y⁻¹ ≤ 2 * (Y + Y⁻¹) := by linarith
  calc (1 + Y⁻¹) ^ (M : ℝ) ≤ (2 * (Y + Y⁻¹)) ^ (M : ℝ) :=
        Real.rpow_le_rpow (by linarith) hle (Nat.cast_nonneg M)
    _ = (2 : ℝ) ^ (M : ℝ) * (Y + Y⁻¹) ^ (M : ℝ) := Real.mul_rpow (by norm_num) (by linarith)

private theorem exists_exponent_profile_of_two_regime {σ p : ℝ} (hσ : 0 ≤ σ) (M : ℕ) :
    ∃ e : ℝ, 0 ≤ e ∧ ∀ (C₀ : ℝ) (C₁ : ℕ → ℝ), ∃ A : ℝ, ∀ (F x Y : ℝ), 0 < x → 0 < Y →
      (x * Y ≤ 1 → F ≤ C₀ * Y ^ p * (x * Y) ^ (-σ)) →
      (∀ N : ℕ, 1 ≤ x * Y → F ≤ C₁ N * Y ^ p * (x * Y) ^ (-(N : ℝ))) →
      F ≤ A * x ^ (-(max σ p)) * (1 + x) ^ (-(M : ℝ)) * (Y + Y⁻¹) ^ e := by
  set s : ℝ := max σ p with hs_def
  have hs : 0 ≤ s := le_trans hσ (le_max_left _ _)
  have hσs : σ ≤ s := le_max_left _ _
  have hps : p ≤ s := le_max_right _ _
  have hpabs : 0 ≤ |p| := abs_nonneg p
  have hp_le : p ≤ |p| := le_abs_self p
  have hp_ge : -|p| ≤ p := neg_abs_le p
  set n : ℕ := ⌈s⌉₊ with hn_def
  have hsn : s ≤ (n : ℝ) := Nat.le_ceil s
  set N₀ : ℕ := n + M with hN₀_def
  have hN₀ : s + M ≤ (N₀ : ℝ) := by simp only [hN₀_def, Nat.cast_add]; linarith
  have hN₀0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  refine ⟨s + s + |p| + M + N₀, by linarith, fun C₀ C₁ => ?_⟩
  set Bmax : ℝ := max (max C₀ 0) (max (C₁ N₀) 0) with hBmax_def
  have hBmax0 : 0 ≤ Bmax := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC₀B : max C₀ 0 ≤ Bmax := le_max_left _ _
  have hC₁B : max (C₁ N₀) 0 ≤ Bmax := le_max_right _ _
  have hC₀0 : 0 ≤ max C₀ 0 := le_max_right _ _
  have hC₁0 : 0 ≤ max (C₁ N₀) 0 := le_max_right _ _
  refine ⟨(2 : ℝ) ^ (M : ℝ) * Bmax, fun F x Y hx hY hsmall hlarge => ?_⟩
  have h2M : 0 ≤ (2 : ℝ) ^ (M : ℝ) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hxs : 0 ≤ x ^ (-s) := (Real.rpow_pos_of_pos hx _).le
  have h1x : 0 < 1 + x := by linarith
  have h1xM : 0 ≤ (1 + x) ^ (-(M : ℝ)) := (Real.rpow_pos_of_pos h1x _).le
  have hprof : 0 ≤ x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := mul_nonneg hxs h1xM
  have hw : 0 < Y + Y⁻¹ := by linarith [one_le_add_inv hY]
  have hw1 : 1 ≤ Y + Y⁻¹ := one_le_add_inv hY
  have hclose : ∀ {B a : ℝ}, 0 ≤ B → B ≤ Bmax → a ≤ s + s + |p| + M + N₀ →
      F ≤ (2 : ℝ) ^ (M : ℝ) * B * (Y + Y⁻¹) ^ a * (x ^ (-s) * (1 + x) ^ (-(M : ℝ))) →
      F ≤ (2 : ℝ) ^ (M : ℝ) * Bmax * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) * (Y + Y⁻¹) ^ (s + s + |p| + M + N₀) := by
    intro B a hB0 hB hae h
    have hwa : (Y + Y⁻¹) ^ a ≤ (Y + Y⁻¹) ^ (s + s + |p| + M + N₀) := Real.rpow_le_rpow_of_exponent_le hw1 hae
    have hwa0 : 0 ≤ (Y + Y⁻¹) ^ a := (Real.rpow_pos_of_pos hw _).le
    have hwe0 : 0 ≤ (Y + Y⁻¹) ^ (s + s + |p| + M + N₀) := (Real.rpow_pos_of_pos hw _).le
    calc F ≤ (2 : ℝ) ^ (M : ℝ) * B * (Y + Y⁻¹) ^ a * (x ^ (-s) * (1 + x) ^ (-(M : ℝ))) := h
      _ ≤ (2 : ℝ) ^ (M : ℝ) * Bmax * (Y + Y⁻¹) ^ (s + s + |p| + M + N₀) * (x ^ (-s) * (1 + x) ^ (-(M : ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ hprof
          exact mul_le_mul (mul_le_mul_of_nonneg_left hB h2M) hwa hwa0 (mul_nonneg h2M hBmax0)
      _ = (2 : ℝ) ^ (M : ℝ) * Bmax * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) * (Y + Y⁻¹) ^ (s + s + |p| + M + N₀) := by
          ring
  rcases le_or_gt (x * Y) 1 with hreg | hreg
  ·
    have hYx : Y ≤ x⁻¹ := by
      rw [← one_div, le_div_iff₀ hx, mul_comm]
      exact hreg
    have hxle : x ≤ Y⁻¹ := (le_inv_comm₀ hx hY).mpr hYx
    have hF := hsmall hreg
    have hrew : Y ^ p * (x * Y) ^ (-σ) = x ^ (-σ) * Y ^ (p - σ) := by
      rw [Real.mul_rpow hx.le hY.le, Real.rpow_sub hY, Real.rpow_neg hY.le, div_eq_mul_inv]; ring
    have hxsplit : x ^ (-σ) = x ^ (-s) * x ^ (s - σ) := by
      rw [← Real.rpow_add hx]; congr 1; ring
    have hxsσ : x ^ (s - σ) ≤ (Y + Y⁻¹) ^ s := by
      calc x ^ (s - σ) ≤ (Y⁻¹) ^ (s - σ) := Real.rpow_le_rpow hx.le hxle (by linarith)
        _ = Y ^ (-(s - σ)) := by rw [Real.inv_rpow hY.le, ← Real.rpow_neg hY.le]
        _ ≤ (Y + Y⁻¹) ^ s := rpow_le_weight hY (by rw [abs_neg, abs_of_nonneg (by linarith)]; linarith)
    have hYp : Y ^ (p - σ) ≤ (Y + Y⁻¹) ^ (|p| + s) :=
      rpow_le_weight hY (by rw [abs_le]; constructor <;> linarith)
    have hws : 0 ≤ (Y + Y⁻¹) ^ s := (Real.rpow_pos_of_pos hw _).le
    have hwps : 0 ≤ (Y + Y⁻¹) ^ (|p| + s) := (Real.rpow_pos_of_pos hw _).le
    have hB0 : 0 ≤ max C₀ 0 * ((Y + Y⁻¹) ^ s * (Y + Y⁻¹) ^ (|p| + s)) :=
      mul_nonneg hC₀0 (mul_nonneg hws hwps)
    have hstep : F ≤ max C₀ 0 * ((Y + Y⁻¹) ^ s * (Y + Y⁻¹) ^ (|p| + s)) * x ^ (-s) := by
      calc F ≤ C₀ * Y ^ p * (x * Y) ^ (-σ) := hF
        _ = C₀ * (x ^ (-σ) * Y ^ (p - σ)) := by rw [mul_assoc, hrew]
        _ ≤ max C₀ 0 * (x ^ (-σ) * Y ^ (p - σ)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _)
              (mul_nonneg (Real.rpow_pos_of_pos hx _).le (Real.rpow_pos_of_pos hY _).le)
        _ = max C₀ 0 * (x ^ (-s) * (x ^ (s - σ) * Y ^ (p - σ))) := by rw [hxsplit]; ring
        _ ≤ max C₀ 0 * (x ^ (-s) * ((Y + Y⁻¹) ^ s * (Y + Y⁻¹) ^ (|p| + s))) := by
            apply mul_le_mul_of_nonneg_left _ hC₀0
            apply mul_le_mul_of_nonneg_left _ hxs
            exact mul_le_mul hxsσ hYp (Real.rpow_pos_of_pos hY _).le hws
        _ = max C₀ 0 * ((Y + Y⁻¹) ^ s * (Y + Y⁻¹) ^ (|p| + s)) * x ^ (-s) := by ring
    have hfin := le_profile_of_le_small hx hxle hB0 M hstep
    have hmerge : (Y + Y⁻¹) ^ s * (Y + Y⁻¹) ^ (|p| + s) * (Y + Y⁻¹) ^ (M : ℝ) = (Y + Y⁻¹) ^ (s + (|p| + s) + M) := by
      rw [← Real.rpow_add hw, ← Real.rpow_add hw]
    have hwM : 0 ≤ (Y + Y⁻¹) ^ (M : ℝ) := (Real.rpow_pos_of_pos hw _).le
    refine hclose hC₀0 hC₀B (a := s + (|p| + s) + M) (by linarith) ?_
    calc F ≤ max C₀ 0 * ((Y + Y⁻¹) ^ s * (Y + Y⁻¹) ^ (|p| + s)) * (1 + Y⁻¹) ^ (M : ℝ) * x ^ (-s)
            * (1 + x) ^ (-(M : ℝ)) := hfin
      _ = max C₀ 0 * ((Y + Y⁻¹) ^ s * (Y + Y⁻¹) ^ (|p| + s)) * (1 + Y⁻¹) ^ (M : ℝ)
            * (x ^ (-s) * (1 + x) ^ (-(M : ℝ))) := by ring
      _ ≤ max C₀ 0 * ((Y + Y⁻¹) ^ s * (Y + Y⁻¹) ^ (|p| + s)) * ((2 : ℝ) ^ (M : ℝ) * (Y + Y⁻¹) ^ (M : ℝ))
            * (x ^ (-s) * (1 + x) ^ (-(M : ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ hprof
          exact mul_le_mul_of_nonneg_left (one_add_inv_rpow_le hY M) hB0
      _ = (2 : ℝ) ^ (M : ℝ) * max C₀ 0 * ((Y + Y⁻¹) ^ s * (Y + Y⁻¹) ^ (|p| + s) * (Y + Y⁻¹) ^ (M : ℝ))
            * (x ^ (-s) * (1 + x) ^ (-(M : ℝ))) := by ring
      _ = (2 : ℝ) ^ (M : ℝ) * max C₀ 0 * (Y + Y⁻¹) ^ (s + (|p| + s) + M) * (x ^ (-s) * (1 + x) ^ (-(M : ℝ))) := by
          rw [hmerge]
  ·
    have hF := hlarge N₀ hreg.le
    have hxY : 0 < x * Y := mul_pos hx hY
    have hrew : Y ^ p * (x * Y) ^ (-(N₀ : ℝ)) = (x * Y) ^ (p - N₀) * x ^ (-p) := by
      have e1 : (x * Y) ^ (p - N₀) = x ^ p * Y ^ p * (x * Y) ^ (-(N₀ : ℝ)) := by
        rw [sub_eq_add_neg, Real.rpow_add hxY, Real.mul_rpow hx.le hY.le]
      have e2 : x ^ p * x ^ (-p) = 1 := by
        rw [Real.rpow_neg hx.le]
        exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hx _).ne'
      calc Y ^ p * (x * Y) ^ (-(N₀ : ℝ)) = Y ^ p * (x * Y) ^ (-(N₀ : ℝ)) * (x ^ p * x ^ (-p)) := by
            rw [e2, mul_one]
        _ = (x * Y) ^ (p - N₀) * x ^ (-p) := by rw [e1]; ring
    have hF' : F ≤ max (C₁ N₀) 0 * ((x * Y) ^ (p - N₀) * x ^ (-p)) := by
      calc F ≤ C₁ N₀ * Y ^ p * (x * Y) ^ (-(N₀ : ℝ)) := hF
        _ = C₁ N₀ * (Y ^ p * (x * Y) ^ (-(N₀ : ℝ))) := by ring
        _ ≤ max (C₁ N₀) 0 * (Y ^ p * (x * Y) ^ (-(N₀ : ℝ))) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _)
              (mul_nonneg (Real.rpow_pos_of_pos hY _).le (Real.rpow_pos_of_pos hxY _).le)
        _ = max (C₁ N₀) 0 * ((x * Y) ^ (p - N₀) * x ^ (-p)) := by rw [hrew]
    have hpN₀ : p - N₀ ≤ 0 := by linarith
    rcases le_or_gt x 1 with hx1 | hx1
    ·
      have h1 : (x * Y) ^ (p - N₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hreg.le hpN₀
      have h2 : x ^ (-p) ≤ x ^ (-s) := Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)
      have hstep : F ≤ max (C₁ N₀) 0 * x ^ (-s) := by
        calc F ≤ max (C₁ N₀) 0 * ((x * Y) ^ (p - N₀) * x ^ (-p)) := hF'
          _ ≤ max (C₁ N₀) 0 * (1 * x ^ (-s)) := by
              apply mul_le_mul_of_nonneg_left _ hC₁0
              exact mul_le_mul h1 h2 (Real.rpow_pos_of_pos hx _).le zero_le_one
          _ = max (C₁ N₀) 0 * x ^ (-s) := by ring
      have hfin := le_profile_of_le_small hx hx1 hC₁0 M hstep
      have h11 : (1 + (1 : ℝ)) = 2 := by norm_num
      rw [h11] at hfin
      refine hclose hC₁0 hC₁B (a := 0) (by linarith) ?_
      rw [Real.rpow_zero]
      calc F ≤ max (C₁ N₀) 0 * (2 : ℝ) ^ (M : ℝ) * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := hfin
        _ = (2 : ℝ) ^ (M : ℝ) * max (C₁ N₀) 0 * 1 * (x ^ (-s) * (1 + x) ^ (-(M : ℝ))) := by ring
    ·
      have hsplitxY : (x * Y) ^ (p - N₀) = x ^ (p - N₀) * Y ^ (p - N₀) := Real.mul_rpow hx.le hY.le
      have hYp : Y ^ (p - N₀) ≤ (Y + Y⁻¹) ^ (|p| + N₀) :=
        rpow_le_weight hY (by rw [abs_le]; constructor <;> linarith)
      have hcomb : x ^ (p - N₀) * x ^ (-p) = x ^ (-(N₀ : ℝ)) := by
        rw [← Real.rpow_add hx]; congr 1; ring
      have hN : x ^ (-(N₀ : ℝ)) ≤ x ^ (-(s + M)) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      have hlarge' := rpow_neg_add_le_large (s := s) hx1.le M
      have hwN : 0 ≤ (Y + Y⁻¹) ^ (|p| + N₀) := (Real.rpow_pos_of_pos hw _).le
      refine hclose hC₁0 hC₁B (a := |p| + N₀) (by linarith) ?_
      calc F ≤ max (C₁ N₀) 0 * ((x * Y) ^ (p - N₀) * x ^ (-p)) := hF'
        _ = max (C₁ N₀) 0 * (Y ^ (p - N₀) * (x ^ (p - N₀) * x ^ (-p))) := by rw [hsplitxY]; ring
        _ = max (C₁ N₀) 0 * (Y ^ (p - N₀) * x ^ (-(N₀ : ℝ))) := by rw [hcomb]
        _ ≤ max (C₁ N₀) 0
              * ((Y + Y⁻¹) ^ (|p| + N₀) * ((2 : ℝ) ^ (M : ℝ) * x ^ (-s) * (1 + x) ^ (-(M : ℝ)))) := by
            apply mul_le_mul_of_nonneg_left _ hC₁0
            exact mul_le_mul hYp (hN.trans hlarge') (Real.rpow_pos_of_pos hx _).le hwN
        _ = (2 : ℝ) ^ (M : ℝ) * max (C₁ N₀) 0 * (Y + Y⁻¹) ^ (|p| + N₀)
              * (x ^ (-s) * (1 + x) ^ (-(M : ℝ))) := by
            ring

private theorem exists_rpow_le_mul_rpow_signed {D₁ D₂ : ℝ} (hD₁ : 0 < D₁) (q : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r D y : ℝ, 0 < r → D₁ ≤ D → D ≤ D₂ → 0 < y → r ^ 2 = D / y →
      r ^ q ≤ B * y ^ (-(q / 2)) := by
  refine ⟨max (D₁ ^ (q / 2)) (D₂ ^ (q / 2)), le_max_of_le_left (Real.rpow_pos_of_pos hD₁ _).le,
    fun r D y hr hD₁D hDD₂ hy h => ?_⟩
  have hD : 0 < D := lt_of_lt_of_le hD₁ hD₁D
  have hsplit : r ^ q = D ^ (q / 2) * y ^ (-(q / 2)) := by
    have h1 : r ^ q = (r ^ (2 : ℝ)) ^ (q / 2) := by
      rw [← Real.rpow_mul hr.le]; congr 1; ring
    rw [h1, Real.rpow_two, h, Real.div_rpow hD.le hy.le, Real.rpow_neg hy.le, div_eq_mul_inv]
  have hyq : 0 ≤ y ^ (-(q / 2)) := (Real.rpow_pos_of_pos hy _).le
  rw [hsplit]
  refine mul_le_mul_of_nonneg_right ?_ hyq
  rcases le_or_gt 0 q with hq | hq
  · exact le_trans (Real.rpow_le_rpow hD.le hDD₂ (by linarith)) (le_max_right _ _)
  · exact le_trans (Real.rpow_le_rpow_of_nonpos hD₁ hD₁D (by linarith)) (le_max_left _ _)

end ProfileArith

end LanglandsTunnell.Converse

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

open LanglandsTunnell.TateLocal NumberField.StandardAddChar

section CosetCover

private theorem exists_wf_bound_on_principal {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    (dF : FinWhittakerDatum K S Pi)
    (hgrow : ∃ κ : ℝ, ∀ v ∉ S,
      ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ)
    (coef : Kˣ → ℂ)
    (hfloor : ∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) → coef α = 0)
    (h : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K) (D : Set (AdelicGL2 (𝓞 K) K))
    (hD : ∃ T : Finset (AdelicGL2 (𝓞 K) K), ∀ g ∈ D, ∃ t ∈ T, ∃ u ∈ levelOne (𝓞 K) K ⊤, h g = t * u) :
    ∃ δ : 𝓞 K, δ ≠ 0 ∧ ∃ V ∈ Filter.principal D, ∃ C κ : ℝ, 0 ≤ κ ∧ ∀ g ∈ V, ∀ α : Kˣ,
      coef α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g) ≠ 0 →
        α ∈ integralAfter δ ∧
          ‖dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ ≤ C * |Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ := by
  classical
  obtain ⟨T, hT⟩ := hD
  choose δt hδt Vt hVt Ct κt hκt hbt using
    fun t : AdelicGL2 (𝓞 K) K => exists_nhds_wf_bound dF hgrow coef hfloor t
  refine ⟨∏ t ∈ T, δt t, Finset.prod_ne_zero_iff.mpr fun t _ => hδt t, D, Filter.mem_principal_self D,
    ∑ t ∈ T, |Ct t|, ∑ t ∈ T, κt t, Finset.sum_nonneg fun t _ => hκt t, fun g hg α hne => ?_⟩
  obtain ⟨t, ht, u, hu, hgu⟩ := hT g hg
  have htrans : dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)
      = dF.Wf (globalPoints (𝓞 K) K (diagOne α) * t) := by
    rw [hgu, ← mul_assoc]
    exact FiniteWhittaker.wf_mul_of_glFin_mem_top dF _ hu
  rw [htrans] at hne ⊢
  obtain ⟨⟨β, hβ⟩, hbound⟩ := hbt t t (mem_of_mem_nhds (hVt t)) α hne
  have hprod : (∏ s ∈ T, δt s) = δt t * ∏ s ∈ T.erase t, δt s := (Finset.mul_prod_erase T δt ht).symm
  have hrest : (∏ s ∈ T.erase t, δt s) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s _ => hδt s
  have hβ0 : β ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hβ
    exact mul_ne_zero (by exact_mod_cast hδt t) α.ne_zero hβ.symm
  have hx1 : (1 : ℝ) ≤ ((|Algebra.norm ℚ ((δt t : K) * (α : K))| : ℚ) : ℝ) := by
    rw [← hβ]
    exact one_le_abs_norm_of_ne_zero hβ0
  have hx0 : (0 : ℝ) ≤ ((|Algebra.norm ℚ ((δt t : K) * (α : K))| : ℚ) : ℝ) := zero_le_one.trans hx1
  have hr1 : (1 : ℝ) ≤ ((|Algebra.norm ℚ ((∏ s ∈ T.erase t, δt s : 𝓞 K) : K)| : ℚ) : ℝ) :=
    one_le_abs_norm_of_ne_zero hrest
  have hK : (((δt t * ∏ s ∈ T.erase t, δt s : 𝓞 K) : K) * (α : K))
      = ((∏ s ∈ T.erase t, δt s : 𝓞 K) : K) * ((δt t : K) * (α : K)) := by
    push_cast
    ring
  have hyq : |Algebra.norm ℚ (((∏ s ∈ T, δt s : 𝓞 K) : K) * (α : K))|
      = |Algebra.norm ℚ ((∏ s ∈ T.erase t, δt s : 𝓞 K) : K)| * |Algebra.norm ℚ ((δt t : K) * (α : K))| := by
    rw [← abs_mul, ← map_mul, hprod, hK]
  have hy : ((|Algebra.norm ℚ (((∏ s ∈ T, δt s : 𝓞 K) : K) * (α : K))| : ℚ) : ℝ)
      = ((|Algebra.norm ℚ ((∏ s ∈ T.erase t, δt s : 𝓞 K) : K)| : ℚ) : ℝ)
        * ((|Algebra.norm ℚ ((δt t : K) * (α : K))| : ℚ) : ℝ) := by
    rw [hyq, Rat.cast_mul]
  have hxy : ((|Algebra.norm ℚ ((δt t : K) * (α : K))| : ℚ) : ℝ)
      ≤ ((|Algebra.norm ℚ (((∏ s ∈ T, δt s : 𝓞 K) : K) * (α : K))| : ℚ) : ℝ) := by
    rw [hy]
    exact le_mul_of_one_le_left hx0 hr1
  have hβ' : (β : K) = (δt t : K) * (α : K) := hβ
  refine ⟨⟨(∏ s ∈ T.erase t, δt s) * β, ?_⟩, ?_⟩
  · rw [hprod]
    push_cast
    first
      | (rw [hβ']; ring1)
      | (simp only [hβ']; ring1)
      | (rw [hβ]; ring1)
      | (simp only [hβ]; ring1)
  · calc ‖dF.Wf (globalPoints (𝓞 K) K (diagOne α) * t)‖
        ≤ Ct t * ((|Algebra.norm ℚ ((δt t : K) * (α : K))| : ℚ) : ℝ) ^ κt t := hbound
      _ ≤ (∑ s ∈ T, |Ct s|) * ((|Algebra.norm ℚ ((δt t : K) * (α : K))| : ℚ) : ℝ) ^ κt t :=
          mul_le_mul_of_nonneg_right
            ((le_abs_self (Ct t)).trans (Finset.single_le_sum (fun s _ => abs_nonneg (Ct s)) ht))
            (Real.rpow_nonneg hx0 _)
      _ ≤ (∑ s ∈ T, |Ct s|)
            * ((|Algebra.norm ℚ (((∏ s ∈ T, δt s : 𝓞 K) : K) * (α : K))| : ℚ) : ℝ) ^ ∑ s ∈ T, κt s := by
          refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun s _ => abs_nonneg (Ct s))
          exact (Real.rpow_le_rpow hx0 hxy (hκt t)).trans
            (Real.rpow_le_rpow_of_exponent_le (hx1.trans hxy) (Finset.single_le_sum (fun s _ => hκt s) ht))

end CosetCover

end LanglandsTunnell.Converse.CuspSynthesis
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.AdelicVolume
open scoped Classical
variable {K : Type} [Field K] [NumberField K]

section SiegelBound

private theorem norm_ringEquivReal (w : InfinitePlace K) (hw : w.IsReal) (z : w.Completion) :
    ‖ringEquivRealOfIsReal hw z‖ = ‖z‖ :=
  (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) z

private theorem norm_ringEquivComplex (w : InfinitePlace K) (hw : w.IsComplex) (z : w.Completion) :
    ‖ringEquivComplexOfIsComplex hw z‖ = ‖z‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) z

private theorem abs_yOf_realComponent (w : InfinitePlace K) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) :
    |ArchIwasawa.Real.yOf (realComponent w hw g)| = localHeight (archComponent K w (glArch (𝓞 K) K g)) := by
  rw [ArchIwasawa.Real.abs_yOf, ArchIwasawa.Real.rowNorm_sq, abs_det_realComponent, archDetNorm, localHeight,
      rowNormSq,
    realComponent_eq_map, Matrix.map_apply, Matrix.map_apply,
    ← sq_abs (ringEquivRealOfIsReal hw _), ← sq_abs (ringEquivRealOfIsReal hw _), ← Real.norm_eq_abs,
    ← Real.norm_eq_abs, norm_ringEquivReal, norm_ringEquivReal]

private theorem norm_yOf_complexComponent (w : InfinitePlace K) (hw : w.IsComplex) (g : AdelicGL2 (𝓞 K) K) :
    ‖ArchIwasawa.Complex.yOf (complexComponent w hw g)‖ = localHeight (archComponent K w (glArch (𝓞 K) K g)) := by
  rw [ArchIwasawa.Complex.norm_yOf, ArchIwasawa.Complex.rowNorm_sq, norm_det_complexComponent, archDetNorm,
      localHeight,
    rowNormSq, complexComponent_eq_map, Matrix.map_apply, Matrix.map_apply, norm_ringEquivComplex,
        norm_ringEquivComplex]

end SiegelBound

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

namespace ArchIwasawa

namespace Real

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.exists_profile_bound_on_exp (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (ψ : ℝ → ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (χ : ℝ → ℂ)
    (hunip : ∀ (x : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), W (!![1, x; 0, 1] * g) = ψ x * W g)
    (hcent : ∀ (z : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), 0 < z → W (z • g) = χ z * W g)
    (σz : ℝ) (hzero : ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ →
      y ≠ 0 → |y| ≤ 1 → ‖W (!![y, 0; 0, 1] * k)‖ ≤ C * |y| ^ (-σz))
    (htop : ∀ N : ℕ, ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ →
      1 ≤ |y| → ‖W (!![y, 0; 0, 1] * k)‖ ≤ C * |y| ^ (-(N : ℝ)))
    (Sm : Set (Matrix (Fin 2) (Fin 2) ℝ)) (hdet : ∀ g ∈ Sm, g.det ≠ 0)
    (B p : ℝ) (hχB : ∀ g ∈ Sm, ‖χ (rowNorm g)‖ ≤ B * |yOf g| ^ p) :
    ∃ (C₀ : ℝ) (C₁ : ℕ → ℝ), ∀ g ∈ Sm, ∀ t : ℝ, t ≠ 0 →
      (|t| * |yOf g| ≤ 1 → ‖W (!![t, 0; 0, 1] * g)‖ ≤ C₀ * |yOf g| ^ p * (|t| * |yOf g|) ^ (-(max σz 0))) ∧
      (∀ N : ℕ, 1 ≤ |t| * |yOf g| → ‖W (!![t, 0; 0, 1] * g)‖ ≤ C₁ N * |yOf g| ^ p * (|t| * |yOf g|) ^ (-(N : ℝ))) := by
  obtain ⟨Cz, hz⟩ := hzero
  choose Ct ht using htop
  have hB' : ∀ g ∈ Sm, ‖χ (rowNorm g)‖ ≤ max B 0 * |yOf g| ^ p := fun g hg =>
    (hχB g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))
  have key : ∀ g ∈ Sm, ∀ t : ℝ,
      ‖W (!![t, 0; 0, 1] * g)‖ = ‖χ (rowNorm g)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := by
    intro g hg t
    rw [diagOne_mul_eq (hdet g hg) t, hunip, hcent _ _ (rowNorm_pos (hdet g hg)), norm_mul, norm_mul, hψ, one_mul]
  refine ⟨max B 0 * max Cz 0, fun N => max B 0 * max (Ct N) 0, ?_⟩
  intro g hg t ht0
  have hy0 : t * yOf g ≠ 0 := mul_ne_zero ht0 (yOf_ne_zero (hdet g hg))
  have hs : |t * yOf g| = |t| * |yOf g| := abs_mul t (yOf g)
  have hspos : 0 < |t| * |yOf g| := by rw [← hs]; exact abs_pos.mpr hy0
  have hk := kOf_mem (hdet g hg)
  constructor
  · intro hs1
    have h1 := hz (t * yOf g) (kOf g) hk hy0 (by rw [hs]; exact hs1)
    rw [hs] at h1
    calc ‖W (!![t, 0; 0, 1] * g)‖
        = ‖χ (rowNorm g)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := key g hg t
      _ ≤ max B 0 * |yOf g| ^ p * (max Cz 0 * (|t| * |yOf g|) ^ (-(max σz 0))) := by
          apply mul_le_mul (hB' g hg) _ (norm_nonneg _)
            (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _))
          calc ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ ≤ Cz * (|t| * |yOf g|) ^ (-σz) := h1
            _ ≤ max Cz 0 * (|t| * |yOf g|) ^ (-σz) := by
                gcongr; exact le_max_left _ _
            _ ≤ max Cz 0 * (|t| * |yOf g|) ^ (-(max σz 0)) :=
                mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg_max hspos hs1) (le_max_right _ _)
      _ = max B 0 * max Cz 0 * |yOf g| ^ p * (|t| * |yOf g|) ^ (-(max σz 0)) := by ring
  · intro N hs1
    have h1 := ht N (t * yOf g) (kOf g) hk (by rw [hs]; exact hs1)
    rw [hs] at h1
    calc ‖W (!![t, 0; 0, 1] * g)‖
        = ‖χ (rowNorm g)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := key g hg t
      _ ≤ max B 0 * |yOf g| ^ p * (max (Ct N) 0 * (|t| * |yOf g|) ^ (-(N : ℝ))) := by
          apply mul_le_mul (hB' g hg) _ (norm_nonneg _)
            (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _))
          calc ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ ≤ Ct N * (|t| * |yOf g|) ^ (-(N : ℝ)) := h1
            _ ≤ max (Ct N) 0 * (|t| * |yOf g|) ^ (-(N : ℝ)) := by
                gcongr; exact le_max_left _ _
      _ = max B 0 * max (Ct N) 0 * |yOf g| ^ p * (|t| * |yOf g|) ^ (-(N : ℝ)) := by ring

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "exists_profile_bound_on_exp"
end Real

namespace Complex

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.exists_profile_bound_on_exp (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (ψ : ℂ → ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (χ : ℂ → ℂ)
    (hunip : ∀ (x : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ), W (!![1, x; 0, 1] * g) = ψ x * W g)
    (hcent : ∀ (z : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ), z ≠ 0 → W (z • g) = χ z * W g)
    (σz : ℝ) (hzero : ∃ C : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), k ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      z ≠ 0 → ‖z‖ ≤ 1 → ‖W (!![z, 0; 0, 1] * k)‖ ≤ C * ‖z‖ ^ (-σz))
    (htop : ∀ N : ℕ, ∃ C : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), k ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      1 ≤ ‖z‖ → ‖W (!![z, 0; 0, 1] * k)‖ ≤ C * ‖z‖ ^ (-(N : ℝ)))
    (Sm : Set (Matrix (Fin 2) (Fin 2) ℂ)) (hdet : ∀ g ∈ Sm, g.det ≠ 0)
    (B p : ℝ) (hχB : ∀ g ∈ Sm, ‖χ ((rowNorm g : ℝ) : ℂ)‖ ≤ B * ‖yOf g‖ ^ p) :
    ∃ (C₀ : ℝ) (C₁ : ℕ → ℝ), ∀ g ∈ Sm, ∀ t : ℂ, t ≠ 0 →
      (‖t‖ * ‖yOf g‖ ≤ 1 → ‖W (!![t, 0; 0, 1] * g)‖ ≤ C₀ * ‖yOf g‖ ^ p * (‖t‖ * ‖yOf g‖) ^ (-(max σz 0))) ∧
      (∀ N : ℕ, 1 ≤ ‖t‖ * ‖yOf g‖ → ‖W (!![t, 0; 0, 1] * g)‖ ≤ C₁ N * ‖yOf g‖ ^ p * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ))) := by
  obtain ⟨Cz, hz⟩ := hzero
  choose Ct ht using htop
  have hB' : ∀ g ∈ Sm, ‖χ ((rowNorm g : ℝ) : ℂ)‖ ≤ max B 0 * ‖yOf g‖ ^ p := fun g hg =>
    (hχB g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  have key : ∀ g ∈ Sm, ∀ t : ℂ,
      ‖W (!![t, 0; 0, 1] * g)‖ = ‖χ ((rowNorm g : ℝ) : ℂ)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := by
    intro g hg t
    rw [diagOne_mul_eq (hdet g hg) t, hunip, hcent _ _ (Complex.ofReal_ne_zero.mpr (rowNorm_ne_zero (hdet g hg))),
      norm_mul, norm_mul, hψ, one_mul]
  refine ⟨max B 0 * max Cz 0, fun N => max B 0 * max (Ct N) 0, ?_⟩
  intro g hg t ht0
  have hy0 : t * yOf g ≠ 0 := mul_ne_zero ht0 (yOf_ne_zero (hdet g hg))
  have hs : ‖t * yOf g‖ = ‖t‖ * ‖yOf g‖ := norm_mul t (yOf g)
  have hspos : 0 < ‖t‖ * ‖yOf g‖ := by rw [← hs]; exact norm_pos_iff.mpr hy0
  have hk := kOf_mem (hdet g hg)
  constructor
  · intro hs1
    have h1 := hz (t * yOf g) (kOf g) hk hy0 (by rw [hs]; exact hs1)
    rw [hs] at h1
    calc ‖W (!![t, 0; 0, 1] * g)‖
        = ‖χ ((rowNorm g : ℝ) : ℂ)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := key g hg t
      _ ≤ max B 0 * ‖yOf g‖ ^ p * (max Cz 0 * (‖t‖ * ‖yOf g‖) ^ (-(max σz 0))) := by
          apply mul_le_mul (hB' g hg) _ (norm_nonneg _)
            (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _))
          calc ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ ≤ Cz * (‖t‖ * ‖yOf g‖) ^ (-σz) := h1
            _ ≤ max Cz 0 * (‖t‖ * ‖yOf g‖) ^ (-σz) := by
                gcongr; exact le_max_left _ _
            _ ≤ max Cz 0 * (‖t‖ * ‖yOf g‖) ^ (-(max σz 0)) :=
                mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg_max hspos hs1) (le_max_right _ _)
      _ = max B 0 * max Cz 0 * ‖yOf g‖ ^ p * (‖t‖ * ‖yOf g‖) ^ (-(max σz 0)) := by ring
  · intro N hs1
    have h1 := ht N (t * yOf g) (kOf g) hk (by rw [hs]; exact hs1)
    rw [hs] at h1
    calc ‖W (!![t, 0; 0, 1] * g)‖
        = ‖χ ((rowNorm g : ℝ) : ℂ)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := key g hg t
      _ ≤ max B 0 * ‖yOf g‖ ^ p * (max (Ct N) 0 * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ))) := by
          apply mul_le_mul (hB' g hg) _ (norm_nonneg _)
            (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _))
          calc ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ ≤ Ct N * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ)) := h1
            _ ≤ max (Ct N) 0 * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ)) := by
                gcongr; exact le_max_left _ _
      _ = max B 0 * max (Ct N) 0 * ‖yOf g‖ ^ p * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ)) := by ring

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "exists_profile_bound_on_exp"
end Complex

end ArchIwasawa

namespace ProfileArith

private theorem profile_le_common {x σ σtot : ℝ} (hx : 0 < x) (hσ : σ ≤ σtot) {n : ℕ} (hn : σtot - σ ≤ n) (M : ℕ) :
    x ^ (-σ) * (1 + x) ^ (-((M + n : ℕ) : ℝ)) ≤ x ^ (-σtot) * (1 + x) ^ (-(M : ℝ)) :=
  rpow_neg_mul_le_of_le hx hσ hn M

private theorem norm_prod_le_weighted {ι X J : Type*} [Fintype ι] (F : ι → X → J → ℂ) (x : ι → J → ℝ)
    (hx : ∀ i b, 0 < x i b) (Y : X → ι → ℝ) (hY : ∀ g i, 1 ≤ Y g i) (σ e : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (he : ∀ i, 0 ≤ e i) (D : Set X) (M : ℕ) (A : ι → ℝ)
    (h : ∀ i, ∀ g ∈ D, ∀ b, ‖F i g b‖
      ≤ A i * (x i b ^ (-σ i) * (1 + x i b) ^ (-((M + ⌈∑ j, σ j⌉₊ : ℕ) : ℝ))) * Y g i ^ e i) :
    ∀ g ∈ D, ∀ b, ‖∏ i, F i g b‖
      ≤ (∏ i, max (A i) 0) * (∏ i, x i b ^ (-(∑ j, σ j))) * (∏ i, (1 + x i b) ^ (-(M : ℝ)))
          * ∏ i, Y g i ^ (∑ j, e j) := by
  intro g hg b
  have hfactor : ∀ i, ‖F i g b‖
      ≤ max (A i) 0 * (x i b ^ (-(∑ j, σ j)) * (1 + x i b) ^ (-(M : ℝ))) * Y g i ^ (∑ j, e j) := by
    intro i
    have hσi : σ i ≤ ∑ j, σ j := Finset.single_le_sum (fun j _ => hσ j) (Finset.mem_univ i)
    have hgap : (∑ j, σ j) - σ i ≤ (⌈∑ j, σ j⌉₊ : ℝ) := by
      have := Nat.le_ceil (∑ j, σ j)
      linarith [hσ i]
    have hei : e i ≤ ∑ j, e j := Finset.single_le_sum (fun j _ => he j) (Finset.mem_univ i)
    have hY0 : 0 < Y g i := lt_of_lt_of_le one_pos (hY g i)
    have hprof0 : 0 ≤ x i b ^ (-σ i) * (1 + x i b) ^ (-((M + ⌈∑ j, σ j⌉₊ : ℕ) : ℝ)) :=
      mul_nonneg (Real.rpow_pos_of_pos (hx i b) _).le (Real.rpow_pos_of_pos (by linarith [hx i b]) _).le
    have hwe0 : 0 ≤ Y g i ^ e i := (Real.rpow_pos_of_pos hY0 _).le
    have hwE : Y g i ^ e i ≤ Y g i ^ (∑ j, e j) := Real.rpow_le_rpow_of_exponent_le (hY g i) hei
    have hcommon0 : 0 ≤ x i b ^ (-(∑ j, σ j)) * (1 + x i b) ^ (-(M : ℝ)) :=
      mul_nonneg (Real.rpow_pos_of_pos (hx i b) _).le (Real.rpow_pos_of_pos (by linarith [hx i b]) _).le
    calc ‖F i g b‖
        ≤ A i * (x i b ^ (-σ i) * (1 + x i b) ^ (-((M + ⌈∑ j, σ j⌉₊ : ℕ) : ℝ))) * Y g i ^ e i := h i g hg b
      _ ≤ max (A i) 0 * (x i b ^ (-(∑ j, σ j)) * (1 + x i b) ^ (-(M : ℝ))) * Y g i ^ (∑ j, e j) := by
          apply mul_le_mul _ hwE hwe0 (mul_nonneg (le_max_right _ _) hcommon0)
          exact mul_le_mul (le_max_left _ _) (profile_le_common (hx i b) hσi hgap M) hprof0 (le_max_right _ _)
  calc ‖∏ i, F i g b‖ = ∏ i, ‖F i g b‖ := norm_prod _ _
    _ ≤ ∏ i, max (A i) 0 * (x i b ^ (-(∑ j, σ j)) * (1 + x i b) ^ (-(M : ℝ))) * Y g i ^ (∑ j, e j) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hfactor i)
    _ = (∏ i, max (A i) 0) * (∏ i, x i b ^ (-(∑ j, σ j))) * (∏ i, (1 + x i b) ^ (-(M : ℝ)))
          * ∏ i, Y g i ^ (∑ j, e j) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        ring

end ProfileArith

end LanglandsTunnell.Converse

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

section WeightedProfile
open Matrix

namespace ArchDatumR
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumR" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumR.zero_bound_of_pair {P : RealArchParam} (D : ArchDatumR P) (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀)) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ → y ≠ 0 → |y| ≤ 1 →
      ‖D.W (!![y, 0; 0, 1] * k)‖ ≤ C * |y| ^ (-(c₀ - 1)) := by
  obtain ⟨C, h⟩ := ArchDatumR.norm_iteratedFDerivWithin_diagOne_le P D c₀ hc₀ 0
  refine ⟨C, fun y k hk hy hy1 => ?_⟩
  have h1 := (norm_asPi_zero D.W y k).symm.trans_le (h y k hk hy hy1)
  refine h1.trans_eq ?_
  congr 2
  push_cast
  ring

end ArchDatumR
p2m_export "LanglandsTunnell.Converse" "ArchDatumR.zero_bound_of_pair"
namespace ArchDatumC
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumC" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumC.zero_bound_of_pair {P : ComplexArchParam} (D : ArchDatumC P) (c₀ : ℝ)
    (hc₀ : ∀ k : ℤ, ∀ ν ∈ (P.twist 0 k).gammaC, -ν.re < c₀) :
    ∃ C : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), k ∈ Matrix.unitaryGroup (Fin 2) ℂ → z ≠ 0 → ‖z‖ ≤ 1 →
      ‖D.W (!![z, 0; 0, 1] * k)‖ ≤ C * ‖z‖ ^ (-(2 * (c₀ - 1))) := by
  obtain ⟨C, h⟩ := ArchDatumC.norm_iteratedFDerivWithin_diagOne_le P D c₀ hc₀ 0
  refine ⟨C, fun z k hk hz hz1 => ?_⟩
  have h1 := (norm_asPiC_zero D.W z k).symm.trans_le (h z k hk hz hz1)
  refine h1.trans_eq ?_
  congr 2
  push_cast
  ring

end ArchDatumC
p2m_export "LanglandsTunnell.Converse" "ArchDatumC.zero_bound_of_pair"
namespace ArchDatumR
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumR" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumR.exists_window_profile (P : RealArchParam) (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    {D₁ D₂ : ℝ} (hD₁ : 0 < D₁) :
    ∃ s : ℝ, 0 ≤ s ∧ ∀ M : ℕ, ∃ e : ℝ, 0 ≤ e ∧ ∀ (D : ArchDatumR P) (Sm : Set (Matrix (Fin 2) (Fin 2) ℝ)),
      (∀ g ∈ Sm, g.det ≠ 0) → (∀ g ∈ Sm, D₁ ≤ |g.det| ∧ |g.det| ≤ D₂) →
      ∃ A : ℝ, ∀ g ∈ Sm, ∀ y : ℝ, y ≠ 0 →
        ‖D.W (ArchR.diagOne y * g)‖
          ≤ A * (|ArchIwasawa.Real.yOf g| + |ArchIwasawa.Real.yOf g|⁻¹) ^ e
              * (|y| ^ (-s) * (1 + |y|) ^ (-(M : ℝ))) := by
  obtain ⟨Bχ, hBχ0, hBχ⟩ := ProfileArith.exists_rpow_le_mul_rpow_signed (D₂ := D₂) hD₁ (P.centralExponent.re + 1)
  refine ⟨max (max (c₀ - 1) 0) (-((P.centralExponent.re + 1) / 2)), le_max_of_le_left (le_max_right _ _),
    fun M => ?_⟩
  obtain ⟨e, he, habs⟩ := ProfileArith.exists_exponent_profile_of_two_regime
    (σ := max (c₀ - 1) 0) (p := -((P.centralExponent.re + 1) / 2)) (le_max_right _ _) M
  refine ⟨e, he, fun D Sm hdet hwin => ?_⟩
  have hχB : ∀ g ∈ Sm,
      ‖ArchR.centralChar P (ArchIwasawa.Real.rowNorm g) * ((|ArchIwasawa.Real.rowNorm g| : ℝ) : ℂ)‖
        ≤ Bχ * |ArchIwasawa.Real.yOf g| ^ (-((P.centralExponent.re + 1) / 2)) := by
    intro g hg
    have hr := ArchIwasawa.Real.rowNorm_pos (hdet g hg)
    have hy : 0 < |ArchIwasawa.Real.yOf g| := abs_pos.mpr (ArchIwasawa.Real.yOf_ne_zero (hdet g hg))
    rw [norm_centralChar_mul hr, ← Real.rpow_add_one hr.ne']
    refine hBχ _ _ _ hr (hwin g hg).1 (hwin g hg).2 hy ?_
    have hd : |g.det| ≠ 0 := abs_ne_zero.mpr (hdet g hg)
    rw [ArchIwasawa.Real.abs_yOf, div_div_eq_mul_div, mul_div_cancel_left₀ _ hd]
  obtain ⟨C₀, C₁, hreg⟩ := ArchIwasawa.Real.exists_profile_bound_on_exp D.W ArchR.psi norm_psi
    (fun z => ArchR.centralChar P z * ((|z| : ℝ) : ℂ)) D.unip_law (fun z g hz => D.central_law z g hz.ne')
    (c₀ - 1) (D.zero_bound_of_pair c₀ hc₀) D.top_bound Sm hdet Bχ (-((P.centralExponent.re + 1) / 2)) hχB
  obtain ⟨A, hA⟩ := habs C₀ C₁
  refine ⟨A, fun g hg y hy => ?_⟩
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hY0 : 0 < |ArchIwasawa.Real.yOf g| := abs_pos.mpr (ArchIwasawa.Real.yOf_ne_zero (hdet g hg))
  obtain ⟨hlow, hhigh⟩ := hreg g hg y hy
  have h := hA ‖D.W (ArchR.diagOne y * g)‖ |y| |ArchIwasawa.Real.yOf g| hy0 hY0 hlow hhigh
  refine h.trans_eq ?_
  ring

end ArchDatumR
p2m_export "LanglandsTunnell.Converse" "ArchDatumR.exists_window_profile"
namespace ArchDatumC
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumC" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumC.exists_window_profile (P : ComplexArchParam) (c₀ : ℝ)
    (hc₀ : ∀ k : ℤ, ∀ ν ∈ (P.twist 0 k).gammaC, -ν.re < c₀) {D₁ D₂ : ℝ} (hD₁ : 0 < D₁) :
    ∃ s : ℝ, 0 ≤ s ∧ ∀ M : ℕ, ∃ e : ℝ, 0 ≤ e ∧ ∀ (D : ArchDatumC P) (Sm : Set (Matrix (Fin 2) (Fin 2) ℂ)),
      (∀ g ∈ Sm, g.det ≠ 0) → (∀ g ∈ Sm, D₁ ≤ ‖g.det‖ ∧ ‖g.det‖ ≤ D₂) →
      ∃ A : ℝ, ∀ g ∈ Sm, ∀ z : ℂ, z ≠ 0 →
        ‖D.W (ArchC.diagOne z * g)‖
          ≤ A * (‖ArchIwasawa.Complex.yOf g‖ + ‖ArchIwasawa.Complex.yOf g‖⁻¹) ^ e
              * (‖z‖ ^ (-s) * (1 + ‖z‖) ^ (-(M : ℝ))) := by
  obtain ⟨Bχ, hBχ0, hBχ⟩ :=
    ProfileArith.exists_rpow_le_mul_rpow_signed (D₂ := D₂) hD₁ ((2 * P.centralExponent).re + 2)
  refine ⟨max (max (2 * (c₀ - 1)) 0) (-(((2 * P.centralExponent).re + 2) / 2)),
    le_max_of_le_left (le_max_right _ _), fun M => ?_⟩
  obtain ⟨e, he, habs⟩ := ProfileArith.exists_exponent_profile_of_two_regime
    (σ := max (2 * (c₀ - 1)) 0) (p := -(((2 * P.centralExponent).re + 2) / 2)) (le_max_right _ _) M
  refine ⟨e, he, fun D Sm hdet hwin => ?_⟩
  have hχB : ∀ g ∈ Sm,
      ‖ArchC.centralChar P ((ArchIwasawa.Complex.rowNorm g : ℝ) : ℂ)
          * ((‖((ArchIwasawa.Complex.rowNorm g : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ)‖
        ≤ Bχ * ‖ArchIwasawa.Complex.yOf g‖ ^ (-(((2 * P.centralExponent).re + 2) / 2)) := by
    intro g hg
    have hr := ArchIwasawa.Complex.rowNorm_pos (hdet g hg)
    have hy : 0 < ‖ArchIwasawa.Complex.yOf g‖ := norm_pos_iff.mpr (ArchIwasawa.Complex.yOf_ne_zero (hdet g hg))
    rw [norm_centralCharC_mul hr, ← Real.rpow_two, ← Real.rpow_add hr]
    refine hBχ _ _ _ hr (hwin g hg).1 (hwin g hg).2 hy ?_
    have hd : ‖g.det‖ ≠ 0 := norm_ne_zero_iff.mpr (hdet g hg)
    rw [ArchIwasawa.Complex.norm_yOf, div_div_eq_mul_div, mul_div_cancel_left₀ _ hd]
  obtain ⟨C₀, C₁, hreg⟩ := ArchIwasawa.Complex.exists_profile_bound_on_exp D.W ArchC.psi norm_psiC
    (fun z => ArchC.centralChar P z * ((‖z‖ ^ 2 : ℝ) : ℂ)) D.unip_law D.central_law
    (2 * (c₀ - 1)) (D.zero_bound_of_pair c₀ hc₀) D.top_bound Sm hdet Bχ (-(((2 * P.centralExponent).re + 2) / 2)) hχB
  obtain ⟨A, hA⟩ := habs C₀ C₁
  refine ⟨A, fun g hg z hz => ?_⟩
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hY0 : 0 < ‖ArchIwasawa.Complex.yOf g‖ := norm_pos_iff.mpr (ArchIwasawa.Complex.yOf_ne_zero (hdet g hg))
  obtain ⟨hlow, hhigh⟩ := hreg g hg z hz
  have h := hA ‖D.W (ArchC.diagOne z * g)‖ ‖z‖ ‖ArchIwasawa.Complex.yOf g‖ hz0 hY0 hlow hhigh
  refine h.trans_eq ?_
  ring

end ArchDatumC
p2m_export "LanglandsTunnell.Converse" "ArchDatumC.exists_window_profile"
end WeightedProfile

end LanglandsTunnell.Converse

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

namespace RealArchParam
private theorem _root_.LanglandsTunnell.Converse.CuspSynthesis.RealArchParam.exists_forall_neg_re_lt (P : RealArchParam) :
    ∃ c₀ : ℝ, ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀) := by
  classical
  let bd : ZMod 2 → ℝ := fun a =>
    ((P.twist 0 a).gammaR.map fun μ : ℂ => |μ.re|).sum + ((P.twist 0 a).gammaC.map fun ν : ℂ => |ν.re|).sum
  have hmapR : ∀ a : ZMod 2, ∀ x ∈ (P.twist 0 a).gammaR.map fun μ : ℂ => |μ.re|, (0 : ℝ) ≤ x := by
    intro a x hx
    obtain ⟨μ, -, rfl⟩ := Multiset.mem_map.1 hx
    exact abs_nonneg _
  have hmapC : ∀ a : ZMod 2, ∀ x ∈ (P.twist 0 a).gammaC.map fun ν : ℂ => |ν.re|, (0 : ℝ) ≤ x := by
    intro a x hx
    obtain ⟨ν, -, rfl⟩ := Multiset.mem_map.1 hx
    exact abs_nonneg _
  have hbd : ∀ a, 0 ≤ bd a := fun a => add_nonneg (Multiset.sum_nonneg (hmapR a)) (Multiset.sum_nonneg (hmapC a))
  refine ⟨1 + ∑ b : ZMod 2, bd b, fun a => ?_⟩
  have hle : bd a ≤ ∑ b : ZMod 2, bd b := Finset.single_le_sum (f := bd) (fun b _ => hbd b) (Finset.mem_univ a)
  refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
  · have h1 : |μ.re| ≤ ((P.twist 0 a).gammaR.map fun μ : ℂ => |μ.re|).sum :=
      Multiset.single_le_sum (hmapR a) _ (Multiset.mem_map.2 ⟨μ, hμ, rfl⟩)
    have h2 : (0 : ℝ) ≤ ((P.twist 0 a).gammaC.map fun ν : ℂ => |ν.re|).sum := Multiset.sum_nonneg (hmapC a)
    have h3 : |μ.re| ≤ bd a := by simp only [bd]; linarith
    linarith [neg_le_abs μ.re]
  · have h1 : |ν.re| ≤ ((P.twist 0 a).gammaC.map fun ν : ℂ => |ν.re|).sum :=
      Multiset.single_le_sum (hmapC a) _ (Multiset.mem_map.2 ⟨ν, hν, rfl⟩)
    have h2 : (0 : ℝ) ≤ ((P.twist 0 a).gammaR.map fun μ : ℂ => |μ.re|).sum := Multiset.sum_nonneg (hmapR a)
    have h3 : |ν.re| ≤ bd a := by simp only [bd]; linarith
    linarith [neg_le_abs ν.re]

end RealArchParam
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "RealArchParam.exists_forall_neg_re_lt"
namespace ComplexArchParam
private theorem _root_.LanglandsTunnell.Converse.CuspSynthesis.ComplexArchParam.exists_forall_neg_re_lt (P : ComplexArchParam) :
    ∃ c₀ : ℝ, ∀ k : ℤ, ∀ ν ∈ (P.twist 0 k).gammaC, -ν.re < c₀ := by
  refine ⟨1 + |P.u₁.re| + |P.u₂.re|, fun k ν hν => ?_⟩
  simp only [ComplexArchParam.twist, ComplexArchParam.gammaC, add_zero, Multiset.insert_eq_cons,
    Multiset.mem_cons, Multiset.mem_singleton] at hν
  have hre : ∀ (u : ℂ) (n : ℕ), (u + (n : ℂ) / 2).re = u.re + (n : ℝ) / 2 := by
    intro u n
    simp
  rcases hν with rfl | rfl
  · rw [hre]
    linarith [neg_le_abs P.u₁.re, abs_nonneg P.u₂.re, (Nat.cast_nonneg (P.k₁ + k).natAbs : (0 : ℝ) ≤ _)]
  · rw [hre]
    linarith [neg_le_abs P.u₂.re, abs_nonneg P.u₁.re, (Nat.cast_nonneg (P.k₂ + k).natAbs : (0 : ℝ) ≤ _)]

end ComplexArchParam
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "ComplexArchParam.exists_forall_neg_re_lt"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

private theorem exists_finset_cover_of_glFin_mem_isCompact (D : Set (AdelicGL2 (𝓞 K) K))
    (Kc : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) (hKc : IsCompact Kc) (hD : ∀ g ∈ D, glFin (𝓞 K) K g ∈ Kc) :
    ∃ T : Finset (AdelicGL2 (𝓞 K) K), ∀ g ∈ D, ∃ t ∈ T, ∃ u ∈ levelOne (𝓞 K) K ⊤, g = t * u := by
  classical
  set U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :=
    (finiteLevelOne (𝓞 K) K ⊤ : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) with hU
  have hUo : IsOpen U := isOpen_finiteLevelOne (𝓞 K) K top_ne_bot
  obtain ⟨T₀, hT₀⟩ := hKc.elim_finite_subcover (fun y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (y * ·) '' U)
    (fun y => isOpenMap_mul_left y U hUo) (fun z _ => Set.mem_iUnion.mpr ⟨z, 1, one_mem _, mul_one z⟩)
  refine ⟨T₀.image (AdelicDock.finEmbed (𝓞 K) K), fun g hg => ?_⟩
  obtain ⟨y, hyT, k, hkU, hyk⟩ := Set.mem_iUnion₂.mp (hT₀ (hD g hg))
  refine ⟨AdelicDock.finEmbed (𝓞 K) K y, Finset.mem_image_of_mem _ hyT,
    (AdelicDock.finEmbed (𝓞 K) K y)⁻¹ * g, ?_, (mul_inv_cancel_left _ _).symm⟩
  rw [mem_levelOne_iff, map_mul, map_inv, AdelicDock.glFin_finEmbed, ← hyk, inv_mul_cancel_left]
  exact hkU

end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.AdelicVolume
open scoped Classical
variable {K : Type} [Field K] [NumberField K]

section WindowProfile

private noncomputable def archHt (w : InfinitePlace K) (q : AdelicGL2 (𝓞 K) K) : ℝ :=
  localHeight (archComponent K w (glArch (𝓞 K) K q))

private theorem archHt_pos (w : InfinitePlace K) (q : AdelicGL2 (𝓞 K) K) : 0 < archHt w q :=
  localHeight_pos _

private theorem one_le_archHt_add_inv (w : InfinitePlace K) (q : AdelicGL2 (𝓞 K) K) :
    1 ≤ archHt w q + (archHt w q)⁻¹ :=
  ProfileArith.one_le_add_inv (archHt_pos w q)

private theorem archWeight_nonneg (e : ℝ) (q : AdelicGL2 (𝓞 K) K) :
    0 ≤ ∏ w : InfinitePlace K, (archHt w q + (archHt w q)⁻¹) ^ e :=
  Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (by linarith [one_le_archHt_add_inv w q]) e).le

private theorem max_mul_le {A wt : ℝ} (hwt : 0 ≤ wt) : max (A * wt) 0 ≤ max A 0 * wt :=
  max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hwt) (mul_nonneg (le_max_right _ _) hwt)

private theorem exists_window_profile_archFactorAt (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam) (w : InfinitePlace K)
    (Q : Set (AdelicGL2 (𝓞 K) K)) {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hQ : ∀ q ∈ Q, archDetNorm w q ∈ Set.Icc d₁ d₂) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ N : ℕ, ∃ e : ℝ, 0 ≤ e ∧
      ∀ (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
        (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)),
        ∃ A : ℝ, ∀ q ∈ Q, ∀ α : Kˣ,
          ‖archFactorAt archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * q)‖
            ≤ A * ((w (α : K)) ^ (-σ) * (1 + w (α : K)) ^ (-(N : ℝ))) * (archHt w q + (archHt w q)⁻¹) ^ e := by
  by_cases hw : w.IsReal
  · obtain ⟨c₀, hc₀⟩ := RealArchParam.exists_forall_neg_re_lt (archR w hw)
    obtain ⟨s, hs, hprof⟩ := ArchDatumR.exists_window_profile (archR w hw) c₀ hc₀ (D₂ := d₂) hd₁
    refine ⟨s + 1 / 2, by linarith, fun N => ?_⟩
    obtain ⟨e, he, hset⟩ := hprof N
    refine ⟨e, he, fun dR dC => ?_⟩
    have hdet : ∀ m ∈ realComponent w hw '' Q, m.det ≠ 0 := by
      rintro _ ⟨q, -, rfl⟩; exact det_realComponent_ne_zero w hw q
    have hwin : ∀ m ∈ realComponent w hw '' Q, d₁ ≤ |m.det| ∧ |m.det| ≤ d₂ := by
      rintro _ ⟨q, hq, rfl⟩; rw [abs_det_realComponent]; exact ⟨(hQ q hq).1, (hQ q hq).2⟩
    obtain ⟨A, hA⟩ := hset (dR w hw) (realComponent w hw '' Q) hdet hwin
    refine ⟨max A 0 * (Real.sqrt d₁)⁻¹, fun q hq α => ?_⟩
    have hmem : realComponent w hw q ∈ realComponent w hw '' Q := ⟨q, hq, rfl⟩
    have hyw : |ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K))| = w (α : K) :=
      abs_ringEquivReal_algebraMap w hw (α : K)
    have hy0 : ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K)) ≠ 0 := by
      intro h
      have := hyw
      rw [h, abs_zero] at this
      exact (w.pos_iff.mpr (Units.ne_zero α)).ne this
    have hfac : archFactorAt archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * q)
        = (dR w hw).W (ArchR.diagOne (ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K)))
              * realComponent w hw q)
          * ((Real.sqrt |(ArchR.diagOne (ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K)))
              * realComponent w hw q).det| : ℝ) : ℂ)⁻¹ := by
      rw [archFactorAt, dif_pos hw, realComponent_globalPoints_diagOne_mul]
    have hB : (Real.sqrt |(realComponent w hw q).det|)⁻¹ ≤ (Real.sqrt d₁)⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr hd₁) (Real.sqrt_le_sqrt (hwin _ hmem).1)
    have hfb := real_factor_bound (dR w hw).W hy0 (hA _ hmem _ hy0) hB
    rw [abs_yOf_realComponent] at hfb
    have hwt0 : 0 ≤ (archHt w q + (archHt w q)⁻¹) ^ e := (Real.rpow_pos_of_pos (by
      linarith [one_le_archHt_add_inv w q]) e).le
    have hxα : 0 < w (α : K) := w.pos_iff.mpr (Units.ne_zero α)
    have hprof0 : 0 ≤ w (α : K) ^ (-(s + 1 / 2)) * (1 + w (α : K)) ^ (-(N : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg (hxα.le) _) (Real.rpow_nonneg (by linarith) _)
    rw [hfac, ← hyw]
    rw [← hyw] at hprof0
    calc _ ≤ _ := hfb
      _ ≤ max A 0 * (archHt w q + (archHt w q)⁻¹) ^ e * (Real.sqrt d₁)⁻¹
            * (|ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K))| ^ (-(s + 1 / 2))
              * (1 + |ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K))|) ^ (-(N : ℝ))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _)))
            hprof0
          exact max_mul_le hwt0
      _ = _ := by ring
  · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    obtain ⟨c₀, hc₀⟩ := ComplexArchParam.exists_forall_neg_re_lt (archC w hw')
    obtain ⟨s, hs, hprof⟩ := ArchDatumC.exists_window_profile (archC w hw') c₀ hc₀ (D₂ := d₂) hd₁
    refine ⟨s + 1, by linarith, fun N => ?_⟩
    obtain ⟨e, he, hset⟩ := hprof N
    refine ⟨e, he, fun dR dC => ?_⟩
    have hdet : ∀ m ∈ complexComponent w hw' '' Q, m.det ≠ 0 := by
      rintro _ ⟨q, -, rfl⟩; exact det_complexComponent_ne_zero w hw' q
    have hwin : ∀ m ∈ complexComponent w hw' '' Q, d₁ ≤ ‖m.det‖ ∧ ‖m.det‖ ≤ d₂ := by
      rintro _ ⟨q, hq, rfl⟩; rw [norm_det_complexComponent]; exact ⟨(hQ q hq).1, (hQ q hq).2⟩
    obtain ⟨A, hA⟩ := hset (dC w hw') (complexComponent w hw' '' Q) hdet hwin
    refine ⟨max A 0 * d₁⁻¹, fun q hq α => ?_⟩
    have hmem : complexComponent w hw' q ∈ complexComponent w hw' '' Q := ⟨q, hq, rfl⟩
    have hzw : ‖ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K))‖ = w (α : K) :=
      norm_ringEquivComplex_algebraMap w hw' (α : K)
    have hz0 : ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K)) ≠ 0 := by
      intro h
      have := hzw
      rw [h, norm_zero] at this
      exact (w.pos_iff.mpr (Units.ne_zero α)).ne this
    have hfac : archFactorAt archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * q)
        = (dC w hw').W (ArchC.diagOne (ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K)))
              * complexComponent w hw' q)
          * ((‖(ArchC.diagOne (ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K)))
              * complexComponent w hw' q).det‖ : ℝ) : ℂ)⁻¹ := by
      rw [archFactorAt, dif_neg hw, complexComponent_globalPoints_diagOne_mul]
    have hB : ‖(complexComponent w hw' q).det‖⁻¹ ≤ d₁⁻¹ := inv_anti₀ hd₁ (hwin _ hmem).1
    have hfb := complex_factor_bound (dC w hw').W hz0 (hA _ hmem _ hz0) hB
    rw [norm_yOf_complexComponent] at hfb
    have hwt0 : 0 ≤ (archHt w q + (archHt w q)⁻¹) ^ e := (Real.rpow_pos_of_pos (by
      linarith [one_le_archHt_add_inv w q]) e).le
    have hxα : 0 < w (α : K) := w.pos_iff.mpr (Units.ne_zero α)
    have hprof0 : 0 ≤ w (α : K) ^ (-(s + 1)) * (1 + w (α : K)) ^ (-(N : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg (hxα.le) _) (Real.rpow_nonneg (by linarith) _)
    rw [hfac, ← hzw]
    rw [← hzw] at hprof0
    calc _ ≤ _ := hfb
      _ ≤ max A 0 * (archHt w q + (archHt w q)⁻¹) ^ e * d₁⁻¹
            * (‖ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K))‖ ^ (-(s + 1))
              * (1 + ‖ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K))‖) ^ (-(N : ℝ))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hd₁.le)) hprof0
          exact max_mul_le hwt0
      _ = _ := by ring

private theorem exists_window_profile_archW' (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam) (Q : Set (AdelicGL2 (𝓞 K) K))
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hQ : ∀ q ∈ Q, ∀ w : InfinitePlace K, archDetNorm w q ∈ Set.Icc d₁ d₂) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ e : ℝ, 0 ≤ e ∧
      ∀ (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
        (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)),
        ∃ A : ℝ, ∀ q ∈ Q, ∀ α : Kˣ,
          ‖archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * q)‖
            ≤ A * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ)) * (∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ)))
                * ∏ w : InfinitePlace K, (archHt w q + (archHt w q)⁻¹) ^ e := by
  choose σ hσ hrest using fun w : InfinitePlace K =>
    exists_window_profile_archFactorAt archR archC w Q hd₁ (fun q hq => hQ q hq w)
  refine ⟨∑ w, σ w, Finset.sum_nonneg fun w _ => hσ w, fun M => ?_⟩
  choose e he hdata using fun w : InfinitePlace K => hrest w (M + ⌈∑ w, σ w⌉₊)
  refine ⟨∑ w, e w, Finset.sum_nonneg fun w _ => he w, fun dR dC => ?_⟩
  choose A hA using fun w : InfinitePlace K => hdata w dR dC
  refine ⟨∏ w, max (A w) 0, fun q hq α => ?_⟩
  have hx : ∀ (w : InfinitePlace K) (α : Kˣ), 0 < w (α : K) := fun w α => w.pos_iff.mpr (Units.ne_zero α)
  have h := ProfileArith.norm_prod_le_weighted
    (fun (w : InfinitePlace K) (q : AdelicGL2 (𝓞 K) K) (α : Kˣ) =>
      archFactorAt archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * q))
    (fun (w : InfinitePlace K) (α : Kˣ) => w (α : K)) hx
    (fun (q : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) => archHt w q + (archHt w q)⁻¹)
    (fun q w => one_le_archHt_add_inv w q) σ e hσ he Q M A (fun w q hq α => hA w q hq α) q hq α
  rw [archW'_eq_prod_archFactorAt]
  exact h

end WindowProfile

end LanglandsTunnell.Converse.CuspSynthesis

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
variable {K : Type} [Field K] [NumberField K]
open LanglandsTunnell.TateLocal NumberField.StandardAddChar
section UniformMajorant

private theorem exists_uniform_majorant_order_first {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    (dF : FinWhittakerDatum K S Pi) (coef : Kˣ → ℂ) (hcoef : ∃ Cb : ℝ, ∀ α, ‖coef α‖ ≤ Cb)
    (hfloor : ∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) → coef α = 0)
    (hgrow : ∃ κ : ℝ, ∀ v ∉ S,
      ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ)
    (h : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K) (D : Set (AdelicGL2 (𝓞 K) K))
    (hD : ∃ T : Finset (AdelicGL2 (𝓞 K) K), ∀ g ∈ D, ∃ t ∈ T, ∃ u ∈ levelOne (𝓞 K) K ⊤, h g = t * u)
    (σ : ℝ) (hσ : 0 ≤ σ) :
    ∃ M : ℕ, ∀ (eps : AdelicGL2 (𝓞 K) K → ℂ), (∀ g, ‖eps g‖ ≤ 1) →
      ∀ (X : AdelicGL2 (𝓞 K) K → Kˣ → ℂ) (Hw : AdelicGL2 (𝓞 K) K → ℝ), (∀ g ∈ D, 0 ≤ Hw g) →
      ∀ A : ℝ, (∀ g ∈ D, ∀ α : Kˣ, ‖X g α‖ ≤ A * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
        * (∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ))) * Hw g) →
      ∃ C : ℝ, ∀ g ∈ D,
        (Summable fun α : Kˣ => ‖coef α * eps g * X g α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖) ∧
        ∑' α : Kˣ, ‖coef α * eps g * X g α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ ≤ C * Hw g:= by
  classical
  obtain ⟨Cb, hCb⟩ := hcoef
  obtain ⟨δ, hδ, V, hV, C, κ, hκ, hY⟩ := exists_wf_bound_on_principal dF hgrow coef hfloor h D hD
  have hDV : D ⊆ V := Filter.mem_principal.1 hV
  obtain ⟨N₀, hN₀⟩ := exists_summable_archLatticeWeight δ hδ ⌈κ⌉₊
  obtain ⟨M, C₂, hC₂, habs⟩ := exists_le_archLatticeWeight δ hδ hκ hσ (Nat.le_ceil κ) N₀
  refine ⟨M, fun eps heps X Hw hH A hA => ?_⟩
  have hwt0 : ∀ α : Kˣ, 0 ≤ (integralAfter δ).indicator (fun α : Kˣ => archLatticeWeight ⌈κ⌉₊ N₀ (α : K)) α :=
    fun α => Set.indicator_nonneg (s := integralAfter δ) (f := fun β : Kˣ => archLatticeWeight ⌈κ⌉₊ N₀ (β : K))
      (fun β _ => archLatticeWeight_nonneg ⌈κ⌉₊ N₀ (β : K)) α
  set wt : Kˣ → ℝ := fun α => (integralAfter δ).indicator (fun α : Kˣ => archLatticeWeight ⌈κ⌉₊ N₀ (α : K)) α
    with hwt
  have hwts : Summable wt := hN₀ N₀ le_rfl
  set Dc : ℝ := max Cb 0 * max C 0 * max A 0 * C₂ with hDc
  have hDc0 : 0 ≤ Dc := by positivity
  refine ⟨Dc * ∑' α : Kˣ, wt α, fun g hg => ?_⟩
  have hHg : 0 ≤ Hw g := hH g hg
  have hterm : ∀ α : Kˣ,
      ‖coef α * eps g * X g α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ ≤ Dc * wt α * Hw g := by
    intro α
    by_cases h0 : coef α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g) = 0
    · have : coef α * eps g * X g α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g) = 0 := by
        rcases mul_eq_zero.1 h0 with h | h <;> simp [h]
      rw [this, norm_zero]
      exact mul_nonneg (mul_nonneg hDc0 (hwt0 α)) hHg
    obtain ⟨hmem, hYb⟩ := hY g (hDV hg) α h0
    have hwtα : wt α = archLatticeWeight ⌈κ⌉₊ N₀ (α : K) := by
      simp only [hwt, Set.indicator_of_mem hmem]
    have hαpos : ∀ w : InfinitePlace K, 0 < w (α : K) := fun w => InfinitePlace.pos_iff.mpr α.ne_zero
    have hn0 : (0 : ℝ) ≤ ((|Algebra.norm ℚ ((δ : K) * (α : K))| : ℚ) : ℝ) ^ κ := by positivity
    set P : ℝ := (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
      * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ)) with hP
    have hP0 : 0 ≤ P :=
      mul_nonneg (Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (hαpos w) _).le)
        (Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (by linarith [hαpos w]) _).le)
    have hXb : ‖X g α‖ ≤ max A 0 * P * Hw g := by
      refine (hA g hg α).trans ?_
      rw [hP, mul_assoc A]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hP0) hHg
    have hYb' : ‖dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖
        ≤ max C 0 * ((|Algebra.norm ℚ ((δ : K) * (α : K))| : ℚ) : ℝ) ^ κ :=
      hYb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0)
    have hcb : ‖coef α‖ ≤ max Cb 0 := (hCb α).trans (le_max_left _ _)
    rw [hwtα, hDc]
    calc ‖coef α * eps g * X g α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖
        = ‖coef α‖ * ‖eps g‖ * ‖X g α‖ * ‖dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ := by
          simp only [norm_mul]
      _ ≤ max Cb 0 * 1 * (max A 0 * P * Hw g) * (max C 0 * |Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ) := by
          gcongr
          exact heps g
      _ = max Cb 0 * max C 0 * max A 0
            * (|Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
              * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ))) * Hw g := by rw [hP]; ring
      _ ≤ max Cb 0 * max C 0 * max A 0 * (C₂ * archLatticeWeight ⌈κ⌉₊ N₀ (α : K)) * Hw g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (habs α hmem) (by positivity)) hHg
      _ = max Cb 0 * max C 0 * max A 0 * C₂ * archLatticeWeight ⌈κ⌉₊ N₀ (α : K) * Hw g := by ring
  have hbound : Summable fun α : Kˣ => Dc * wt α * Hw g := (hwts.mul_left Dc).mul_right (Hw g)
  have hsum : Summable fun α : Kˣ =>
      ‖coef α * eps g * X g α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ :=
    Summable.of_nonneg_of_le (fun α => norm_nonneg _) hterm hbound
  refine ⟨hsum, (hsum.tsum_le_tsum hterm hbound).trans (le_of_eq ?_)⟩
  rw [tsum_mul_right, tsum_mul_left]

end UniformMajorant
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section BadCellBound

open MeasureTheory Topology

variable {K : Type} [Field K] [NumberField K]

private noncomputable def hgt (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) : ℝ :=
  localHeight (archComponent K w (glArch (𝓞 K) K g))

private noncomputable def symmWeight (κ : ℝ) (g : AdelicGL2 (𝓞 K) K) : ℝ :=
  ∏ w : InfinitePlace K, (hgt w g + (hgt w g)⁻¹) ^ κ

private noncomputable def archUnip (v : mixedEmbedding.mixedSpace K) (t : ℝ) : AdelicGL2 (𝓞 K) K :=
  unipotentGL2 (R := AdeleRing (𝓞 K) K) ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0)

private noncomputable def sliceDeriv (F : AdelicGL2 (𝓞 K) K → ℂ) (v : mixedEmbedding.mixedSpace K) (j : ℕ)
    (h : AdelicGL2 (𝓞 K) K) : ℂ :=
  iteratedDeriv j (fun t : ℝ => F (archUnip v t * h)) 0

private theorem exists_pos_le_hgt_of_mem_window (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ g ∈ (pinsOf c u d₁ d₂ T).D, ∀ w : InfinitePlace K, ρ ≤ hgt w g := by
  classical
  choose Kb hKb using fun (x : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) =>
    cellHeights_exists_right (archComponent K w (glArch (𝓞 K) K x))
  have hKb_nn : ∀ x w, 0 ≤ Kb x w := fun x w => (hKb x w).1.le
  set B : ℝ := 1 + ∑ x ∈ T, ∑ w : InfinitePlace K, Kb x w with hB
  have hB_pos : 0 < B :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun w _ => hKb_nn x w)
  refine ⟨c / B, div_pos hc hB_pos, fun g hg w => ?_⟩
  change g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂ at hg
  simp only [Set.mem_iUnion, Set.mem_image] at hg
  obtain ⟨x, hxT, s, hs, rfl⟩ := hg
  obtain ⟨-, hsh, -, -⟩ := hs
  have hKb_le : Kb x w ≤ B := by
    have h1 : Kb x w ≤ ∑ w' : InfinitePlace K, Kb x w' :=
      Finset.single_le_sum (fun w' _ => hKb_nn x w') (Finset.mem_univ w)
    have h2 : ∑ w' : InfinitePlace K, Kb x w' ≤ ∑ x' ∈ T, ∑ w' : InfinitePlace K, Kb x' w' :=
      Finset.single_le_sum (f := fun x' => ∑ w' : InfinitePlace K, Kb x' w')
        (fun x' _ => Finset.sum_nonneg fun w' _ => hKb_nn x' w') hxT
    rw [hB]
    linarith
  have hmul : hgt w (s * x) =
      localHeight (archComponent K w (glArch (𝓞 K) K s) * archComponent K w (glArch (𝓞 K) K x)) := by
    simp only [hgt, map_mul]
  have h1 := ((hKb x w).2 (archComponent K w (glArch (𝓞 K) K s))).1
  have hpos := localHeight_pos (archComponent K w (glArch (𝓞 K) K s) * archComponent K w (glArch (𝓞 K) K x))
  rw [hmul, div_le_iff₀ hB_pos]
  calc c ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) := hsh w
    _ ≤ Kb x w * localHeight (archComponent K w (glArch (𝓞 K) K s) * archComponent K w (glArch (𝓞 K) K x)) := h1
    _ ≤ B * localHeight (archComponent K w (glArch (𝓞 K) K s) * archComponent K w (glArch (𝓞 K) K x)) :=
      mul_le_mul_of_nonneg_right hKb_le hpos.le
    _ = localHeight (archComponent K w (glArch (𝓞 K) K s) * archComponent K w (glArch (𝓞 K) K x)) * B :=
      mul_comm _ _

private theorem memLp_prod_hgt_rpow_of_nonpos (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c)
    (hd₁ : 0 < d₁) (Z : Set (AdelicGL2 (𝓞 K) K)) (e : ℝ) (he : e ≤ 0) :
    letI := (pinsOf c u d₁ d₂ T).mS
    MemLp (fun g : AdelicGL2 (𝓞 K) K => (∏ w : InfinitePlace K, hgt w g) ^ e) 2
      (((pinsOf c u d₁ d₂ T).μ).restrict ((pinsOf c u d₁ d₂ T).D \ Z)) := by
  letI := (pinsOf c u d₁ d₂ T).mS
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  have hfloor := exists_pos_le_hgt_of_mem_window c u d₁ d₂ T hc
  obtain ⟨ρ, hρ, hρle⟩ := hfloor
  have hprod_pos : ∀ g : AdelicGL2 (𝓞 K) K, 0 < ∏ w : InfinitePlace K, hgt w g := fun g =>
    Finset.prod_pos fun w _ => localHeight_pos _
  have hcont : Continuous fun g : AdelicGL2 (𝓞 K) K => (∏ w : InfinitePlace K, hgt w g) ^ e :=
    (continuous_finset_prod _ fun w _ => continuous_localHeight_place w).rpow_const fun g =>
      Or.inl (hprod_pos g).ne'
  haveI : IsFiniteMeasure (((pinsOf c u d₁ d₂ T).μ).restrict ((pinsOf c u d₁ d₂ T).D \ Z)) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply_univ]
    refine (MeasureTheory.measure_mono Set.diff_subset).trans_lt ?_
    change NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤
    refine (MeasureTheory.measure_biUnion_finset_le T _).trans_lt (ENNReal.sum_lt_top.2 fun x _ => ?_)
    exact adelicGLHaar_mul_right_centreCutSiegelSet_lt_top K hc u hd₁ d₂ x
  refine MeasureTheory.MemLp.of_bound hcont.aestronglyMeasurable ((ρ ^ Fintype.card (InfinitePlace K)) ^ e) ?_
  refine (MeasureTheory.ae_restrict_iff (measurableSet_le hcont.norm.measurable measurable_const)).2
    (Filter.Eventually.of_forall fun g hg => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (hprod_pos g).le _)]
  refine Real.rpow_le_rpow_of_nonpos (pow_pos hρ _) ?_ he
  calc ρ ^ Fintype.card (InfinitePlace K) = ∏ _w : InfinitePlace K, ρ := by
        rw [Finset.prod_const, Finset.card_univ]
    _ ≤ ∏ w : InfinitePlace K, hgt w g := Finset.prod_le_prod (fun _ _ => hρ.le) fun w _ => hρle g hg.1 w

private theorem symmWeight_le_mul_prod_hgt_rpow (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ A : ℝ, ∀ g ∈ (pinsOf c u d₁ d₂ T).D,
      symmWeight κ g ≤ A * (∏ w : InfinitePlace K, hgt w g) ^ κ := by
  obtain ⟨ρ, hρ, hρle⟩ := exists_pos_le_hgt_of_mem_window c u d₁ d₂ T hc
  refine ⟨((1 + ρ⁻¹ ^ 2) ^ κ) ^ Fintype.card (InfinitePlace K), fun g hg => ?_⟩
  have hpos : ∀ w : InfinitePlace K, 0 < hgt w g := fun w => localHeight_pos _
  have hle : ∀ w : InfinitePlace K, hgt w g + (hgt w g)⁻¹ ≤ (1 + ρ⁻¹ ^ 2) * hgt w g := by
    intro w
    have h1 : ρ ≤ hgt w g := hρle g hg w
    have h2 : (hgt w g)⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ h1
    have h3 : ρ⁻¹ ≤ ρ⁻¹ ^ 2 * hgt w g :=
      calc ρ⁻¹ = ρ⁻¹ ^ 2 * ρ := by rw [sq, mul_assoc, inv_mul_cancel₀ hρ.ne', mul_one]
        _ ≤ ρ⁻¹ ^ 2 * hgt w g := mul_le_mul_of_nonneg_left h1 (sq_nonneg ρ⁻¹)
    calc hgt w g + (hgt w g)⁻¹ ≤ hgt w g + ρ⁻¹ ^ 2 * hgt w g := by linarith [h2, h3]
      _ = (1 + ρ⁻¹ ^ 2) * hgt w g := by ring
  have hA : 0 ≤ 1 + ρ⁻¹ ^ 2 := by positivity
  calc symmWeight κ g = ∏ w : InfinitePlace K, (hgt w g + (hgt w g)⁻¹) ^ κ := rfl
    _ ≤ ∏ w : InfinitePlace K, ((1 + ρ⁻¹ ^ 2) * hgt w g) ^ κ := by
        refine Finset.prod_le_prod (fun w _ => Real.rpow_nonneg (add_pos (hpos w) (inv_pos.2 (hpos w))).le κ)
          fun w _ => ?_
        exact Real.rpow_le_rpow (add_pos (hpos w) (inv_pos.2 (hpos w))).le (hle w) hκ
    _ = ∏ w : InfinitePlace K, (1 + ρ⁻¹ ^ 2) ^ κ * hgt w g ^ κ :=
        Finset.prod_congr rfl fun w _ => Real.mul_rpow hA (hpos w).le
    _ = ((1 + ρ⁻¹ ^ 2) ^ κ) ^ Fintype.card (InfinitePlace K) * ∏ w : InfinitePlace K, hgt w g ^ κ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ = ((1 + ρ⁻¹ ^ 2) ^ κ) ^ Fintype.card (InfinitePlace K) * (∏ w : InfinitePlace K, hgt w g) ^ κ := by
        rw [Real.finsetProd_rpow Finset.univ (fun w : InfinitePlace K => hgt w g) (fun w _ => (hpos w).le) κ]

private theorem exists_norm_jlSeries'_le_mul_symmWeight {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Pi : HeckeEigensystem K ℂ} {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (Q : Set (AdelicGL2 (𝓞 K) K))
    (Kc : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) (hKc : IsCompact Kc) (hQ : ∀ q ∈ Q, glFin (𝓞 K) K q ∈ Kc)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁)
    (hdet : ∀ q ∈ Q, ∀ w : InfinitePlace K, NumberField.AdelicVolume.archDetNorm w q ∈ Set.Icc d₁ d₂) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
        (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)),
        ∃ C : ℝ, ∀ q ∈ Q, ‖jlSeries' d archR archC dR dC dF q‖ ≤ C * symmWeight κ q := by
  obtain ⟨σ, hσ, hprof⟩ := exists_window_profile_archW' archR archC Q hd₁ hdet
  obtain ⟨M, hM⟩ := exists_uniform_majorant_order_first dF d.a (d.bounded.imp fun _ h α => (h α).1)
    (fun α h => (d.floor α h).1) (exists_growth_exponent Pi S archR archC epsS ω hω hωb d hnice) id Q
    (by
      obtain ⟨T, hT⟩ := exists_finset_cover_of_glFin_mem_isCompact Q Kc hKc hQ
      exact ⟨T, fun g hg => hT g hg⟩)
    σ hσ
  obtain ⟨e, he, hdata⟩ := hprof M
  refine ⟨e, he, fun dR dC => ?_⟩
  obtain ⟨A, hA⟩ := hdata dR dC
  obtain ⟨C, hC⟩ := hM d.epsChar (norm_epsChar_le_one d hω)
    (fun g α => archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g))
    (fun g => ∏ w : InfinitePlace K, (archHt w g + (archHt w g)⁻¹) ^ e) (fun g _ => archWeight_nonneg e g) A
    (fun g hg α => hA g hg α)
  refine ⟨C, fun q hq => ?_⟩
  have hterm := hC q hq
  rw [jlSeries'_eq_tsum_seriesTerm]
  calc ‖∑' α : Kˣ, seriesTerm d archR archC dR dC dF q α‖
      ≤ ∑' α : Kˣ, ‖seriesTerm d archR archC dR dC dF q α‖ := norm_tsum_le_tsum_norm hterm.1
    _ ≤ C * symmWeight e q := hterm.2

end BadCellBound

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section WeightComparison

variable {K : Type} [Field K] [NumberField K]

private theorem prod_add_inv_rpow_le_of_pow_bounds {ι : Type*} [Fintype ι] {κ C : ℝ} (hκ : 0 ≤ κ) (hC : 0 < C) (k : ℕ)
    (x y : ι → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hup : ∀ i, x i ≤ C * y i ^ k)
    (hlow : ∀ i, (y i ^ k)⁻¹ / C ≤ x i) :
    ∏ i, (x i + (x i)⁻¹) ^ κ ≤ ((2 * C) ^ κ) ^ Fintype.card ι * ∏ i, (y i + (y i)⁻¹) ^ (κ * k) := by
  have hfac : ∀ i, (x i + (x i)⁻¹) ^ κ ≤ (2 * C) ^ κ * (y i + (y i)⁻¹) ^ (κ * k) := by
    intro i
    have hyk : 0 < y i ^ k := pow_pos (hy i) k
    have hb : 0 < (y i ^ k)⁻¹ / C := div_pos (inv_pos.mpr hyk) hC
    have hxinv : (x i)⁻¹ ≤ C * y i ^ k := by
      calc (x i)⁻¹ ≤ ((y i ^ k)⁻¹ / C)⁻¹ := inv_anti₀ hb (hlow i)
        _ = C * y i ^ k := by rw [inv_div, div_inv_eq_mul]
    have hB : 0 < y i + (y i)⁻¹ := add_pos (hy i) (inv_pos.mpr (hy i))
    have hyle : y i ^ k ≤ (y i + (y i)⁻¹) ^ k :=
      pow_le_pow_left₀ (hy i).le (le_add_of_nonneg_right (inv_pos.mpr (hy i)).le) k
    have hCy : C * y i ^ k ≤ C * (y i + (y i)⁻¹) ^ k := mul_le_mul_of_nonneg_left hyle hC.le
    have hsum : x i + (x i)⁻¹ ≤ 2 * C * (y i + (y i)⁻¹) ^ k := by linarith [hup i, hxinv, hCy]
    have hbase : 0 ≤ x i + (x i)⁻¹ := by have := hx i; positivity
    calc (x i + (x i)⁻¹) ^ κ ≤ (2 * C * (y i + (y i)⁻¹) ^ k) ^ κ := Real.rpow_le_rpow hbase hsum hκ
      _ = (2 * C) ^ κ * ((y i + (y i)⁻¹) ^ k) ^ κ := Real.mul_rpow (by positivity) (by positivity)
      _ = (2 * C) ^ κ * (y i + (y i)⁻¹) ^ (κ * k) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le, mul_comm (k : ℝ) κ]
  calc ∏ i, (x i + (x i)⁻¹) ^ κ ≤ ∏ i, ((2 * C) ^ κ * (y i + (y i)⁻¹) ^ (κ * k)) :=
        Finset.prod_le_prod (fun i _ => by have := hx i; positivity) (fun i _ => hfac i)
    _ = ((2 * C) ^ κ) ^ Fintype.card ι * ∏ i, (y i + (y i)⁻¹) ^ (κ * k) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

private theorem exists_symmWeight_le_of_hgt_bounds {κ C : ℝ} (hκ : 0 ≤ κ) (hC : 0 < C) (k : ℕ) :
    ∃ C' : ℝ, ∀ q h : AdelicGL2 (𝓞 K) K,
      (∀ w : InfinitePlace K, hgt w q ≤ C * hgt w h ^ k ∧ (hgt w h ^ k)⁻¹ / C ≤ hgt w q) →
        symmWeight κ q ≤ C' * symmWeight (κ * k) h := by
  refine ⟨((2 * C) ^ κ) ^ Fintype.card (InfinitePlace K), fun q h hqh => ?_⟩
  unfold symmWeight
  exact prod_add_inv_rpow_le_of_pow_bounds hκ hC k (fun w => hgt w q) (fun w => hgt w h)
    (fun w => localHeight_pos _) (fun w => localHeight_pos _) (fun w => (hqh w).1) (fun w => (hqh w).2)

end WeightComparison

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.FiniteWhittaker"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section ULevelBall

open scoped WithZero Classical

private theorem isLevelOneMatrix_of_forall_sub_mem_idealBall {N : Ideal (𝓞 K)}
    {M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hM : ∀ i j, (M - 1) i j ∈ idealBall (𝓞 K) K N) :
    IsLevelOneMatrix (𝓞 K) K N M := by
  rw [(add_sub_cancel 1 M).symm]
  exact
    { integral := fun i j => by
        rw [Matrix.add_apply, Matrix.one_apply]
        refine add_mem_integralFiniteAdeles ?_ (idealBall_subset_integralFiniteAdeles N (hM i j))
        split_ifs
        · exact one_mem_integralFiniteAdeles
        · exact zero_mem_integralFiniteAdeles
      lowerLeft := by
        rw [Matrix.add_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), zero_add]
        exact hM 1 0
      lowerRight := by
        rw [Matrix.add_apply, Matrix.one_apply_eq, add_sub_cancel_left]
        exact hM 1 1 }

private theorem theForm_mul_eq_of_forall_sub_mem_idealBall {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    {u : AdelicGL2 (𝓞 K) K} (hu : u ∈ finiteAdelicGL2Subgroup K)
    (hK : ∀ i j, ((glFin (𝓞 K) K u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈
      idealBall (𝓞 K) K (∏ v : ↥S, v.1.asIdeal ^ d.m v))
    (hK' : ∀ i j, ((((glFin (𝓞 K) K u)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K (∏ v : ↥S, v.1.asIdeal ^ d.m v))
    (g : AdelicGL2 (𝓞 K) K) :
    theForm d archR archC dR dC dF (g * u) = theForm d archR archC dR dC dF g := by
  classical
  have hN : (∏ v : ↥S, v.1.asIdeal ^ d.m v) ≠ ⊥ := by
    rw [Submodule.zero_eq_bot.symm, Finset.prod_ne_zero_iff]
    exact fun v _ => pow_ne_zero _ (by rw [Submodule.zero_eq_bot]; exact v.1.ne_bot)
  have hlev : u ∈ levelOne (𝓞 K) K (∏ v : ↥S, v.1.asIdeal ^ d.m v) :=
    mem_levelOne_iff.mpr (mem_finiteLevelOne_iff.mpr
      ⟨isLevelOneMatrix_of_forall_sub_mem_idealBall hK, isLevelOneMatrix_of_forall_sub_mem_idealBall hK'⟩)
  refine theForm_mul_eq_of_upperLeft d archR archC dR dC dF hinv (Subgroup.mem_inf.mpr ⟨hlev, hu⟩) (fun v => ?_) g
  have h0 := hK 0 0 v.1
  rw [Matrix.sub_apply, Matrix.one_apply_eq, coe_sub_apply, coe_one_apply] at h0
  exact h0.trans
    (idealBound_le_of_pow_dvd hN (Finset.dvd_prod_of_mem (fun w : ↥S => w.1.asIdeal ^ d.m w) (Finset.mem_univ v)))

end ULevelBall

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.FiniteWhittaker"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section TranslateChain

private theorem _root_.LanglandsTunnell.Converse.CuspSynthesis.one_le_add_inv {x : ℝ} (hx : 0 < x) : 1 ≤ x + x⁻¹ := by
  rcases le_or_gt 1 x with h | h
  · exact le_add_of_le_of_nonneg h (inv_nonneg.2 hx.le)
  · exact le_add_of_nonneg_of_le hx.le ((one_le_inv₀ hx).2 h.le)

p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "one_le_add_inv"
private theorem hgt_pos (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) : 0 < hgt w g := by
  unfold hgt
  exact localHeight_pos _

private theorem hgt_mul_of_mem (w : InfinitePlace K) {g k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ finiteAdelicGL2Subgroup K) : hgt w (g * k) = hgt w g := by
  unfold hgt
  rw [map_mul, show glArch (𝓞 K) K k = 1 from hk, mul_one]

private theorem symmWeight_mul_of_mem (κ : ℝ) {g k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ finiteAdelicGL2Subgroup K) : symmWeight κ (g * k) = symmWeight κ g := by
  unfold symmWeight
  simp only [hgt_mul_of_mem _ hk]

private theorem symmWeight_nonneg (κ : ℝ) (g : AdelicGL2 (𝓞 K) K) : 0 ≤ symmWeight κ g := by
  unfold symmWeight
  exact Finset.prod_nonneg fun w _ =>
    Real.rpow_nonneg (add_nonneg (hgt_pos w g).le (inv_nonneg.2 (hgt_pos w g).le)) κ

private theorem symmWeight_mono {κ₁ κ₂ : ℝ} (h : κ₁ ≤ κ₂) (g : AdelicGL2 (𝓞 K) K) :
    symmWeight κ₁ g ≤ symmWeight κ₂ g := by
  unfold symmWeight
  refine Finset.prod_le_prod (fun w _ => ?_) fun w _ => ?_
  · exact Real.rpow_nonneg (add_nonneg (hgt_pos w g).le (inv_nonneg.2 (hgt_pos w g).le)) κ₁
  · exact Real.rpow_le_rpow_of_exponent_le (one_le_add_inv (hgt_pos w g)) h

private theorem conj_mul_eq (a b x : AdelicGL2 (𝓞 K) K) :
    (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by
  simp only [mul_inv_rev, mul_assoc]

private theorem conj_unipotentGL2_fin_mem (g : AdelicGL2 (𝓞 K) K) (t : FiniteAdeleRing (𝓞 K) K) :
    g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
        (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g ∈
      finiteAdelicGL2Subgroup K := by
  rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_mul, map_inv, glArch_unipotentGL2]
  simp

private theorem mul_mem_pinsOf_image [DecidableEq (AdelicGL2 (𝓞 K) K)] {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 K) K)}
    {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ (pinsOf c u d₁ d₂ T).D) (k : AdelicGL2 (𝓞 K) K) :
    g * k ∈ (pinsOf c u d₁ d₂ (T.image (· * k))).D := by
  have hg' : g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂ := hg
  obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_iUnion₂.1 hg'
  show s * x * k ∈ ⋃ y ∈ T.image (· * k), (· * y) '' centreCutSiegelSet K c u d₁ d₂
  exact Set.mem_iUnion₂.2 ⟨x * k, Finset.mem_image_of_mem (· * k) hx, s, hs, (mul_assoc s x k).symm⟩

private theorem exists_chain_translateSum (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    {n : ℕ} (ks : Fin n → AdelicGL2 (𝓞 K) K) (cs : Fin n → ℂ) (hks : ∀ i, ks i ∈ finiteAdelicGL2Subgroup K)
    (Ts : Fin n → Finset (AdelicGL2 (𝓞 K) K))
    (hTs : ∀ i, ∀ g ∈ (pinsOf c u d₁ d₂ T).D, g * ks i ∈ (pinsOf c u d₁ d₂ (Ts i)).D)
    (N N₀ : Ideal (𝓞 K))
    (hchain : ∀ i : Fin n,
        ∃ κ : ℝ, 0 ≤ κ ∧ ∀ M : ℕ, ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧ ∀ g ∈ (pinsOf c u d₁ d₂ (Ts i)).D,
          ∀ v : mixedEmbedding.mixedSpace K,
            sliceDeriv (theForm d archR archC dR dC dF) v 0 = theForm d archR archC dR dC dF ∧
            (∀ j, Continuous (sliceDeriv (theForm d archR archC dR dC dF) v j)) ∧
            (∀ j (β : K) (h : AdelicGL2 (𝓞 K) K),
              sliceDeriv (theForm d archR archC dR dC dF) v j
                  (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) =
                sliceDeriv (theForm d archR archC dR dC dF) v j h) ∧
            (∀ j (h : AdelicGL2 (𝓞 K) K),
              HasDerivAt (fun t : ℝ => sliceDeriv (theForm d archR archC dR dC dF) v j (archUnip v t * h))
                (sliceDeriv (theForm d archR archC dR dC dF) v (j + 1) h) 0) ∧
            (∀ (y : InfiniteAdeleRing K) (t : FiniteAdeleRing (𝓞 K) K),
              g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
                  (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g ∈
                  levelOne (𝓞 K) K N₀ ⊓ finiteAdelicGL2Subgroup K →
              ‖sliceDeriv (theForm d archR archC dR dC dF) v M (unipotentGL2 (R := AdeleRing (𝓞 K) K)
                  (((y, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g)‖ ≤
                (Λ₀ * symmWeight κ g) *
                  (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g) ^ M))
    (hconj :
        ∀ (i : Fin n) (u : AdelicGL2 (𝓞 K) K), u ∈ finiteAdelicGL2Subgroup K →
          (∀ l m, ((glFin (𝓞 K) K u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) l m ∈
            idealBall (𝓞 K) K N) →
          (∀ l m, ((((glFin (𝓞 K) K u)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) l m ∈ idealBall (𝓞 K) K N) →
          (ks i)⁻¹ * u * ks i ∈ finiteAdelicGL2Subgroup K ∧
          (∀ l m, ((glFin (𝓞 K) K ((ks i)⁻¹ * u * ks i) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) l m ∈
            idealBall (𝓞 K) K N₀) ∧
          (∀ l m, ((((glFin (𝓞 K) K ((ks i)⁻¹ * u * ks i))⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) l m ∈ idealBall (𝓞 K) K N₀))
    :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ M : ℕ, ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧ ∀ g ∈ (pinsOf c u d₁ d₂ T).D,
      ∀ v : mixedEmbedding.mixedSpace K, ∃ xs : ℕ → AdelicGL2 (𝓞 K) K → ℂ,
        xs 0 = translateSum d archR archC dR dC dF ks cs ∧
        (∀ j, Continuous (xs j)) ∧
        (∀ j (β : K) (h : AdelicGL2 (𝓞 K) K),
          xs j (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) = xs j h) ∧
        (∀ j (h : AdelicGL2 (𝓞 K) K),
          HasDerivAt (fun t : ℝ => xs j (unipotentGL2 (R := AdeleRing (𝓞 K) K)
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0) * h)) (xs (j + 1) h) 0) ∧
        (∀ (y : InfiniteAdeleRing K) (t : FiniteAdeleRing (𝓞 K) K),
          (∀ i j, ((glFin (𝓞 K) K (g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
              (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g) :
                Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
          (∀ i j, ((((glFin (𝓞 K) K (g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
              (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g))⁻¹ :
                GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
                Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
          ‖xs M (unipotentGL2 (R := AdeleRing (𝓞 K) K)
              (((y, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g)‖ ≤
            (Λ₀ * symmWeight κ g) *
              (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g) ^ M) := by
  choose κs hκΛ using hchain
  refine ⟨∑ i, κs i, Finset.sum_nonneg fun i _ => (hκΛ i).1, fun M => ?_⟩
  choose Λs hΛ using fun i : Fin n => (hκΛ i).2 M
  refine ⟨∑ i, ‖cs i‖ * |Λs i|, Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (abs_nonneg _), ?_⟩
  intro g hg v
  have hi := fun i : Fin n => (hΛ i).2 (g * ks i) (hTs i g hg) v
  refine ⟨fun j h => ∑ i, cs i * sliceDeriv (theForm d archR archC dR dC dF) v j (h * ks i),
    ?_, ?_, ?_, ?_, ?_⟩
  · funext h
    unfold translateSum
    exact Finset.sum_congr rfl fun i _ => by rw [(hi i).1]
  · intro j
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul (((hi i).2.1 j).comp (continuous_id.mul continuous_const))
  · intro j β h
    exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, (hi i).2.2.1 j β (h * ks i)]
  · intro j h
    have hD : HasDerivAt
        (fun t : ℝ => ∑ i, cs i * sliceDeriv (theForm d archR archC dR dC dF) v j (archUnip v t * (h * ks i)))
        (∑ i, cs i * sliceDeriv (theForm d archR archC dR dC dF) v (j + 1) (h * ks i)) 0 :=
      HasDerivAt.fun_sum fun i _ => ((hi i).2.2.2.1 j (h * ks i)).const_mul (cs i)
    exact hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by simp only [archUnip, mul_assoc])
  · intro y t h₁ h₂
    have hB : 0 ≤ ∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g :=
      Finset.sum_nonneg fun w _ => div_nonneg (mixedEmbedding.normAtPlace_nonneg w v) (hgt_pos w g).le
    have hb : ∀ i : Fin n,
        ‖sliceDeriv (theForm d archR archC dR dC dF) v M (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            (((y, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g * ks i)‖ ≤
          (|Λs i| * symmWeight (∑ i, κs i) g) *
            (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g) ^ M := by
      intro i
      obtain ⟨hfin, hc₁, hc₂⟩ := hconj i _ (conj_unipotentGL2_fin_mem g t) h₁ h₂
      have hlev : (g * ks i)⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
          (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * (g * ks i) ∈
            levelOne (𝓞 K) K N₀ ⊓ finiteAdelicGL2Subgroup K := by
        rw [conj_mul_eq]
        exact Subgroup.mem_inf.mpr ⟨mem_levelOne_iff.mpr (mem_finiteLevelOne_iff.mpr
          ⟨isLevelOneMatrix_of_forall_sub_mem_idealBall hc₁, isLevelOneMatrix_of_forall_sub_mem_idealBall hc₂⟩),
          hfin⟩
      have h₀ := (hi i).2.2.2.2 y t hlev
      simp only [hgt_mul_of_mem _ (hks i), symmWeight_mul_of_mem _ (hks i)] at h₀
      rw [mul_assoc]
      refine h₀.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hB M))
      exact mul_le_mul (le_abs_self _)
        (symmWeight_mono (Finset.single_le_sum (fun j _ => (hκΛ j).1) (Finset.mem_univ i)) g)
        (symmWeight_nonneg _ _) (abs_nonneg _)
    calc ‖∑ i, cs i * sliceDeriv (theForm d archR archC dR dC dF) v M (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            (((y, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g * ks i)‖
        ≤ ∑ i, ‖cs i‖ * ‖sliceDeriv (theForm d archR archC dR dC dF) v M (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            (((y, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g * ks i)‖ :=
          (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _))
      _ ≤ ∑ i, ‖cs i‖ * ((|Λs i| * symmWeight (∑ i, κs i) g) *
            (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g) ^ M) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)
      _ = ((∑ i, ‖cs i‖ * |Λs i|) * symmWeight (∑ i, κs i) g) *
            (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g) ^ M := by
          simp only [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring

end TranslateChain

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section SliceDerivativeChain

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse"
open MeasureTheory Topology
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

private theorem archUnip_add (v : mixedEmbedding.mixedSpace K) (s t : ℝ) :
    archUnip v (s + t) = archUnip v s * archUnip v t := by
  unfold archUnip
  rw [← unipotentGL2_add]
  congr 1
  show ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm ((s + t) • v), (0 : FiniteAdeleRing (𝓞 K) K)) =
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (s • v), (0 : FiniteAdeleRing (𝓞 K) K)) +
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), (0 : FiniteAdeleRing (𝓞 K) K))
  rw [Prod.mk_add_mk, add_zero, add_smul, map_add]

private theorem iteratedDeriv_slice_translate {G : Type*} [Monoid G] (n : ℝ → G)
    (hn : ∀ s t : ℝ, n (s + t) = n s * n t) (F : G → ℂ) (j : ℕ) (t : ℝ) (h : G) :
    iteratedDeriv j (fun s : ℝ => F (n s * (n t * h))) 0 = iteratedDeriv j (fun s : ℝ => F (n s * h)) t := by
  have hfun : (fun s : ℝ => F (n s * (n t * h))) = fun s : ℝ => F (n (s + t) * h) := by
    funext s
    rw [hn, mul_assoc]
  rw [hfun, iteratedDeriv_comp_add_const (f := fun s : ℝ => F (n s * h)) (s := t)]
  simp

private theorem sliceDeriv_archUnip_mul (F : AdelicGL2 (𝓞 K) K → ℂ) (v : mixedEmbedding.mixedSpace K) (j : ℕ)
    (t : ℝ) (h : AdelicGL2 (𝓞 K) K) :
    sliceDeriv F v j (archUnip v t * h) = iteratedDeriv j (fun s : ℝ => F (archUnip v s * h)) t :=
  iteratedDeriv_slice_translate (archUnip v) (archUnip_add v) F j t h

private theorem archUnip_eq_unipotentInf (v : mixedEmbedding.mixedSpace K) (t : ℝ) :
    archUnip v t = unipotentInf (archOf (t • v)) := rfl

private theorem hgt_nonneg (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) : 0 ≤ hgt w g :=
  (localHeight_pos _).le

private theorem archUnip_zero (v : mixedEmbedding.mixedSpace K) : archUnip v 0 = 1 := by
  unfold archUnip
  rw [zero_smul, map_zero]
  exact unipotentGL2_zero

private theorem theForm_apply_eq_jlSeries'_of_invOn {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Pi : HeckeEigensystem K ℂ} {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (eR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (eC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) (dF : FinWhittakerDatum K S Pi)
    (heinv : InvOn (kZeroSet S d.m) (jlSeries' d archR archC eR eC dF)) {γ : GL (Fin 2) K}
    {h : AdelicGL2 (𝓞 K) K} (hγ : globalPoints (𝓞 K) K γ * h ∈ kZeroSet S d.m) (x : AdelicGL2 (𝓞 K) K)
    (hx : globalPoints (𝓞 K) K γ * h * x ∈ kZeroSet S d.m) :
    theForm d archR archC eR eC dF (h * x) = jlSeries' d archR archC eR eC dF (globalPoints (𝓞 K) K γ * h * x) := by
  rw [theForm_eq, ← extend_mul_left heinv γ, ← mul_assoc, extend_apply_of_mem heinv hx]

private theorem theForm_apply_eq_jlSeries'_globalPoints_mul {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Pi : HeckeEigensystem K ℂ} {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (eR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (eC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) (dF : FinWhittakerDatum K S Pi)
    (heinv : InvOn (kZeroSet S d.m) (jlSeries' d archR archC eR eC dF)) {γ : GL (Fin 2) K}
    {h : AdelicGL2 (𝓞 K) K} (hγ : globalPoints (𝓞 K) K γ * h ∈ kZeroSet S d.m) :
    theForm d archR archC eR eC dF h = jlSeries' d archR archC eR eC dF (globalPoints (𝓞 K) K γ * h) := by
  rw [theForm_eq, ← extend_mul_left heinv γ, extend_apply_of_mem heinv hγ]

private theorem sum_add_sum_eq_sub_ofReal_zero_mul {α₁ β₁ α₂ β₂ : Type} {s₁ : Finset α₁} {t₁ : Finset β₁}
    {s₂ : Finset α₂} {t₂ : Finset β₂} {a₁ f₁ g₁ : α₁ → β₁ → ℂ} {a₂ f₂ g₂ : α₂ → β₂ → ℂ} {r : ℝ} {z : ℂ}
    (h₁ : s₁.sum (fun w => t₁.sum fun ι => a₁ w ι * f₁ w ι) = s₁.sum fun w => t₁.sum fun ι => a₁ w ι * g₁ w ι)
    (h₂ : s₂.sum (fun w => t₂.sum fun ι => a₂ w ι * f₂ w ι) = s₂.sum fun w => t₂.sum fun ι => a₂ w ι * g₂ w ι)
    (hr : r = 0) :
    s₁.sum (fun w => t₁.sum fun ι => a₁ w ι * f₁ w ι) + s₂.sum (fun w => t₂.sum fun ι => a₂ w ι * f₂ w ι) =
      s₁.sum (fun w => t₁.sum fun ι => a₁ w ι * g₁ w ι) + s₂.sum (fun w => t₂.sum fun ι => a₂ w ι * g₂ w ι) -
        ((r : ℝ) : ℂ) * z := by
  rw [h₁, h₂, hr]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]

private theorem exists_families_hasDerivAt_theForm_archUnip_mul {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Pi : HeckeEigensystem K ℂ} {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam) (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (eR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (eC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (heinv : InvOn (kZeroSet S d.m) (jlSeries' d archR archC eR eC dF)) :
    ∃ (eR' : ∀ (w : InfinitePlace K), w.IsReal → Fin 2 × Fin 2 →
          ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), ArchDatumR (archR w' hw'))
      (eC' : ∀ (w : InfinitePlace K), w.IsComplex → (Fin 2 × Fin 2) × Fin 2 →
          ∀ (w' : InfinitePlace K) (hw' : w'.IsComplex), ArchDatumC (archC w' hw')),
      (∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2),
          InvOn (kZeroSet S d.m) (jlSeries' d archR archC (eR' w hw ι) eC dF)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2),
          InvOn (kZeroSet S d.m) (jlSeries' d archR archC eR (eC' w hw ι) dF)) ∧
      ∀ (v : mixedEmbedding.mixedSpace K) (h : AdelicGL2 (𝓞 K) K),
        HasDerivAt (fun t : ℝ => theForm d archR archC eR eC dF (archUnip v t * h))
          ((∑ w : {w : InfinitePlace K // w.IsReal}, ∑ ι : Fin 2 × Fin 2,
              ((sliceCoefR w.1 w.2 v h ι.1 ι.2 : ℝ) : ℂ) * theForm d archR archC (eR' w.1 w.2 ι) eC dF h) +
            ∑ w : {w : InfinitePlace K // w.IsComplex}, ∑ ι : (Fin 2 × Fin 2) × Fin 2,
              ((cplxCoeff (sliceCoefC w.1 w.2 v h) ι : ℝ) : ℂ) * theForm d archR archC eR (eC' w.1 w.2 ι) dF h) 0 := by
  have hRfam := exists_realFamilies_plain archR eR
  obtain ⟨eR', hR'off, hR'at⟩ := hRfam
  have hCfam := exists_complexFamilies archC eC
  obtain ⟨eC', hC'off, hC'at⟩ := hCfam
  have hinvR : ∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2),
      InvOn (kZeroSet S d.m) (jlSeries' d archR archC (eR' w hw ι) eC dF) := fun w hw ι =>
    invOn_jlSeries'_realFamilies hω hωb d archR archC eR eC dF heinv hnice eR' hR'off hR'at w hw ι
  have hinvC : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2),
      InvOn (kZeroSet S d.m) (jlSeries' d archR archC eR (eC' w hw ι) dF) := fun w hw ι =>
    invOn_jlSeries'_complexFamilies hω hωb d archR archC eR eC dF heinv hnice eC' hC'off hC'at w hw ι
  refine ⟨eR', eC', hinvR, hinvC, fun v h => ?_⟩
  have hmeets := kZeroSet_meets S d.m h
  obtain ⟨γ, hγ⟩ := hmeets
  set q : AdelicGL2 (𝓞 K) K := globalPoints (𝓞 K) K γ * h with hq
  have hqx : ∀ x : GL (Fin 2) (InfiniteAdeleRing K), q * AutomorphicForm.adelicArchGLIncl K x ∈ kZeroSet S d.m :=
    fun x => mem_kZeroSet_mul_adelicArchGLIncl S d.m hγ x
  have hfun : (fun t : ℝ => theForm d archR archC eR eC dF (archUnip v t * h)) =
      fun t : ℝ => jlSeries' d archR archC eR eC dF (q * AutomorphicForm.adelicArchGLIncl K (sliceCurve v h t)) := by
    funext t
    rw [archUnip_eq_unipotentInf, unipotentInf_mul_eq_mul_sliceCurve,
      theForm_apply_eq_jlSeries'_of_invOn d archR archC eR eC dF heinv hγ _ (hqx _)]
  have hDR : ∀ (w : InfinitePlace K) (hw : w.IsReal) (t : ℝ),
      HasDerivAt (fun s : ℝ => Matrix.of.symm (realComponent w hw
          (AutomorphicForm.adelicArchGLIncl K (sliceCurve v h s)))) (Matrix.of.symm (sliceCoefR w hw v h)) t := by
    intro w hw t
    simp only [realComponent_sliceCurve]
    exact (((hasDerivAt_id t).smul_const (Matrix.of.symm (sliceCoefR w hw v h))).const_add
      (Matrix.of.symm 1)).congr_deriv (one_smul ℝ _)
  have hDC : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (t : ℝ),
      HasDerivAt (fun s : ℝ => Matrix.of.symm (complexComponent w hw
          (AutomorphicForm.adelicArchGLIncl K (sliceCurve v h s)))) (Matrix.of.symm (sliceCoefC w hw v h)) t := by
    intro w hw t
    simp only [complexComponent_sliceCurve]
    exact (((hasDerivAt_id t).smul_const (Matrix.of.symm (sliceCoefC w hw v h))).const_add
      (Matrix.of.symm 1)).congr_deriv (one_smul ℝ _)
  have hmain := hasDerivAt_jlSeries'_mul_adelicArchGLIncl hω hωb d archR archC eR eC dF hnice eR' hR'off hR'at
    eC' hC'off hC'at (sliceCurve v h) (sliceCurve_zero v h) (continuous_adelicArchGLIncl_sliceCurve v h).continuousAt
    (fun w hw _ => sliceCoefR w hw v h) (fun w hw _ => sliceCoefC w hw v h) hDR hDC
    (fun _ _ => continuousAt_const) (fun _ _ => continuousAt_const) q
  rw [hfun]
  have hR : ∀ (w : InfinitePlace K) (hw : w.IsReal) (ι : Fin 2 × Fin 2),
      theForm d archR archC (eR' w hw ι) eC dF h = jlSeries' d archR archC (eR' w hw ι) eC dF q :=
    fun w hw ι => theForm_apply_eq_jlSeries'_globalPoints_mul d archR archC _ _ dF (hinvR w hw ι) hγ
  have hC : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (ι : (Fin 2 × Fin 2) × Fin 2),
      theForm d archR archC eR (eC' w hw ι) dF h = jlSeries' d archR archC eR (eC' w hw ι) dF q :=
    fun w hw ι => theForm_apply_eq_jlSeries'_globalPoints_mul d archR archC _ _ dF (hinvC w hw ι) hγ
  refine hmain.congr_deriv (Eq.symm (sum_add_sum_eq_sub_ofReal_zero_mul ?_ ?_ ?_))
  · exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun ι _ => by rw [hR w.1 w.2 ι]
  · exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun ι _ => by rw [hC w.1 w.2 ι]
  · simp only [trace_sliceCoefR, trace_sliceCoefC, Complex.zero_re, Finset.sum_const_zero, mul_zero, add_zero]

private theorem exists_family_sliceDeriv_theForm (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (j : ℕ) :
    ∃ (n : ℕ) (fR : Fin n → ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
        (fC : Fin n → ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)),
      (∀ k (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
          globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
          jlSeries' d archR archC (fR k) (fC k) dF (globalPoints (𝓞 K) K γ * g) =
            jlSeries' d archR archC (fR k) (fC k) dF g) ∧
      ∀ v : mixedEmbedding.mixedSpace K, ∃ cf : Fin n → AdelicGL2 (𝓞 K) K → ℂ,
        (∀ k, Continuous (cf k)) ∧
        (∀ k (β : K) (h : AdelicGL2 (𝓞 K) K),
            cf k (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) = cf k h) ∧
        (∀ k (t : ℝ) (h : AdelicGL2 (𝓞 K) K), cf k (archUnip v t * h) = cf k h) ∧
        (∀ k (h : AdelicGL2 (𝓞 K) K),
            ‖cf k h‖ ≤ (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w h) ^ j) ∧
        (∀ h : AdelicGL2 (𝓞 K) K,
            sliceDeriv (theForm d archR archC dR dC dF) v j h =
              ∑ k, cf k h * theForm d archR archC (fR k) (fC k) dF h) := by
  classical
  induction j with
  | zero =>
    refine ⟨1, fun _ => dR, fun _ => dC, fun _ => hinv, fun v => ⟨fun _ _ => 1, fun _ => continuous_const,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => by simp, fun h => ?_⟩⟩
    simp [sliceDeriv, iteratedDeriv_zero, archUnip_zero]
  | succ j ih =>
    obtain ⟨n, fR, fC, hfinv, hcf⟩ := ih
    have hfam := fun k : Fin n =>
      exists_families_hasDerivAt_theForm_archUnip_mul hω hωb d archR archC dF hnice (fR k) (fC k) (hfinv k)
    choose eR' eC' hinvR hinvC hder using hfam
    let Slot := {w : InfinitePlace K // w.IsReal} × (Fin 2 × Fin 2) ⊕
      {w : InfinitePlace K // w.IsComplex} × ((Fin 2 × Fin 2) × Fin 2)
    let e : Fin (Fintype.card (Fin n × Slot)) ≃ Fin n × Slot := (Fintype.equivFin (Fin n × Slot)).symm
    let gR : Fin n × Slot → ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw) := fun ks =>
      Sum.elim (fun p => eR' ks.1 p.1.1 p.1.2 p.2) (fun _ => fR ks.1) ks.2
    let gC : Fin n × Slot → ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw) := fun ks =>
      Sum.elim (fun _ => fC ks.1) (fun p => eC' ks.1 p.1.1 p.1.2 p.2) ks.2
    refine ⟨Fintype.card (Fin n × Slot), fun i => gR (e i), fun i => gC (e i), fun i => ?_, fun v => ?_⟩
    ·
      beta_reduce
      rcases he : e i with ⟨k, (p | p)⟩
      · exact hinvR k p.1.1 p.1.2 p.2
      · exact hinvC k p.1.1 p.1.2 p.2
    · obtain ⟨cf, hcf_cont, hcf_rat, hcf_slice, hcf_le, hexp⟩ := hcf v
      let entry : Slot → AdelicGL2 (𝓞 K) K → ℂ := fun s h =>
        Sum.elim (fun p : {w : InfinitePlace K // w.IsReal} × (Fin 2 × Fin 2) =>
            ((sliceCoefR p.1.1 p.1.2 v h p.2.1 p.2.2 : ℝ) : ℂ))
          (fun p : {w : InfinitePlace K // w.IsComplex} × ((Fin 2 × Fin 2) × Fin 2) =>
            ((cplxCoeff (sliceCoefC p.1.1 p.1.2 v h) p.2 : ℝ) : ℂ)) s
      have hentry_cont : ∀ s : Slot, Continuous (entry s) := by
        rintro (⟨w, ι⟩ | ⟨w, ι⟩)
        · exact Complex.continuous_ofReal.comp
            (((continuous_sliceCoefR w.1 w.2 v).matrix_elem ι.1 ι.2))
        · simp only [entry, Sum.elim_inr]
          unfold cplxCoeff
          split_ifs
          · exact Complex.continuous_ofReal.comp
              (Complex.continuous_re.comp ((continuous_sliceCoefC w.1 w.2 v).matrix_elem _ _))
          · exact Complex.continuous_ofReal.comp
              (Complex.continuous_im.comp ((continuous_sliceCoefC w.1 w.2 v).matrix_elem _ _))
      have hentry_unip : ∀ (s : Slot) (a : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K),
          entry s (unipotentGL2 a * h) = entry s h := by
        rintro (⟨w, ι⟩ | ⟨w, ι⟩) a h
        · simp only [entry, Sum.elim_inl, sliceCoefR_unipotentGL2_mul]
        · simp only [entry, Sum.elim_inr, sliceCoefC_unipotentGL2_mul]
      have hentry_le : ∀ (s : Slot) (h : AdelicGL2 (𝓞 K) K),
          ‖entry s h‖ ≤ ∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w h := by
        have hterm : ∀ (w : InfinitePlace K) (h : AdelicGL2 (𝓞 K) K),
            mixedEmbedding.normAtPlace w v / hgt w h ≤
              ∑ w' : InfinitePlace K, mixedEmbedding.normAtPlace w' v / hgt w' h :=
          fun w h => Finset.single_le_sum (f := fun w' => mixedEmbedding.normAtPlace w' v / hgt w' h)
            (fun w' _ => div_nonneg (mixedEmbedding.normAtPlace_nonneg _ _) (hgt_nonneg w' h)) (Finset.mem_univ w)
        rintro (⟨w, ι⟩ | ⟨w, ι⟩) h
        · simp only [entry, Sum.elim_inl, Complex.norm_real, Real.norm_eq_abs]
          exact (abs_sliceCoefR_apply_le w.1 w.2 v h ι.1 ι.2).trans (hterm w.1 h)
        · simp only [entry, Sum.elim_inr, Complex.norm_real, Real.norm_eq_abs]
          refine le_trans ?_ ((norm_sliceCoefC_apply_le w.1 w.2 v h ι.1.1 ι.1.2).trans (hterm w.1 h))
          unfold cplxCoeff
          split_ifs
          · exact Complex.abs_re_le_norm _
          · exact Complex.abs_im_le_norm _
      refine ⟨fun i h => cf (e i).1 h * entry (e i).2 h, fun i => ?_, fun i β h => ?_, fun i t h => ?_,
        fun i h => ?_, fun h => ?_⟩
      · exact (hcf_cont _).mul (hentry_cont _)
      · beta_reduce
        rw [hcf_rat, hentry_unip]
      · beta_reduce
        rw [hcf_slice]
        exact congrArg _ (hentry_unip _ _ h)
      · rw [norm_mul, pow_succ]
        exact mul_le_mul (hcf_le _ h) (hentry_le _ h) (norm_nonneg _) (pow_nonneg (Finset.sum_nonneg
          fun w _ => div_nonneg (mixedEmbedding.normAtPlace_nonneg _ _) (hgt_nonneg w h)) _)
      ·
        have hslice : (fun t : ℝ => sliceDeriv (theForm d archR archC dR dC dF) v j (archUnip v t * h)) =
            fun t : ℝ => ∑ k, cf k h * theForm d archR archC (fR k) (fC k) dF (archUnip v t * h) := by
          funext t
          rw [hexp]
          exact Finset.sum_congr rfl fun k _ => by rw [hcf_slice]
        have hd : HasDerivAt (fun t : ℝ => sliceDeriv (theForm d archR archC dR dC dF) v j (archUnip v t * h))
            (∑ k, cf k h * ((∑ w : {w : InfinitePlace K // w.IsReal}, ∑ ι : Fin 2 × Fin 2,
                ((sliceCoefR w.1 w.2 v h ι.1 ι.2 : ℝ) : ℂ) * theForm d archR archC (eR' k w.1 w.2 ι) (fC k) dF h) +
              ∑ w : {w : InfinitePlace K // w.IsComplex}, ∑ ι : (Fin 2 × Fin 2) × Fin 2,
                ((cplxCoeff (sliceCoefC w.1 w.2 v h) ι : ℝ) : ℂ) *
                  theForm d archR archC (fR k) (eC' k w.1 w.2 ι) dF h))
            0 := by
          rw [hslice]
          exact HasDerivAt.fun_sum fun k _ => (hder k v h).const_mul (cf k h)
        have hlhs : sliceDeriv (theForm d archR archC dR dC dF) v (j + 1) h =
            deriv (fun t : ℝ => sliceDeriv (theForm d archR archC dR dC dF) v j (archUnip v t * h)) 0 := by
          simp only [sliceDeriv, iteratedDeriv_succ]
          exact congrArg (fun F : ℝ → ℂ => deriv F 0)
            (funext fun t => (sliceDeriv_archUnip_mul (theForm d archR archC dR dC dF) v j t h).symm)
        rw [hlhs, hd.deriv]
        beta_reduce
        refine Eq.trans ?_ (e.sum_comp fun ks : Fin n × Slot =>
          cf ks.1 h * entry ks.2 h * theForm d archR archC (gR ks) (gC ks) dF h).symm
        simp only [Slot, entry, gR, gC, Fintype.sum_prod_type, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
          mul_add, Finset.mul_sum, mul_assoc]

private theorem sliceDeriv_succ (F : AdelicGL2 (𝓞 K) K → ℂ) (v : mixedEmbedding.mixedSpace K) (j : ℕ)
    (h : AdelicGL2 (𝓞 K) K) :
    sliceDeriv F v (j + 1) h = deriv (fun t : ℝ => sliceDeriv F v j (archUnip v t * h)) 0 := by
  have he : (fun t : ℝ => sliceDeriv F v j (archUnip v t * h)) =
      iteratedDeriv j (fun s : ℝ => F (archUnip v s * h)) :=
    funext fun t => sliceDeriv_archUnip_mul F v j t h
  rw [he]
  simp only [sliceDeriv, iteratedDeriv_succ]

private theorem continuous_theForm_of_invOn {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (eR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (eC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (heinv : InvOn (kZeroSet S d.m) (jlSeries' d archR archC eR eC dF)) :
    Continuous (theForm d archR archC eR eC dF) := by
  rw [theForm_eq]
  exact continuous_extend heinv (isOpen_kZeroSet S d.m)
    (exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice K Pi S archR archC epsS ω
      hω hωb d eR eC dF hnice).2.2.2.2.2.1

private theorem theForm_unipotentGL2_algebraMap_mul_of_invOn {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Pi : HeckeEigensystem K ℂ} {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (eR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (eC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) (dF : FinWhittakerDatum K S Pi)
    (heinv : InvOn (kZeroSet S d.m) (jlSeries' d archR archC eR eC dF)) (β : K) (h : AdelicGL2 (𝓞 K) K) :
    theForm d archR archC eR eC dF (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) =
      theForm d archR archC eR eC dF h := by
  rw [theForm_eq, ← globalPoints_unipotentGL2, extend_mul_left heinv]

private theorem chain_clauses_sliceDeriv_theForm (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (v : mixedEmbedding.mixedSpace K) :
    sliceDeriv (theForm d archR archC dR dC dF) v 0 = theForm d archR archC dR dC dF ∧
    (∀ j, Continuous (sliceDeriv (theForm d archR archC dR dC dF) v j)) ∧
    (∀ j (β : K) (h : AdelicGL2 (𝓞 K) K),
      sliceDeriv (theForm d archR archC dR dC dF) v j
          (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) =
        sliceDeriv (theForm d archR archC dR dC dF) v j h) ∧
    (∀ j (h : AdelicGL2 (𝓞 K) K),
      HasDerivAt (fun t : ℝ => sliceDeriv (theForm d archR archC dR dC dF) v j (archUnip v t * h))
        (sliceDeriv (theForm d archR archC dR dC dF) v (j + 1) h) 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext h
    simp [sliceDeriv, iteratedDeriv_zero, archUnip_zero]
  · intro j
    obtain ⟨n, fR, fC, hfinv, hcf⟩ :=
      exists_family_sliceDeriv_theForm c u d₁ d₂ T hc hd₁ hω hωb d archR archC dR dC dF hinv hnice j
    obtain ⟨cf, hcont, -, -, -, hexp⟩ := hcf v
    have hfun : sliceDeriv (theForm d archR archC dR dC dF) v j =
        fun h => ∑ k, cf k h * theForm d archR archC (fR k) (fC k) dF h := funext hexp
    rw [hfun]
    exact continuous_finset_sum _ fun k _ =>
      (hcont k).mul (continuous_theForm_of_invOn hω hωb d archR archC (fR k) (fC k) dF hnice (hfinv k))
  · intro j β h
    obtain ⟨n, fR, fC, hfinv, hcf⟩ :=
      exists_family_sliceDeriv_theForm c u d₁ d₂ T hc hd₁ hω hωb d archR archC dR dC dF hinv hnice j
    obtain ⟨cf, -, hrat, -, -, hexp⟩ := hcf v
    rw [hexp, hexp]
    exact Finset.sum_congr rfl fun k _ => by
      rw [hrat k β h, theForm_unipotentGL2_algebraMap_mul_of_invOn d archR archC (fR k) (fC k) dF (hfinv k)]
  · intro j h
    obtain ⟨n, fR, fC, hfinv, hcf⟩ :=
      exists_family_sliceDeriv_theForm c u d₁ d₂ T hc hd₁ hω hωb d archR archC dR dC dF hinv hnice j
    obtain ⟨cf, -, -, hslice, -, hexp⟩ := hcf v
    have hfam := fun k : Fin n =>
      exists_families_hasDerivAt_theForm_archUnip_mul hω hωb d archR archC dF hnice (fR k) (fC k) (hfinv k)
    choose eR' eC' hinvR hinvC hder using hfam
    have hfun : (fun t : ℝ => sliceDeriv (theForm d archR archC dR dC dF) v j (archUnip v t * h)) =
        fun t : ℝ => ∑ k, cf k h * theForm d archR archC (fR k) (fC k) dF (archUnip v t * h) := by
      funext t
      rw [hexp]
      exact Finset.sum_congr rfl fun k _ => by rw [hslice]
    have hd : HasDerivAt
        (fun t : ℝ => ∑ k, cf k h * theForm d archR archC (fR k) (fC k) dF (archUnip v t * h)) _ 0 :=
      HasDerivAt.fun_sum fun k _ => (hder k v h).const_mul (cf k h)
    rw [← hfun] at hd
    rw [sliceDeriv_succ (theForm d archR archC dR dC dF) v j h]
    exact hd.differentiableAt.hasDerivAt

end SliceDerivativeChain

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section UnipotentLeftInvariance

private theorem hgt_unipotentGL2_mul (w : InfinitePlace K) (a : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    hgt w (unipotentGL2 a * g) = hgt w g :=
  localHeight_archComponent_unipotentGL2_mul w a g

private theorem symmWeight_unipotentGL2_mul (κ : ℝ) (a : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    symmWeight κ (unipotentGL2 a * g) = symmWeight κ g := by
  simp only [symmWeight, hgt_unipotentGL2_mul]

end UnipotentLeftInvariance

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section ChainBound

open MeasureTheory Topology

private theorem exists_chain_sliceDeriv_theForm (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ M : ℕ, ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧ ∀ g ∈ (pinsOf c u d₁ d₂ T).D,
      ∀ v : mixedEmbedding.mixedSpace K,
        sliceDeriv (theForm d archR archC dR dC dF) v 0 = theForm d archR archC dR dC dF ∧
        (∀ j, Continuous (sliceDeriv (theForm d archR archC dR dC dF) v j)) ∧
        (∀ j (β : K) (h : AdelicGL2 (𝓞 K) K),
          sliceDeriv (theForm d archR archC dR dC dF) v j
              (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) =
            sliceDeriv (theForm d archR archC dR dC dF) v j h) ∧
        (∀ j (h : AdelicGL2 (𝓞 K) K),
          HasDerivAt (fun t : ℝ => sliceDeriv (theForm d archR archC dR dC dF) v j (archUnip v t * h))
            (sliceDeriv (theForm d archR archC dR dC dF) v (j + 1) h) 0) ∧
        (∀ (y : InfiniteAdeleRing K) (t : FiniteAdeleRing (𝓞 K) K),
          g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
              (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g ∈
              levelOne (𝓞 K) K (∏ v : ↥S, v.1.asIdeal ^ d.m v) ⊓ finiteAdelicGL2Subgroup K →
          ‖sliceDeriv (theForm d archR archC dR dC dF) v M (unipotentGL2 (R := AdeleRing (𝓞 K) K)
              (((y, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g)‖ ≤
            (Λ₀ * symmWeight κ g) *
              (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g) ^ M) := by
  classical
  have hNprod : (∏ v : ↥S, v.1.asIdeal ^ d.m v) ≠ ⊥ := by
    rw [Submodule.zero_eq_bot.symm, Finset.prod_ne_zero_iff]
    exact fun v _ => pow_ne_zero _ (by rw [Submodule.zero_eq_bot]; exact v.1.ne_bot)
  have hconj := exists_conjugation_ideal c u d₁ d₂ T (∏ v : ↥S, v.1.asIdeal ^ d.m v) hNprod
  obtain ⟨a, ha, hconj⟩ := hconj
  have hred := exists_bound_forall_exists_add_algebraMap_mul_norm_le a ha
  obtain ⟨R₀, hR₀⟩ := hred
  have hreps := exists_reps_of_window S d.m (u := |u| + R₀) (d₂ := d₂) hc hd₁ T
  obtain ⟨Rs, C, hC, k, Kc, hKc, d₁', d₂', hd₁', hrep, hbox⟩ := hreps
  have hU5 := exists_norm_jlSeries'_le_mul_symmWeight hω hωb d archR archC dF hnice
    {q | glFin (𝓞 K) K q ∈ Kc ∧
      ∀ w : InfinitePlace K, NumberField.AdelicVolume.archDetNorm w q ∈ Set.Icc d₁' d₂'}
    Kc hKc (fun _ hq => hq.1) d₁' d₂' hd₁' (fun _ hq => hq.2)
  obtain ⟨κ, hκ, hU5⟩ := hU5
  have hcmp := exists_symmWeight_le_of_hgt_bounds (K := K) hκ hC k
  obtain ⟨C', hC'⟩ := hcmp
  refine ⟨κ * k, mul_nonneg hκ (Nat.cast_nonneg k), fun M => ?_⟩
  have hfam := exists_family_sliceDeriv_theForm c u d₁ d₂ T hc hd₁ hω hωb d archR archC dR dC dF hinv hnice M
  obtain ⟨n, fR, fC, hfinv, hcf⟩ := hfam
  have hU5k := fun i : Fin n => hU5 (fR i) (fC i)
  choose Cs hCs using hU5k
  refine ⟨|C'| * ∑ i, |Cs i|, mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _), ?_⟩
  intro g hg v
  obtain ⟨cf, -, -, -, hcf_le, hexp⟩ := hcf v
  have hclauses := chain_clauses_sliceDeriv_theForm c u d₁ d₂ T hc hd₁ hω hωb d archR archC dR dC dF hinv hnice v
  obtain ⟨h0, hcont, hrat, hder⟩ := hclauses
  refine ⟨h0, hcont, hrat, hder, ?_⟩
  intro y t hguard
  obtain ⟨m, hm⟩ := hR₀ y
  obtain ⟨β, hβ⟩ : ∃ β : K, β = algebraMap (𝓞 K) K (a * m) := ⟨_, rfl⟩
  have hm' : ∀ w : InfinitePlace K, ‖(y + algebraMap K (InfiniteAdeleRing K) β) w‖ ≤ R₀ := by
    rw [hβ]
    exact hm
  obtain ⟨yA, hyA⟩ : ∃ x : InfiniteAdeleRing K, x = y + algebraMap K (InfiniteAdeleRing K) β := ⟨_, rfl⟩
  obtain ⟨tA, htA⟩ : ∃ x : FiniteAdeleRing (𝓞 K) K, x = t + algebraMap K (FiniteAdeleRing (𝓞 K) K) β := ⟨_, rfl⟩
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : AdelicGL2 (𝓞 K) K, q₁ = unipotentGL2 (R := AdeleRing (𝓞 K) K)
      (((yA, 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g := ⟨_, rfl⟩
  obtain ⟨uf, huf⟩ : ∃ uf : AdelicGL2 (𝓞 K) K, uf = unipotentGL2 (R := AdeleRing (𝓞 K) K)
      (((0, tA) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) := ⟨_, rfl⟩
  have hpoint : unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * (unipotentGL2 (R := AdeleRing (𝓞 K) K)
      (((y, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g) =
      unipotentGL2 (R := AdeleRing (𝓞 K) K)
        (((yA, 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * (uf * g) := by
    rw [huf, ← mul_assoc, ← mul_assoc, ← unipotentGL2_add, ← unipotentGL2_add]
    congr 2
    rw [hyA, htA]
    refine Prod.ext ?_ ?_
    · show algebraMap K (InfiniteAdeleRing K) β + y = y + algebraMap K (InfiniteAdeleRing K) β + 0
      rw [add_zero, add_comm]
    · show algebraMap K (FiniteAdeleRing (𝓞 K) K) β + t = 0 + (t + algebraMap K (FiniteAdeleRing (𝓞 K) K) β)
      rw [zero_add, add_comm]
  have hshift : sliceDeriv (theForm d archR archC dR dC dF) v M (unipotentGL2 (R := AdeleRing (𝓞 K) K)
      (((y, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g) =
      sliceDeriv (theForm d archR archC dR dC dF) v M (unipotentGL2 (R := AdeleRing (𝓞 K) K)
        (((yA, 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * (uf * g)) := by
    rw [← hpoint, hrat M β]
  have hβf : algebraMap K (FiniteAdeleRing (𝓞 K) K) β =
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a * (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) m * 1) := by
    rw [hβ, mul_one, ← map_mul, ← IsScalarTower.algebraMap_apply]
  have hβconj : g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
      (((0, algebraMap K (FiniteAdeleRing (𝓞 K) K) β) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :
        AdeleRing (𝓞 K) K) * g ∈
      levelOne (𝓞 K) K (∏ v : ↥S, v.1.asIdeal ^ d.m v) ⊓ finiteAdelicGL2Subgroup K := by
    have hr := (hconj g hg _ (algebraMap_mul_mem_integralFiniteAdeles m
      NumberField.AdelicLevel.one_mem_integralFiniteAdeles)).1
    rw [finShift_eq_pair] at hr
    rw [hβf]
    exact hr
  have hufsplit : uf = unipotentGL2 (R := AdeleRing (𝓞 K) K)
      (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) *
      unipotentGL2 (R := AdeleRing (𝓞 K) K)
        (((0, algebraMap K (FiniteAdeleRing (𝓞 K) K) β) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :
          AdeleRing (𝓞 K) K) := by
    rw [huf, ← unipotentGL2_add]
    congr 1
    refine Prod.ext ?_ ?_
    · show (0 : InfiniteAdeleRing K) = 0 + 0
      rw [add_zero]
    · exact htA
  have hlev : g⁻¹ * uf * g ∈
      levelOne (𝓞 K) K (∏ v : ↥S, v.1.asIdeal ^ d.m v) ⊓ finiteAdelicGL2Subgroup K := by
    have hprod : g⁻¹ * uf * g = (g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
        (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g) *
        (g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
          (((0, algebraMap K (FiniteAdeleRing (𝓞 K) K) β) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :
            AdeleRing (𝓞 K) K) * g) := by
      rw [hufsplit]
      simp only [mul_assoc, mul_inv_cancel_left]
    rw [hprod]
    exact mul_mem hguard hβconj
  have hdet : Matrix.GeneralLinearGroup.det (g⁻¹ * uf * g) = 1 := by
    rw [map_mul, map_mul, map_inv, huf, det_unipotentGL2', mul_one, inv_mul_cancel]
  have hq₀ : unipotentGL2 (R := AdeleRing (𝓞 K) K)
      (((yA, 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * (uf * g) =
      q₁ * (g⁻¹ * uf * g) := by
    rw [hq₁]
    simp only [mul_assoc, mul_inv_cancel_left]
  have hq₁D : q₁ ∈ (pinsOf c (|u| + R₀) d₁ d₂ T).D := by
    rw [hq₁, hyA]
    exact unipotentGL2_mul_mem_window_of_norm_le c u d₁ d₂ T hm' hg
  have hq₁rep := hrep q₁ hq₁D
  obtain ⟨γ, hγR, hγZ, hγht⟩ := hq₁rep
  have hγbox := hbox γ hγR q₁ hq₁D
  have hratio : (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w (q₁ * (g⁻¹ * uf * g))) =
      ∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g := by
    rw [← hq₀, huf]
    simp only [hgt_unipotentGL2_mul]
  have hratio_nonneg : 0 ≤ (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g) ^ M :=
    pow_nonneg (Finset.sum_nonneg fun w _ =>
      div_nonneg (mixedEmbedding.normAtPlace_nonneg _ _) (hgt_nonneg w g)) _
  have hsw : symmWeight κ (globalPoints (𝓞 K) K γ * q₁) ≤ |C'| * symmWeight (κ * k) g := by
    have h1 : symmWeight κ (globalPoints (𝓞 K) K γ * q₁) ≤ C' * symmWeight (κ * k) q₁ :=
      hC' _ _ (fun w => hγht w)
    have h2 : symmWeight (κ * k) q₁ = symmWeight (κ * k) g := by
      rw [hq₁, symmWeight_unipotentGL2_mul]
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C') (symmWeight_nonneg _ _))
  have hterm : ∀ i : Fin n,
      ‖theForm d archR archC (fR i) (fC i) dF (q₁ * (g⁻¹ * uf * g))‖ ≤ |Cs i| * (|C'| * symmWeight (κ * k) g) := by
    intro i
    rw [theForm_mul_eq_of_det_eq_one d archR archC (fR i) (fC i) dF (hfinv i) hlev hdet q₁,
      theForm_apply_eq_jlSeries'_globalPoints_mul d archR archC (fR i) (fC i) dF (hfinv i) hγZ]
    have hb := hCs i _ hγbox
    calc ‖jlSeries' d archR archC (fR i) (fC i) dF (globalPoints (𝓞 K) K γ * q₁)‖
        ≤ Cs i * symmWeight κ (globalPoints (𝓞 K) K γ * q₁) := hb
      _ ≤ |Cs i| * symmWeight κ (globalPoints (𝓞 K) K γ * q₁) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (symmWeight_nonneg _ _)
      _ ≤ |Cs i| * (|C'| * symmWeight (κ * k) g) := mul_le_mul_of_nonneg_left hsw (abs_nonneg _)
  rw [hshift, hq₀, hexp]
  calc ‖∑ i, cf i (q₁ * (g⁻¹ * uf * g)) * theForm d archR archC (fR i) (fC i) dF (q₁ * (g⁻¹ * uf * g))‖
      ≤ ∑ i, ‖cf i (q₁ * (g⁻¹ * uf * g)) * theForm d archR archC (fR i) (fC i) dF (q₁ * (g⁻¹ * uf * g))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, |Cs i| * ((|C'| * symmWeight (κ * k) g) *
          (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g) ^ M) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        have hc' := hcf_le i (q₁ * (g⁻¹ * uf * g))
        rw [hratio] at hc'
        calc ‖cf i (q₁ * (g⁻¹ * uf * g))‖ * ‖theForm d archR archC (fR i) (fC i) dF (q₁ * (g⁻¹ * uf * g))‖
            ≤ (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g) ^ M *
                (|Cs i| * (|C'| * symmWeight (κ * k) g)) :=
              mul_le_mul hc' (hterm i) (norm_nonneg _) hratio_nonneg
          _ = |Cs i| * ((|C'| * symmWeight (κ * k) g) *
                (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g) ^ M) := by ring
    _ = (|C'| * ∑ i, |Cs i|) * symmWeight (κ * k) g *
          (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / hgt w g) ^ M := by
        rw [← Finset.sum_mul]
        ring

end ChainBound

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.FiniteWhittaker"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

section TranslateLevel

open scoped WithZero Classical

private theorem algebraMap_mul_mem_integralFiniteAdeles_depth (a : 𝓞 K) {r : FiniteAdeleRing (𝓞 K) K}
    (hr : r ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a * r ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  intro v
  rw [NumberField.AdelicLevel.coe_mul_apply]
  exact mul_mem (NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers v a) (hr v)

private theorem exists_algebraMap_mul_mem_depth (y : FiniteAdeleRing (𝓞 K) K) :
    ∃ b : 𝓞 K, b ≠ 0 ∧
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b * y ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  obtain ⟨b, hb, hby⟩ := NumberField.AdelicBox.exists_mul_mem_integralFiniteAdeles (R := 𝓞 K) (K := K) y
  exact ⟨b, hb, fun v => hby v⟩

private theorem exists_algebraMap_mul_mem_of_finset_depth (F : Finset (FiniteAdeleRing (𝓞 K) K)) :
    ∃ b : 𝓞 K, b ≠ 0 ∧ ∀ y ∈ F,
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b * y ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun y hy => absurd hy (Finset.notMem_empty y)⟩
  | insert z F _ ih =>
    obtain ⟨b₁, hb₁, h₁⟩ := ih
    obtain ⟨b₂, hb₂, h₂⟩ := exists_algebraMap_mul_mem_depth (K := K) z
    refine ⟨b₁ * b₂, mul_ne_zero hb₁ hb₂, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hyF
    · rw [map_mul, mul_assoc]
      exact algebraMap_mul_mem_integralFiniteAdeles_depth b₁ h₂
    · rw [map_mul, mul_comm (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b₁), mul_assoc]
      exact algebraMap_mul_mem_integralFiniteAdeles_depth b₂ (h₁ y hyF)

private theorem idealBound_mul_depth {M N : Ideal (𝓞 K)} (hM : M ≠ ⊥) (hN : N ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.AdelicLevel.idealBound (𝓞 K) (M * N) v
      = NumberField.AdelicLevel.idealBound (𝓞 K) M v * NumberField.AdelicLevel.idealBound (𝓞 K) N v := by
  have hMN : M * N ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨hM, hN⟩
  rw [NumberField.AdelicLevel.idealBound_of_ne_bot hMN, NumberField.AdelicLevel.idealBound_of_ne_bot hM,
    NumberField.AdelicLevel.idealBound_of_ne_bot hN, ← WithZero.exp_add, ← Associates.mk_mul_mk,
    Associates.count_mul (Associates.mk_ne_zero.2 hM) (Associates.mk_ne_zero.2 hN)
      (HeightOneSpectrum.associates_irreducible v),
    Nat.cast_add, neg_add]

private theorem valued_algebraMap_eq_idealBound_depth {b : 𝓞 K} (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b) v)
      = NumberField.AdelicLevel.idealBound (𝓞 K) (Ideal.span {b}) v := by
  have h : Valued.v ((algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b) v) = v.intValuation b :=
    NumberField.AdelicLevel.valued_algebraMap v b
  rw [h, HeightOneSpectrum.intValuation_if_neg v hb,
    NumberField.AdelicLevel.idealBound_of_ne_bot (Ideal.span_singleton_eq_bot.not.2 hb)]

private theorem mul_mul_mem_idealBall_depth {N₀ : Ideal (𝓞 K)} (hN₀ : N₀ ≠ ⊥) {b : 𝓞 K} (hb : b ≠ 0)
    {x y z : FiniteAdeleRing (𝓞 K) K}
    (hx : algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b * x ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hy : y ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K (N₀ * Ideal.span {b} * Ideal.span {b}))
    (hz : algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b * z ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    x * y * z ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K N₀ := by
  intro v
  have hsb : Ideal.span {b} ≠ ⊥ := Ideal.span_singleton_eq_bot.not.2 hb
  have hMb : N₀ * Ideal.span {b} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨hN₀, hsb⟩
  have hβ := valued_algebraMap_eq_idealBound_depth (K := K) hb v
  have hxv := NumberField.AdelicLevel.valued_apply_le_one hx v
  rw [NumberField.AdelicLevel.coe_mul_apply, Valuation.map_mul] at hxv
  have hzv := NumberField.AdelicLevel.valued_apply_le_one hz v
  rw [NumberField.AdelicLevel.coe_mul_apply, Valuation.map_mul, mul_comm] at hzv
  have hyv := hy v
  rw [idealBound_mul_depth hMb hsb, idealBound_mul_depth hN₀ hsb, ← hβ] at hyv
  rw [NumberField.AdelicLevel.coe_mul_apply, NumberField.AdelicLevel.coe_mul_apply, Valuation.map_mul,
    Valuation.map_mul]
  calc Valued.v (x v) * Valued.v (y v) * Valued.v (z v)
      ≤ Valued.v (x v) * (NumberField.AdelicLevel.idealBound (𝓞 K) N₀ v
          * Valued.v ((algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b) v)
          * Valued.v ((algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b) v)) * Valued.v (z v) :=
        mul_le_mul' (mul_le_mul' le_rfl hyv) le_rfl
    _ = Valued.v ((algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b) v) * Valued.v (x v)
          * NumberField.AdelicLevel.idealBound (𝓞 K) N₀ v
          * (Valued.v (z v) * Valued.v ((algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b) v)) := by ac_rfl
    _ ≤ 1 * NumberField.AdelicLevel.idealBound (𝓞 K) N₀ v * 1 := mul_le_mul' (mul_le_mul' hxv le_rfl) hzv
    _ = NumberField.AdelicLevel.idealBound (𝓞 K) N₀ v := by rw [one_mul, mul_one]

private theorem conj_entry_mem_idealBall_depth {N₀ : Ideal (𝓞 K)} (hN₀ : N₀ ≠ ⊥) {b : 𝓞 K} (hb : b ≠ 0)
    {A M C : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hA : ∀ i j, algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b * A i j
      ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hM : ∀ i j, M i j ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K (N₀ * Ideal.span {b} * Ideal.span {b}))
    (hC : ∀ i j, algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b * C i j
      ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (i j : Fin 2) :
    (A * M * C) i j ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K N₀ := by
  have t : ∀ l m, A i l * M l m * C m j ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K N₀ :=
    fun l m => mul_mul_mem_idealBall_depth hN₀ hb (hA i l) (hM l m) (hC m j)
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Fin.sum_univ_two, add_mul, add_mul]
  exact NumberField.AdelicLevel.add_mem_idealBall
    (NumberField.AdelicLevel.add_mem_idealBall (t 0 0) (t 1 0))
    (NumberField.AdelicLevel.add_mem_idealBall (t 0 1) (t 1 1))

private theorem coe_conj_sub_one_depth (k u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    ((k⁻¹ * u * k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1
      = ((k⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
          * ((u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1)
          * (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, Units.val_mul, Units.val_mul]

private theorem exists_level_conj (N₀ : Ideal (𝓞 K)) (hN₀ : N₀ ≠ ⊥) {n : ℕ} (ks : Fin n → AdelicGL2 (𝓞 K) K) :
    ∃ N : Ideal (𝓞 K), N ≠ ⊥ ∧ N₀ ∣ N ∧
      ∀ (i : Fin n) (u : AdelicGL2 (𝓞 K) K), u ∈ finiteAdelicGL2Subgroup K →
        (∀ l m, ((glFin (𝓞 K) K u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) l m ∈
          idealBall (𝓞 K) K N) →
        (∀ l m, ((((glFin (𝓞 K) K u)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) l m ∈ idealBall (𝓞 K) K N) →
        (ks i)⁻¹ * u * ks i ∈ finiteAdelicGL2Subgroup K ∧
        (∀ l m, ((glFin (𝓞 K) K ((ks i)⁻¹ * u * ks i) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) l m ∈
          idealBall (𝓞 K) K N₀) ∧
        (∀ l m, ((((glFin (𝓞 K) K ((ks i)⁻¹ * u * ks i))⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) l m ∈ idealBall (𝓞 K) K N₀) := by
  classical
  obtain ⟨b, hb, hbF⟩ := exists_algebraMap_mul_mem_of_finset_depth (K := K)
    ((Finset.univ.image fun p : Fin n × Fin 2 × Fin 2 =>
        (glFin (𝓞 K) K (ks p.1) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) p.2.1 p.2.2) ∪
      (Finset.univ.image fun p : Fin n × Fin 2 × Fin 2 =>
        (((glFin (𝓞 K) K (ks p.1))⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) p.2.1 p.2.2))
  have hA : ∀ (i : Fin n) (l m : Fin 2),
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b
        * (glFin (𝓞 K) K (ks i) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) l m
          ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K :=
    fun i l m => hbF _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, l, m))))
  have hB : ∀ (i : Fin n) (l m : Fin 2),
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b
        * (((glFin (𝓞 K) K (ks i))⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) l m
            ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K :=
    fun i l m => hbF _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, l, m))))
  have hsb : Ideal.span {b} ≠ ⊥ := Ideal.span_singleton_eq_bot.not.2 hb
  have hN : N₀ * Ideal.span {b} * Ideal.span {b} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or, Ideal.mul_eq_bot, not_or]
    exact ⟨⟨hN₀, hsb⟩, hsb⟩
  refine ⟨N₀ * Ideal.span {b} * Ideal.span {b}, hN, ⟨Ideal.span {b} * Ideal.span {b}, mul_assoc _ _ _⟩,
    fun i u hu hK hK' => ?_⟩
  have hc : glFin (𝓞 K) K ((ks i)⁻¹ * u * ks i)
      = (glFin (𝓞 K) K (ks i))⁻¹ * glFin (𝓞 K) K u * glFin (𝓞 K) K (ks i) := by
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
  have hc' : (glFin (𝓞 K) K ((ks i)⁻¹ * u * ks i))⁻¹
      = (glFin (𝓞 K) K (ks i))⁻¹ * (glFin (𝓞 K) K u)⁻¹ * glFin (𝓞 K) K (ks i) := by
    rw [hc]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  refine ⟨?_, fun l m => ?_, fun l m => ?_⟩
  · rw [mem_finiteAdelicGL2Subgroup_iff] at hu ⊢
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, hu, mul_one, inv_mul_cancel]
  · rw [hc, coe_conj_sub_one_depth]
    exact conj_entry_mem_idealBall_depth hN₀ hb (hB i) hK (hA i) l m
  · rw [hc', coe_conj_sub_one_depth]
    exact conj_entry_mem_idealBall_depth hN₀ hb (hB i) hK' (hA i) l m

end TranslateLevel

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.FiniteWhittaker"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section CombinationPointBound

open scoped WithZero Classical

private theorem exists_norm_translateSum_le_mul_prod_hgt_rpow
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt ω v)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archR w hw).centralExponent ((archR w hw).centralSign.val : ℤ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archC w hw).centralExponent (archC w hw).centralTwist)
    (d : JLData K S epsS ω)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (hcont : Continuous (theForm d archR archC dR dC dF))
    {n : ℕ}
    (ks : Fin n → AdelicGL2 (𝓞 K) K) (cs : Fin n → ℂ) (hks : ∀ i, ks i ∈ finiteAdelicGL2Subgroup K)
    (hcusp : @IsCuspidalFn _ (pinsOf c u d₁ d₂ T).nS _ _ (pinsOf c u d₁ d₂ T).ν unipotentGL2
      (translateSum d archR archC dR dC dF ks cs)) :
    ∃ C e : ℝ, e ≤ 0 ∧ ∀ g ∈ (pinsOf c u d₁ d₂ T).D,
      ‖translateSum d archR archC dR dC dF ks cs g‖ ≤ C * (∏ w : InfinitePlace K, hgt w g) ^ e := by
  have _ := hωunr
  have _ := hωR
  have _ := hωC
  obtain ⟨N, hN, -, hconj⟩ := exists_level_conj (K := K) (∏ v : ↥S, v.1.asIdeal ^ d.m v)
    (Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.1.ne_bot) ks
  obtain ⟨κ, hκ, Hκ⟩ := exists_chain_translateSum c u d₁ d₂ T d archR archC dR dC dF ks cs hks
    (fun i => T.image (· * ks i)) (fun i g hg => mul_mem_pinsOf_image hg (ks i)) N
    (∏ v : ↥S, v.1.asIdeal ^ d.m v)
    (fun i => exists_chain_sliceDeriv_theForm c u d₁ d₂ (T.image (· * ks i)) hc hd₁ hω hωb d archR archC dR dC
      dF hinv hnice)
    hconj
  obtain ⟨ρ, hρ, hfloor⟩ := exists_pos_le_hgt_of_mem_window c u d₁ d₂ T hc
  obtain ⟨M, C, hC, H⟩ :=
    exists_forall_norm_le_mul_prod_rpow_neg_of_hasDerivAt_chains_of_constantTerm_eq_zero_of_mem_idealBall K c u
      d₁ d₂ T N hN ρ hρ (⌈κ⌉₊ * Module.finrank ℚ K)
  obtain ⟨Λ₀, hΛ₀, HΛ⟩ := Hκ M
  obtain ⟨A, hA⟩ := symmWeight_le_mul_prod_hgt_rpow c u d₁ d₂ T hc κ hκ
  have hcontF : Continuous (translateSum d archR archC dR dC dF ks cs) := by
    unfold translateSum
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (hcont.comp (continuous_mul_const (ks i)))
  have hR : 0 < ∏ w : InfinitePlace K, ρ ^ (w.mult - 1) := Finset.prod_pos fun w _ => pow_pos hρ _
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hexp : -((⌈κ⌉₊ * Module.finrank ℚ K : ℕ) : ℝ) / (Module.finrank ℚ K : ℝ) = -(⌈κ⌉₊ : ℝ) := by
    rw [Nat.cast_mul, neg_div, mul_div_assoc, div_self hn, mul_one]
  refine ⟨C * Λ₀ * max A 1 * (∏ w : InfinitePlace K, ρ ^ (w.mult - 1)) ^ (-(⌈κ⌉₊ : ℝ)), κ + -(⌈κ⌉₊ : ℝ),
    by linarith [Nat.le_ceil κ], fun g hg => ?_⟩
  have hb := H (translateSum d archR archC dR dC dF ks cs) hcontF
    (translateSum_globalPoints_mul d archR archC dR dC dF hinv ks cs)
    (fun h u' hu' hK hK' => by
      unfold translateSum
      refine Finset.sum_congr rfl fun i _ => ?_
      obtain ⟨hcf, hcK, hcK'⟩ := hconj i u' hu' hK hK'
      rw [show h * u' * ks i = h * ks i * ((ks i)⁻¹ * u' * ks i) by simp only [mul_assoc, mul_inv_cancel_left],
        theForm_mul_eq_of_forall_sub_mem_idealBall d archR archC dR dC dF hinv hcf hcK hcK' (h * ks i)])
    g hg (hcusp g) (fun w => hgt w g) (fun w => hfloor g hg w) (Λ₀ * symmWeight κ g) (HΛ g hg)
  rw [hexp] at hb
  have hP : 0 < ∏ w : InfinitePlace K, hgt w g := Finset.prod_pos fun w _ => localHeight_pos _
  have hPm : (∏ w : InfinitePlace K, hgt w g) * ∏ w : InfinitePlace K, ρ ^ (w.mult - 1) ≤
      ∏ w : InfinitePlace K, hgt w g ^ w.mult := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun w _ => mul_nonneg (localHeight_pos _).le (pow_nonneg hρ.le _)) fun w _ => ?_
    calc hgt w g * ρ ^ (w.mult - 1) ≤ hgt w g * hgt w g ^ (w.mult - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le (hfloor g hg w) _) (localHeight_pos _).le
      _ = hgt w g ^ w.mult := by
          rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr InfinitePlace.mult_ne_zero)]
  have hPm' : (∏ w : InfinitePlace K, hgt w g ^ w.mult) ^ (-(⌈κ⌉₊ : ℝ)) ≤
      (∏ w : InfinitePlace K, hgt w g) ^ (-(⌈κ⌉₊ : ℝ)) *
        (∏ w : InfinitePlace K, ρ ^ (w.mult - 1)) ^ (-(⌈κ⌉₊ : ℝ)) := by
    rw [← Real.mul_rpow hP.le hR.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hP hR) hPm (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hsW : symmWeight κ g ≤ max A 1 * (∏ w : InfinitePlace K, hgt w g) ^ κ :=
    (hA g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hP.le _))
  rw [Real.rpow_add hP]
  refine hb.trans ?_
  calc C * (Λ₀ * symmWeight κ g) * (∏ w : InfinitePlace K, hgt w g ^ w.mult) ^ (-(⌈κ⌉₊ : ℝ))
      ≤ C * (Λ₀ * (max A 1 * (∏ w : InfinitePlace K, hgt w g) ^ κ)) *
          ((∏ w : InfinitePlace K, hgt w g) ^ (-(⌈κ⌉₊ : ℝ)) *
            (∏ w : InfinitePlace K, ρ ^ (w.mult - 1)) ^ (-(⌈κ⌉₊ : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsW hΛ₀) hC.le) hPm'
          (Real.rpow_nonneg (Finset.prod_nonneg fun w _ => pow_nonneg (localHeight_pos _).le _) _)
          (mul_nonneg hC.le (mul_nonneg hΛ₀ (mul_nonneg (zero_le_one.trans (le_max_right A 1))
            (Real.rpow_nonneg hP.le _))))
    _ = C * Λ₀ * max A 1 * (∏ w : InfinitePlace K, ρ ^ (w.mult - 1)) ^ (-(⌈κ⌉₊ : ℝ)) *
          ((∏ w : InfinitePlace K, hgt w g) ^ κ * (∏ w : InfinitePlace K, hgt w g) ^ (-(⌈κ⌉₊ : ℝ))) := by
        ring

end CombinationPointBound

end LanglandsTunnell.Converse.CuspSynthesis

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR TateLocal.charExt TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam ComplexArchParam.gammaC ComplexArchParam.twist"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.unip ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.unip ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW localOf IsOneMod JLData IsJLNice IsAdmissibleTwist IsArchCompAt twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist ArchDatumC.exists_W_eq_fderivWithin_mul ArchDatumR.exists_W_eq_fderivWithin_mul ArchDatumC.norm_iteratedFDerivWithin_diagOne_le ArchDatumR.norm_iteratedFDerivWithin_diagOne_le"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet mem_kZeroSet_iff kZeroSet_meets archNormFactor archW' jlSeries' theForm pinsOf theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

namespace SquareIntegrableTranslates

open MeasureTheory NumberField.AdelicHaar

variable {K : Type} [Field K] [NumberField K]

private theorem measurableSet_window (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    @MeasurableSet _ (pinsOf c u d₁ d₂ T).mS (pinsOf c u d₁ d₂ T).D := by
  letI := (pinsOf c u d₁ d₂ T).mS
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  change MeasurableSet (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
  refine Finset.measurableSet_biUnion T fun x _ => ?_
  have himg : (· * x) '' centreCutSiegelSet K c u d₁ d₂ =
      (· * x⁻¹) ⁻¹' centreCutSiegelSet K c u d₁ d₂ := by
    ext g; simp [Set.mem_preimage]
  rw [himg]
  exact (measurableSet_centreCutSiegelSet c u d₁ d₂).preimage (measurable_mul_const x⁻¹)

private theorem measure_window_lt_top (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c)
    (hd₁ : 0 < d₁) :
    letI := (pinsOf c u d₁ d₂ T).mS
    (pinsOf c u d₁ d₂ T).μ (pinsOf c u d₁ d₂ T).D < ⊤ := by
  letI := (pinsOf c u d₁ d₂ T).mS
  change NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤
  refine (MeasureTheory.measure_biUnion_finset_le T _).trans_lt (ENNReal.sum_lt_top.2 fun x _ => ?_)
  exact adelicGLHaar_mul_right_centreCutSiegelSet_lt_top K hc u hd₁ d₂ x

private theorem memLp_window_of_dominated (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c)
    (hd₁ : 0 < d₁) {Z : Set (AdelicGL2 (𝓞 K) K)} (hZ : @MeasurableSet _ (pinsOf c u d₁ d₂ T).mS Z)
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (B : ℝ)
    (hB : ∀ g ∈ (pinsOf c u d₁ d₂ T).D ∩ Z, ‖f g‖ ≤ B)
    {F : AdelicGL2 (𝓞 K) K → ℝ} (C : ℝ)
    (hF : letI := (pinsOf c u d₁ d₂ T).mS
      MemLp F 2 (((pinsOf c u d₁ d₂ T).μ).restrict ((pinsOf c u d₁ d₂ T).D \ Z)))
    (hdom : ∀ g ∈ (pinsOf c u d₁ d₂ T).D \ Z, ‖f g‖ ≤ C * ‖F g‖) :
    letI := (pinsOf c u d₁ d₂ T).mS
    MemLp f 2 (((pinsOf c u d₁ d₂ T).μ).restrict (pinsOf c u d₁ d₂ T).D) := by
  classical
  letI := (pinsOf c u d₁ d₂ T).mS
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  have hD : MeasurableSet (pinsOf c u d₁ d₂ T).D := measurableSet_window c u d₁ d₂ T
  set μD := ((pinsOf c u d₁ d₂ T).μ).restrict (pinsOf c u d₁ d₂ T).D with hμD
  have key : MemLp (Z.piecewise f f) 2 μD := by
    refine MemLp.piecewise hZ ?_ ?_
    ·
      rw [hμD, MeasureTheory.Measure.restrict_restrict hZ]
      haveI : IsFiniteMeasure (((pinsOf c u d₁ d₂ T).μ).restrict (Z ∩ (pinsOf c u d₁ d₂ T).D)) := by
        refine ⟨?_⟩
        rw [MeasureTheory.Measure.restrict_apply_univ]
        exact (MeasureTheory.measure_mono Set.inter_subset_right).trans_lt
          (measure_window_lt_top c u d₁ d₂ T hc hd₁)
      refine MeasureTheory.MemLp.of_bound hf.aestronglyMeasurable B ?_
      refine MeasureTheory.ae_restrict_of_forall_mem (hZ.inter hD) fun g hg => ?_
      exact hB g ⟨hg.2, hg.1⟩
    ·
      rw [hμD, MeasureTheory.Measure.restrict_restrict hZ.compl, Set.inter_comm, ← Set.diff_eq]
      refine MeasureTheory.MemLp.of_le_mul (c := C) hF hf.aestronglyMeasurable ?_
      exact MeasureTheory.ae_restrict_of_forall_mem (hD.diff hZ) fun g hg => hdom g hg
  simpa only [Set.piecewise_same] using key

private theorem continuous_translateSum {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (hcont : Continuous (theForm d archR archC dR dC dF))
    {n : ℕ} (ks : Fin n → AdelicGL2 (𝓞 K) K) (cs : Fin n → ℂ) :
    Continuous (translateSum d archR archC dR dC dF ks cs) := by
  unfold translateSum
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (hcont.comp (continuous_mul_const (ks i)))

end SquareIntegrableTranslates

end LanglandsTunnell.Converse.CuspSynthesis

end

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell _root_.LanglandsTunnell.Converse.CuspSynthesis _root_.P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse.CuspSynthesis.SquareIntegrableTranslates in

theorem solution
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt ω v)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archR w hw).centralExponent ((archR w hw).centralSign.val : ℤ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archC w hw).centralExponent (archC w hw).centralTwist)
    (d : JLData K S epsS ω)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (hcont : Continuous (theForm d archR archC dR dC dF))
    {n : ℕ}
    (ks : Fin n → AdelicGL2 (𝓞 K) K) (cs : Fin n → ℂ) (hks : ∀ i, ks i ∈ finiteAdelicGL2Subgroup K)
    (hcusp : @IsCuspidalFn _ (pinsOf c u d₁ d₂ T).nS _ _ (pinsOf c u d₁ d₂ T).ν unipotentGL2
      (translateSum d archR archC dR dC dF ks cs)) :
    letI := (pinsOf c u d₁ d₂ T).mS
    MeasureTheory.MemLp (translateSum d archR archC dR dC dF ks cs) 2
      (((pinsOf c u d₁ d₂ T).μ).restrict (pinsOf c u d₁ d₂ T).D) := by
  letI := (pinsOf c u d₁ d₂ T).mS
  obtain ⟨C, e, he, hbd⟩ :=
    exists_norm_translateSum_le_mul_prod_hgt_rpow K c u d₁ d₂ T hc hd₁ Pi S archR archC epsS ω hω hωunr
      hωb hωR hωC d dR dC dF hinv hnice hcont ks cs hks hcusp
  have hprod_pos : ∀ g : AdelicGL2 (𝓞 K) K, 0 < ∏ w : InfinitePlace K, hgt w g := fun g =>
    Finset.prod_pos fun w _ => localHeight_pos _
  refine memLp_window_of_dominated c u d₁ d₂ T hc hd₁ (Z := ∅) MeasurableSet.empty
    (continuous_translateSum d archR archC dR dC dF hcont ks cs) 0 (fun g hg => by simp at hg) C
    (memLp_prod_hgt_rpow_of_nonpos c u d₁ d₂ T hc hd₁ ∅ e he) ?_
  intro g hg
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (hprod_pos g).le _)]
  exact hbd g hg.1

end S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum
end P2MW
export P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum (solution)
