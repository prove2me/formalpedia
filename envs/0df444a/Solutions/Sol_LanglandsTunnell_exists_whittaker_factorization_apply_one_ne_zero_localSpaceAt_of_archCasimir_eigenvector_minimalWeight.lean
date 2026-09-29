-- Prove2me | solution 1 for LanglandsTunnell.exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_minimalWeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/719cc260-2a26-5467-8ce6-7a35d78f32f3

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.MellinTransform
import Theorems.Thm_LanglandsTunnell_exists_whittaker_factorization_eq_or_eq_smul_raise_of_archCasimir_eigenvector_minimalWeight
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_minimalWeight
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar"
p2m_attr_erase "instance" "AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.iotaZsqrtdNegTwo_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

namespace P2M
namespace WPlusFamilyMin

theorem psiQ_archLine (w : InfinitePlace ℚ) (_hw : w.IsReal) (x : InfiniteAdeleRing ℚ)
    (_hx : ∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) :
    NumberField.StandardAddChar.psiQ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ)
      = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)) := by
  rw [NumberField.StandardAddChar.psiQ_apply]
  show NumberField.StandardAddChar.psiArch x * NumberField.StandardAddChar.psiFin 0 = _
  rw [AddChar.map_zero_eq_one, mul_one, NumberField.StandardAddChar.psiArch_apply, finprod_eq_prod_of_fintype,
    Fintype.prod_subsingleton _ w, NumberField.StandardAddChar.psiArchPlace_apply,
    extensionEmbeddingOfIsReal_apply]

end P2M.WPlusFamilyMin

theorem solution
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (_hR : Continuous R.toFun)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam)
    (_hS : R.exceptionalSet ⊆ S)
    (_htype : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (_hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ))
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ)
    (_hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsGeneral ℚ)
        R.centralChar Φ.level S Φ φ₁)
    (_hne : φ₁ ≠ 0)
    (_hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁)
    (_hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k₁ w)) φ₁)
    (_hminp : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₁ w = 0 ∨ k₁ w = 1) ∧ ((k₁ w : ZMod 2) = a₁ + a₂))
    (_hmind : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn → k₁ w = (n : ℤ) + 1)
    (_hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ₁ ∧ archCasimirAt hw φ₁ = (archR w hw).laplaceEigenvalue • φ₁)
    (_hJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ₁ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ₁ g)
    (_hlow : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_hlow1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_heq : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = a₂ ∨ u₁ = u₂)

    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (_hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) R.centralChar V) (_hφ₁V : φ₁ ∈ V)
    (_hVloc : ∀ φ ∈ V,
          (∀ p : HeightOneSpectrum (𝓞 ℚ),
            ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
                W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
                  fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
            (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
              ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
                ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ,
                  (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
                    W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
            (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
                ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))))
    (_htorus : ∃ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 ∧
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 (diagOne a) ≠ 0) :
    ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      C 1 1 ≠ 0 ∧
    ∀ par : InfinitePlace ℚ → ZMod 2,
      ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ),
        IsIsotypicCuspFormAt ℚ
            (productionPinsGeneral ℚ)
            R.centralChar Φ.level S Φ φ ∧
        φ ≠ 0 ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ),
            ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
                W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
                  fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
            (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
              ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
                ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ,
                  (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
                    W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
            (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
                ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))) ∧
        (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
            (k w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w)) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
        (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
            whittakerCoefficient ℚ
                (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ φ 1 (diagOne a * g)
              = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                  * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
            ∀ t : ℝ, Wr w (-t) = (-1 : ℂ) ^ a₁.val * Wr w t) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr w t = 0) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
            ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
              MellinConvergent
                  (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s ∧
                mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s
                  = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                      * ((archR w hw).twist 0 a₁).archFactor s) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
          (b = par w ∨ b = par w + (archR w hw).centralSign) →
            ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
              MellinConvergent
                  (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s ∧
                mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s
                  = ((archR w hw).twist 0 b).archFactor s) := by
  classical

  have hcov : CoversModCentre ℚ
      (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) :=
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat

  obtain ⟨C, ⟨Wr₁, hWr₁⟩, hfam⟩ :=
    LanglandsTunnell.exists_whittaker_factorization_eq_or_eq_smul_raise_of_archCasimir_eigenvector_minimalWeight
      (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov Φ R _hR
      NumberField.StandardAddChar.psiQ NumberField.StandardAddChar.isGlobalAddChar_psiQ
      P2M.WPlusFamilyMin.psiQ_archLine S archR _hS _htype _hcen φ₁ k₁ _hiso _hne _hconv _hwt _hminp _hmind
      _hpair _hJ _hlow _hlow1 _heq

  obtain ⟨a₀, ha₀, hWa₀⟩ := _htorus
  have hC : C 1 1 ≠ 0 := by
    intro h0
    apply hWa₀
    have h := hWr₁ a₀ 1 (Subgroup.one_mem _)
    rw [mul_one, ha₀, h0, mul_zero] at h
    exact h
  refine ⟨C, hC, fun par => ?_⟩
  obtain ⟨φ, Wr, k, hform, hiso, hne, hconv, hwt, hkp, hkd, hfact, hpar, hvan, hmel1, hmel2⟩ := hfam par

  have hφV : φ ∈ V := by
    rcases hform with rfl | ⟨w, hw, cr, rfl⟩
    · exact _hφ₁V
    · refine V.smul_mem cr ?_

      let χ : ∀ v : InfinitePlace ℚ, rowIsometrySubgroup₀ v.Completion →* ℂˣ :=
        fun v => archWeightCharAt (isReal_infinitePlace_rat v) (k₁ v)
      let χ' : ℤ → ∀ v : InfinitePlace ℚ, rowIsometrySubgroup₀ v.Completion →* ℂˣ :=
        fun m v => archWeightCharAt (isReal_infinitePlace_rat v) m
      have hmem : φ₁ ∈ V ⊓ CuspidalConstituent.levelInvariantSubmodule ℚ
            (productionPinsOf ℚ (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
              (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
              (adelicBox ℚ)) Φ.level ⊓
            archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by
        refine ⟨⟨_hφ₁V, fun g u' hu' => _hiso.level_invariant g u' hu'⟩, ?_⟩
        refine (mem_archCutSubmodule_ofChar_iff (F := ℚ) χ φ₁).mpr fun v => ?_
        obtain rfl : v = w := Subsingleton.elim _ _
        exact _hwt v (isReal_infinitePlace_rat v)
      have h := AutomorphicForm.CuspidalConstituent.iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar ℚ
        (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov R.centralChar V _hV
        isReal_infinitePlace_rat Φ.level Φ.level_ne_bot χ w hw (k₁ w) rfl χ'
        (fun m v hv => absurd (Subsingleton.elim v w) hv) (fun m => rfl) φ₁ hmem
      have h1 := (Submodule.mem_inf.mp (Submodule.mem_inf.mp (h.2 1)).1).1
      simp only [Function.iterate_one] at h1
      exact h1

  exact ⟨φ, Wr, k, hiso, hne, fun p => _hVloc φ hφV p, hconv, hwt, hkp, hkd, hfact, hpar, hvan, hmel1, hmel2⟩

end S_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_minimalWeight
end P2MW
export P2MW.S_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_minimalWeight (solution)
