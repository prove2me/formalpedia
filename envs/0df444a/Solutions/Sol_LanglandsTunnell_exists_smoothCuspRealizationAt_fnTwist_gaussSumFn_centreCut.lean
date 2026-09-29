-- Prove2me | solution 1 for LanglandsTunnell.exists_smoothCuspRealizationAt_fnTwist_gaussSumFn_centreCut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/43eae8c9-0664-5d27-9100-38dc879c8ad1

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Theorems.Thm_LanglandsTunnell_fnTwist_gaussSumFn_isSmoothCuspData
import Theorems.Thm_LanglandsTunnell_fnTwist_gaussSumFn_level_invariant
import Theorems.Thm_LanglandsTunnell_isHeckeCosetEigenfunctionAt_fnTwist_gaussSumFn
import Theorems.Thm_LanglandsTunnell_exists_admitsModulus_gaussSumFn_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_smoothCuspRealizationAt_fnTwist_gaussSumFn_centreCut
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply"
p2m_attr_erase "simp" "IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option Elab.async false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel

namespace TwistCentreCut

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume AutomorphicForm.SmoothCusp AutomorphicForm.GaussTwist

variable (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))

private abbrev window : Set (AdelicGL2 (𝓞 F) F) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂

private abbrev pins : CarrierPins F :=
  productionPinsOf F (window F c u d₁ d₂ T)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private theorem window_measure_lt_top (hc : 0 < c) (hd₁ : 0 < d₁) :
    (letI := (pins F c u d₁ d₂ T).mS; (pins F c u d₁ d₂ T).μ (pins F c u d₁ d₂ T).D < ⊤) := by
  letI := glBorel (Fin 2) (𝓞 F) F
  calc (pins F c u d₁ d₂ T).μ (pins F c u d₁ d₂ T).D
      = adelicGLHaar (Fin 2) (𝓞 F) F (window F c u d₁ d₂ T) := rfl
    _ ≤ ∑ x ∈ T, adelicGLHaar (Fin 2) (𝓞 F) F ((· * x) '' centreCutSiegelSet F c u d₁ d₂) :=
        measure_biUnion_finset_le _ _
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun x _ =>
        adelicGLHaar_mul_right_centreCutSiegelSet_lt_top F hc u hd₁ d₂ x

private theorem window_measurableSet :
    (letI := (pins F c u d₁ d₂ T).mS; MeasurableSet (pins F c u d₁ d₂ T).D) := by
  letI := glBorel (Fin 2) (𝓞 F) F
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  show MeasurableSet (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
  refine Finset.measurableSet_biUnion T fun x _ => ?_
  rw [Set.image_mul_right]
  exact (continuous_id.mul continuous_const).measurable (measurableSet_centreCutSiegelSet c u d₁ d₂)

private theorem memLp_two_of_bound (hc : 0 < c) (hd₁ : 0 < d₁) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) (hφb : ∃ B : ℝ, ∀ g ∈ window F c u d₁ d₂ T, ‖φ g‖ ≤ B) :
    letI := (pins F c u d₁ d₂ T).mS;
    MeasureTheory.MemLp φ 2 ((pins F c u d₁ d₂ T).μ.restrict (pins F c u d₁ d₂ T).D) := by
  letI := glBorel (Fin 2) (𝓞 F) F
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  obtain ⟨B, hB⟩ := hφb
  haveI : IsFiniteMeasure ((pins F c u d₁ d₂ T).μ.restrict (pins F c u d₁ d₂ T).D) :=
    isFiniteMeasure_restrict.mpr (window_measure_lt_top F c u d₁ d₂ T hc hd₁).ne
  refine MemLp.of_bound hφc.aestronglyMeasurable B ?_
  exact (ae_restrict_iff' (window_measurableSet F c u d₁ d₂ T)).mpr
    (Filter.Eventually.of_forall fun g hg => hB g hg)

private theorem integrable_constantTermIntegrand (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (Φ : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F (pins F c u d₁ d₂ T) Φ.toRawCentral)
    (hR : ∀ (α : F) (g : AdelicGL2 (𝓞 F) F),
      WhittakerCoefficientIntegrable F (pins F c u d₁ d₂ T) ψ R.toFun α g)
    (g : AdelicGL2 (𝓞 F) F) :
    MeasureTheory.Integrable (constantTermIntegrand unipotentGL2 R.toFun g) (pins F c u d₁ d₂ T).ν := by
  have h := hR 0 g
  unfold WhittakerCoefficientIntegrable at h
  simp only [map_zero, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one] at h
  exact h

private theorem norm_apply_eq_one_of_isFiniteOrder (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η) (z : (AdeleRing (𝓞 F) F)ˣ) :
    ‖((η z : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hη.isOfFinOrder
  have h1 : η z ^ n = 1 := by
    have h := congrArg (fun f : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ => f z) hpow
    simpa using h
  have h2 : ‖((η z : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h2

private def twistedSystemAt (Φ : HeckeEigensystem F ℂ) (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) : HeckeEigensystem F ℂ where
  level := Φ.level * 𝔣 ^ 2
  level_ne_bot := by
    rw [pow_two]; intro h
    rcases Ideal.mul_eq_bot.1 h with h | h
    · exact Φ.level_ne_bot h
    · rcases Ideal.mul_eq_bot.1 h with h | h <;> exact h𝔣 h
  a := fun v => ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) * Φ.a v
  b := fun v => ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) ^ 2 * Φ.b v

private theorem impl
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Φ.toRawCentral)
    (hR : IsBoundedGenuineCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      (NumberField.StandardAddChar.stdAddChar F) Φ.toRawCentral R)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η)
    (𝔣 : Ideal (𝓞 F)) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) :
    ∃ 𝔣₀ : Ideal (𝓞 F), 𝔣₀ ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus F η 𝔣₀ ∧
      (∃ g : AdelicGL2 (𝓞 F) F, GaussTwist.gaussSumFn F η 𝔣₀ R.toFun g ≠ 0) ∧
      ∃ Φ' : HeckeEigensystem F ℂ,
        Φ'.level = Φ.level * 𝔣₀ ^ 2 ∧
        (∀ v : HeightOneSpectrum (𝓞 F),
          Φ'.a v = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) * Φ.a v ∧
          Φ'.b v = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) ^ 2 * Φ.b v) ∧
        ∃ R₁ : SmoothCuspRealizationAt F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
              (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Φ'.toRawCentral,
          R₁.toFun = fnTwist F η (GaussTwist.gaussSumFn F η 𝔣₀ R.toFun) ∧
          IsBoundedGenuineCuspRealizationAt F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
              (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
            (NumberField.StandardAddChar.stdAddChar F) Φ'.toRawCentral R₁ := by
  classical
  have hRF : IsBoundedGenuineFn F (pins F c u d₁ d₂ T) (NumberField.StandardAddChar.stdAddChar F) R.toFun :=
    hR
  obtain ⟨-, -, hRint, -⟩ := id hRF

  obtain ⟨𝔣₀, h𝔣₀, hmod₀, g₀, hg₀⟩ :=
    LanglandsTunnell.exists_admitsModulus_gaussSumFn_ne_zero F c u d₁ d₂ T Φ.toRawCentral R hR η 𝔣 hmod

  have hη₁ : IsUnitaryChar (𝓞 F) F η := fun z => norm_apply_eq_one_of_isFiniteOrder F η hη z
  letI := (pins F c u d₁ d₂ T).mS
  obtain ⟨⟨hauto, hcusp⟩, hkf⟩ := R.smoothCusp
  have h2 := (lsXiMemberAt_iff (𝓞 F) F (pins F c u d₁ d₂ T).μ (pins F c u d₁ d₂ T).Z
    R.centralChar (pins F c u d₁ d₂ T).D R.toFun).mp hauto

  obtain ⟨-, hlsxiT, hcuspT, hkfT, hcenT, hgenT⟩ :=
    LanglandsTunnell.fnTwist_gaussSumFn_isSmoothCuspData F η hη.isIdeleClassChar hη.continuous hη₁
      𝔣₀ h𝔣₀ hmod₀ (pins F c u d₁ d₂ T).ν (pins F c u d₁ d₂ T) (NumberField.StandardAddChar.stdAddChar F)
      h2.1 (integrable_constantTermIntegrand F c u d₁ d₂ T _ Φ R hRint) hcusp hkf hRF
  obtain ⟨hTc, hTwin, -, -⟩ := id hgenT
  have hL2 := memLp_two_of_bound F c u d₁ d₂ T hc hd₁ hTc (hTwin c u d₁ d₂ T hc hd₁)
  have hN' : Φ.level * 𝔣₀ ^ 2 ≠ ⊥ := (twistedSystemAt F Φ η 𝔣₀ h𝔣₀).level_ne_bot
  have hinv : ∀ g, ∀ k ∈ (productionPinsCompact F).U Φ.level, R.toFun (g * k) = R.toFun g :=
    fun g k hk => R.level_invariant g k hk
  refine ⟨𝔣₀, h𝔣₀, hmod₀, ⟨g₀, hg₀⟩, twistedSystemAt F Φ η 𝔣₀ h𝔣₀, rfl, fun v => ⟨rfl, rfl⟩, ?_⟩
  refine ⟨{ toFun := fnTwist F η (gaussSumFn F η 𝔣₀ R.toFun)
            exists_ne_zero := ⟨g₀, by
              rw [fnTwist_apply]
              exact mul_ne_zero (Units.ne_zero _) hg₀⟩
            centralChar := twistedCentralChar F (pins F c u d₁ d₂ T).Z R.centralChar η
            smoothCusp :=
              ⟨⟨(lsXiMemberAt_iff (𝓞 F) F (pins F c u d₁ d₂ T).μ (pins F c u d₁ d₂ T).Z
                  (twistedCentralChar F (pins F c u d₁ d₂ T).Z R.centralChar η)
                  (pins F c u d₁ d₂ T).D (fnTwist F η (gaussSumFn F η 𝔣₀ R.toFun))).mpr
                  ⟨hlsxiT, hL2⟩, hcuspT⟩, hkfT⟩
            level_invariant := fun g k hk =>
              LanglandsTunnell.fnTwist_gaussSumFn_level_invariant F Φ.level Φ.level_ne_bot η 𝔣₀ h𝔣₀
                hmod₀ hinv g k hk
            exceptionalSet := R.exceptionalSet ∪ (Ideal.finite_factors hN').toFinset
            hecke_eigen := by
              intro v hv
              simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
              exact LanglandsTunnell.isHeckeCosetEigenfunctionAt_fnTwist_gaussSumFn F Φ.level η 𝔣₀
                hmod₀ v hv.2 hinv (R.hecke_eigen v hv.1)
            central_eigen := by
              intro v hv g
              simp only [Finset.mem_union, not_or] at hv
              have hR' : ∀ g' : AdelicGL2 (𝓞 F) F,
                  R.toFun (centralScalar (𝓞 F) F
                      (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) * g')
                    = Φ.toRawCentral.b v * R.toFun g' :=
                fun g' => R.central_eigen v hv.1 g'
              show fnTwist F η (gaussSumFn F η 𝔣₀ R.toFun) (centralScalar (𝓞 F) F
                  (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) * g)
                = (twistedSystemAt F Φ η 𝔣₀ h𝔣₀).toRawCentral.b v
                    * fnTwist F η (gaussSumFn F η 𝔣₀ R.toFun) g
              rw [hcenT _ _ hR' g]
              have hb : (twistedSystemAt F Φ η 𝔣₀ h𝔣₀).toRawCentral.b v
                  = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) ^ 2
                    * Φ.toRawCentral.b v := by
                show (HeckeEigensystem.cNorm v)⁻¹ * ((_ : ℂ) ^ 2 * Φ.b v)
                  = _ ^ 2 * ((_ : ℂ)⁻¹ * Φ.b v)
                ring
              rw [hb] }, rfl, ?_⟩

  exact hgenT

end TwistCentreCut

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Φ.toRawCentral)
    (hR : IsBoundedGenuineCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      (NumberField.StandardAddChar.stdAddChar F) Φ.toRawCentral R)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η)
    (𝔣 : Ideal (𝓞 F)) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) :
    ∃ 𝔣₀ : Ideal (𝓞 F), 𝔣₀ ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus F η 𝔣₀ ∧
      (∃ g : AdelicGL2 (𝓞 F) F, GaussTwist.gaussSumFn F η 𝔣₀ R.toFun g ≠ 0) ∧
      ∃ Φ' : HeckeEigensystem F ℂ,
        Φ'.level = Φ.level * 𝔣₀ ^ 2 ∧
        (∀ v : HeightOneSpectrum (𝓞 F),
          Φ'.a v = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) * Φ.a v ∧
          Φ'.b v = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) ^ 2 * Φ.b v) ∧
        ∃ R₁ : SmoothCuspRealizationAt F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
              (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Φ'.toRawCentral,
          R₁.toFun = fnTwist F η (GaussTwist.gaussSumFn F η 𝔣₀ R.toFun) ∧
          IsBoundedGenuineCuspRealizationAt F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
              (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
            (NumberField.StandardAddChar.stdAddChar F) Φ'.toRawCentral R₁ := by
  exact TwistCentreCut.impl F c u d₁ d₂ T hc hd₁ Φ R hR η hη 𝔣 hmod

end

end S_LanglandsTunnell_exists_smoothCuspRealizationAt_fnTwist_gaussSumFn_centreCut
end P2MW
export P2MW.S_LanglandsTunnell_exists_smoothCuspRealizationAt_fnTwist_gaussSumFn_centreCut (solution)
