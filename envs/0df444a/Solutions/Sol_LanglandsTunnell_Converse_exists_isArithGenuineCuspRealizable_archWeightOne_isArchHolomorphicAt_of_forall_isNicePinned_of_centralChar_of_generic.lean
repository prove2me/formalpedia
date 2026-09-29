-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/72167342-2d38-528d-bab8-7a32bdd70929

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Theorems.Thm_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_of_isJLNice
import Theorems.Thm_LanglandsTunnell_Converse_exists_isJLNice_of_forall_isNicePinned
import Theorems.Thm_LanglandsTunnell_Converse_exists_finWhittakerDatum_Wf_ne_zero
import Theorems.Thm_LanglandsTunnell_Converse_exists_archDatumC_W_ne_zero
import Theorems.Thm_LanglandsTunnell_Converse_exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic
p2m_attr_erase "instance" "AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "instance" "instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val MeasureTheory.L2.kernelIntegralLM_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply"
p2m_attr_erase "simp" "IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply"
p2m_attr_erase "simp" "AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel

namespace Ws23
namespace ConvDock

open LanglandsTunnell LanglandsTunnell.Converse

theorem twist_twist_eq_self {F : Type} [Field F] [NumberField F] (Φ : HeckeEigensystem F ℂ)
    (χ χ' : HeightOneSpectrum (𝓞 F) → ℂ) (h : ∀ v, χ' v * χ v = 1) :
    (Φ.twist χ).twist χ' = Φ := by
  cases Φ with
  | mk lvl hl a b =>
    simp only [HeckeEigensystem.twist, HeckeEigensystem.mk.injEq, true_and]
    refine ⟨funext fun v => ?_, funext fun v => ?_⟩
    · rw [← mul_assoc, h, one_mul]
    · rw [← mul_assoc, ← mul_pow, h, one_pow, one_mul]

theorem agreesAwayFromFinite_twist {F : Type} [Field F] [NumberField F] {Φ Φ' : HeckeEigensystem F ℂ}
    (h : HeckeEigensystem.AgreesAwayFromFinite Φ Φ') (χ : HeightOneSpectrum (𝓞 F) → ℂ) :
    HeckeEigensystem.AgreesAwayFromFinite (Φ.twist χ) (Φ'.twist χ) := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun v hv => ?_⟩
  obtain ⟨ha, hb⟩ := hS v hv
  simp only [HeckeEigensystem.twist_a, HeckeEigensystem.twist_b, ha, hb, and_self]

theorem normHalf_mul_normNegHalf {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (((Ideal.absNorm v.asIdeal : ℝ) ^ ((1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
  have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [← Complex.ofReal_mul, ← Real.rpow_add hN]
  norm_num

theorem normHalf_ne_zero {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (((Ideal.absNorm v.asIdeal : ℝ) ^ ((1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := normHalf_mul_normNegHalf (F := F) v
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem archWeightCharAt_one {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal) :
    archWeightCharAt hw 1 = archWeightOneAt hw := by
  ext k
  simp [archWeightCharAt]

theorem centralExponent_swap (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (RealArchParam.principal u₂ a₂ u₁ a₁).centralExponent = (RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent := by
  simp [RealArchParam.centralExponent, add_comm]

theorem centralSign_swap (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (RealArchParam.principal u₂ a₂ u₁ a₁).centralSign = (RealArchParam.principal u₁ a₁ u₂ a₂).centralSign := by
  simp [RealArchParam.centralSign, add_comm]

theorem centralChar_swap (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    ArchR.centralChar (RealArchParam.principal u₂ a₂ u₁ a₁) = ArchR.centralChar (RealArchParam.principal u₁ a₁ u₂ a₂) := by
  funext y
  simp only [ArchR.centralChar, centralExponent_swap, centralSign_swap]

theorem archFactor_twist_swap (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) (u : ℂ) (a : ZMod 2) :
    ((RealArchParam.principal u₂ a₂ u₁ a₁).twist u a).archFactor =
      ((RealArchParam.principal u₁ a₁ u₂ a₂).twist u a).archFactor := by
  funext s
  simp only [RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC,
    Multiset.pair_comm (u₂ + u + signShift (a₂ + a))]

theorem epsilonFactor_twist_swap (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) (u : ℂ) (a : ZMod 2) :
    ((RealArchParam.principal u₂ a₂ u₁ a₁).twist u a).epsilonFactor =
      ((RealArchParam.principal u₁ a₁ u₂ a₂).twist u a).epsilonFactor := by
  simp only [RealArchParam.twist, RealArchParam.epsilonFactor, mul_comm]

noncomputable def swapDatum {u₁ : ℂ} {a₁ : ZMod 2} {u₂ : ℂ} {a₂ : ZMod 2}
    (d : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂)) :
    ArchDatumR (RealArchParam.principal u₂ a₂ u₁ a₁) where
  W := d.W
  smooth := d.smooth
  unip_law := d.unip_law
  central_law := by rw [centralChar_swap]; exact d.central_law
  zetaEntire := d.zetaEntire
  zetaEntire_differentiable := d.zetaEntire_differentiable
  zeta_abscissa := d.zeta_abscissa
  zeta_integrable := d.zeta_integrable
  zeta_eq := by intro g u a s hg hs; rw [archFactor_twist_swap]; exact d.zeta_eq g u a s hg hs
  functional_equation := by
    intro g u a s hg
    rw [centralExponent_swap, centralSign_swap, epsilonFactor_twist_swap]
    exact d.functional_equation g u a s hg
  zetaEntire_finiteOrder := d.zetaEntire_finiteOrder
  decay_top := d.decay_top
  decay_zero := d.decay_zero

@[scoped simp] theorem swapDatum_W {u₁ : ℂ} {a₁ : ZMod 2} {u₂ : ℂ} {a₂ : ZMod 2}
    (d : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂)) : (swapDatum d).W = d.W := rfl

theorem exists_datum (P : RealArchParam) (h : ∃ a₁ a₂ : ZMod 2, a₁ ≠ a₂ ∧ P = RealArchParam.principal 0 a₁ 0 a₂) :
    ∃ d : ArchDatumR P,
      (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        d.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ 1 r : ℂ) * d.W (x : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      (∀ (x : GL (Fin 2) ℝ),
        MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
          ((z.im : ℝ) : ℂ)⁻¹ *
            d.W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      ∃ g : GL (Fin 2) ℝ, d.W g ≠ 0 := by
  obtain ⟨a₁, a₂, hne, rfl⟩ := h
  obtain ⟨d, hwt, hhol, g, hg⟩ := exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero
  fin_cases a₁ <;> fin_cases a₂
  · exact absurd rfl hne
  · exact ⟨d, hwt, hhol, g, hg⟩
  · exact ⟨swapDatum d, hwt, hhol, g, hg⟩
  · exact absurd rfl hne

end Ws23.ConvDock
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic.Ws23 P2MW.S_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic.Ws23.ConvDock"
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic.Ws23"

open LanglandsTunnell LanglandsTunnell.Converse Ws23.ConvDock in
theorem solution
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (hepsS : ∀ v ∈ S, Continuous ⇑(epsS v))
    (A Ad : (↥S → ℤ) → ℂ)
    (hsys : ∀ (N : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)), ¬ v.asIdeal ∣ N →
      ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K,
        HeckeIntegralSeam.IsHeckeCosetSystem
          ((productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).U N)
          (heckeGen (𝓞 K) K v) reps)
    (hbd : ∃ C : ℝ, ∀ n : ↥S → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C)
    (hsupp : ∃ n₀ : ↥S → ℤ, ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0)
    (hA0 : A ≠ 0)
    (hnice : ∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsAdmissibleTwist K μ →
      (∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
        localChar μ v u * epsS v u = 1) →
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
        (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
        (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        IsNicePinned (twistedDatum K Pi S archR archC μ uR aR uC kC)
          (sPart K S A μ) (sPartDual K S Ad μ)
          (pinnedRootNumber K Pi μ S archR archC uR aR uC kC) (finiteConductor K μ S))
    (hnonEis : ∀ (μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
      IsIdeleClassChar (𝓞 K) K μ₁ → IsIdeleClassChar (𝓞 K) K μ₂ →
      Continuous μ₁ → Continuous μ₂ →
      ¬ HeckeEigensystem.AgreesAwayFromFinite Pi
          (eisensteinTableOf K Pi.level Pi.level_ne_bot μ₁ μ₂))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt ω v)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) = Pi.b v)
    (hgen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      Pi.a v ^ 2 ≠ Pi.b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹))
    (hgenR : ∀ (w : InfinitePlace K) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (hgenC : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (p q : ℕ), 1 ≤ p → 1 ≤ q →
      ¬ ((2 * ((archC w hw).u₁ - (archC w hw).u₂) = ((p + q : ℕ) : ℂ) ∧
            (archC w hw).k₁ - (archC w hw).k₂ = (p : ℤ) - q) ∨
          (2 * ((archC w hw).u₁ - (archC w hw).u₂) = -((p + q : ℕ) : ℂ) ∧
            (archC w hw).k₁ - (archC w hw).k₂ = (q : ℤ) - p)))
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archR w hw).centralExponent ((archR w hw).centralSign.val : ℤ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archC w hw).centralExponent (archC w hw).centralTwist)
    (harchR₁ : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      ∃ a₁ a₂ : ZMod 2, a₁ ≠ a₂ ∧ archR w hw = RealArchParam.principal 0 a₁ 0 a₂) :
    ∃ Φ' : HeckeEigensystem K ℂ,
      (∃ R : SmoothCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Φ'.toRawCentral,
        IsGenuineCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Φ'.toRawCentral R ∧
        (∀ w : InfinitePlace K, ∀ hw : w.IsReal, HasArchCharacterAt₀ K w (archWeightOneAt hw) R.toFun) ∧
        (∀ w : InfinitePlace K, ∀ hw : w.IsReal, IsArchHolomorphicAt w hw R.toFun)) ∧
      HeckeEigensystem.AgreesAwayFromFinite Pi Φ' := by
  classical

  set χp : HeightOneSpectrum (𝓞 K) → ℂ := fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ ((1 / 2 : ℝ)) : ℝ) : ℂ) with hχp
  set χm : HeightOneSpectrum (𝓞 K) → ℂ := fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hχm
  have L1 : (Pi.twist χp).twist χm = Pi :=
    twist_twist_eq_self Pi χp χm fun v => normHalf_mul_normNegHalf (F := K) v

  obtain ⟨d, hd⟩ := exists_isJLNice_of_forall_isNicePinned K Pi S archR archC epsS hepsS A Ad hbd hsupp hA0 hnice ω hω

  have hb : ∀ v ∉ S, (Pi.twist χp).b v ≠ 0 := by
    intro v hv
    rw [HeckeEigensystem.twist_b, ← hωb v hv]
    exact mul_ne_zero (pow_ne_zero _ (normHalf_ne_zero (F := K) v)) (Units.ne_zero _)
  obtain ⟨dF, hnvF⟩ := exists_finWhittakerDatum_Wf_ne_zero K S (Pi.twist χp) hb

  choose dR hwt hhol hnvR using fun (w : InfinitePlace K) (hw : w.IsReal) => exists_datum (archR w hw) (harchR₁ w hw)
  choose dC hnvC using fun (w : InfinitePlace K) (hw : w.IsComplex) => exists_archDatumC_W_ne_zero (archC w hw)

  have H := exists_isArithGenuineCuspRealizable_of_isJLNice K c u d₁ d₂ T hc hd₁ (Pi.twist χp) S archR archC epsS
    ω hω hωunr (by intro v hv; rw [L1]; exact hωb v hv) hωR hωC d dR dC dF hnvR hnvC hnvF (by rw [L1]; exact hd)
    (by intro μ₁ μ₂ h₁ h₂ c₁ c₂; rw [L1]; exact hnonEis μ₁ μ₂ h₁ h₂ c₁ c₂)
  obtain ⟨Φ', -, hagree, -, -, h5⟩ := H
  obtain ⟨R, -, R', -, hR'gen, hR'wt, hR'hol⟩ := h5 (fun _ _ => 1) (fun w hw => hwt w hw) (fun w hw => hhol w hw)
  refine ⟨Φ'.twist χm, ⟨R', hR'gen, fun w hw => ?_, hR'hol⟩, ?_⟩
  · rw [← archWeightCharAt_one]; exact hR'wt w hw
  · have := agreesAwayFromFinite_twist hagree χm
    rwa [L1] at this

end S_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic (solution)
