-- Prove2me | solution 1 for LanglandsTunnell.exists_realArchParam_archDatumR_whittakerCoefficient_fibre_eq_isCasimirEigen_of_archOccursInClassOf_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b3de91ae-47e6-5392-bed8-5154434980e1

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le
import Theorems.Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_exists_realArchParam_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_Converse_exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero
import Theorems.Thm_LanglandsTunnell_archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_or_twist_sign_of_archOccursInClassOf_rat
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_twist_sign_W_eq_sign_det_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_realArchParam_archDatumR_whittakerCoefficient_fibre_eq_isCasimirEigen_of_archOccursInClassOf_rat
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul"
p2m_attr_erase "simp" "IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.mem_borelSubgroup_iff"
p2m_attr_erase "simp" "AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.mem_inducedSectionSubmodule_iff LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

namespace Ws23
namespace PEXR
open AutomorphicForm LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

theorem k0_twist01 (P : RealArchParam) : (match (generalizing := false) (P.twist 0 1) with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) = (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) := by
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    simp only [RealArchParam.twist]
    have key : ∀ a b : ZMod 2, (a + 1 + (b + 1) = 0 ↔ a + b = 0) := by decide
    simp only [key]
  | discrete u m hm => simp [RealArchParam.twist]

theorem laplace_twist01 (P : RealArchParam) : laplaceEigenvalue (P.twist 0 1) = laplaceEigenvalue P := by
  cases P <;> simp [RealArchParam.twist, laplaceEigenvalue]

theorem ce_twist01 (P : RealArchParam) : centralExponent (P.twist 0 1) = centralExponent P := by
  cases P <;> simp [RealArchParam.twist, centralExponent]

theorem hgen_twist01 (P : RealArchParam) (hgen : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))) : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P.twist 0 1 = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) := by
  cases P with
  | principal v₁ b₁ v₂ b₂ =>
    intro u₁ u₂ a₁ a₂ h p hp hu
    simp only [RealArchParam.twist, RealArchParam.principal.injEq, add_zero] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    have := hgen v₁ v₂ b₁ b₂ rfl p hp hu
    intro h'; apply this; linear_combination h'
  | discrete u₀ k hk =>
    intro u₁ u₂ a₁ a₂ h; simp [RealArchParam.twist] at h

theorem htype_twist01 (P : RealArchParam) (htype : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)) : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P.twist 0 1 = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) := by
  cases P with
  | principal v₁ b₁ v₂ b₂ =>
    intro u₁ u₂ a₁ a₂ h
    simp only [RealArchParam.twist, RealArchParam.principal.injEq, add_zero] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact htype v₁ v₂ b₁ b₂ rfl
  | discrete u₀ k hk =>
    intro u₁ u₂ a₁ a₂ h; simp [RealArchParam.twist] at h

theorem archW_congr_R {K : Type} [Field K] [NumberField K]
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR dR' : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (h : ∀ w hw, (dR w hw).W = (dR' w hw).W) :
    archW archR archC dR dC = archW archR archC dR' dC := by
  funext g
  unfold archW
  refine Finset.prod_congr rfl fun w _ => ?_
  split_ifs with hw
  · rw [h w hw]
  · rfl

theorem k0_of_clauses (P : RealArchParam) (k₀ : ℤ)
    (h1 : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → (k₀ = 0 ∨ k₀ = 1) ∧ ((k₀ : ZMod 2) = a₁ + a₂))
    (h2 : ∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1) :
    k₀ = (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) := by
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    obtain ⟨h01, hpar⟩ := h1 u₁ u₂ a₁ a₂ rfl
    rcases h01 with rfl | rfl
    · simp at hpar ⊢; exact hpar.symm
    · simp at hpar ⊢
      intro h; rw [h] at hpar; exact absurd hpar (by decide)
  | discrete u m hm => simpa using h2 u m hm rfl

theorem pos_of_cover
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) : 0 < d₂ := by
  obtain ⟨γ, z, hmem⟩ := hcov 1
  simp only [Set.mem_iUnion, Set.mem_image] at hmem
  obtain ⟨x, -, g, hg, -⟩ := hmem
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have h4 := (mem_centreCutSiegelSet_iff.mp hg).2.2.2 v₀
  exact lt_of_lt_of_le (NumberField.AdelicVolume.archDetNorm_pos v₀ g) h4.2

end Ws23.PEXR

set_option maxHeartbeats 6400000 in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (hΦ : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ (fun _ => True)) :
    ∃ (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
      (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
      (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw)),
      ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ,
          (∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g =
              (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                archW (fun _ _ => P) archC dR dC g * z) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal), (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ))) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchCasimir.IsCasimirEigen (dR w hw)) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ g : GL (Fin 2) ℝ, (dR w hw).W g ≠ 0) ∧
      (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
        (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ) := by
  classical

  obtain ⟨Φ', hΦ'agr, R', hR', -⟩ := hΦ
  have hc : 0 < c := lt_of_not_ge fun h =>
    AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre ℚ c u d₁ d₂ T h hd hcov Φ' ⟨R', hR'⟩
  have hd₂ : 0 < d₂ := Ws23.PEXR.pos_of_cover ℚ c u d₁ d₂ T hcov
  have hdp : 0 < max d₁ (d₂ / 2) := lt_max_of_lt_right (half_pos hd₂)
  have hdp₂ : max d₁ (d₂ / 2) < d₂ := max_lt hd (half_lt_self hd₂)
  have hle : d₁ ≤ max d₁ (d₂ / 2) := le_max_left _ _
  have hΘ : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ (fun _ => True) := ⟨Φ', hΦ'agr, R', hR', trivial⟩
  obtain ⟨hcovp, htr⟩ := AutomorphicForm.coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le ℚ c u d₁ d₂ (max d₁ (d₂ / 2)) T
    hc hdp hdp₂ hle hcov Φ hΘ

  obtain ⟨P, hgen, htype, hoccP⟩ := LanglandsTunnell.exists_realArchParam_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre ℚ c u (max d₁ (d₂ / 2)) d₂ T hdp₂ hcovp Φ Rat.infinitePlace Rat.isReal_infinitePlace ((htr _).mp hΘ)

  obtain ⟨D, k₀, hk₁, hk₂, hDW, hDE, hDnv⟩ := LanglandsTunnell.Converse.exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero P hgen
  have hk₀ : k₀ = (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) := Ws23.PEXR.k0_of_clauses P k₀ hk₁ hk₂

  have hoccK : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u (max d₁ (d₂ / 2)) d₂) Φ
      (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ k₀).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ ∧
          IsArchSmoothAt Rat.isReal_infinitePlace φ ∧
          (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt Rat.isReal_infinitePlace) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
                NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt Rat.isReal_infinitePlace) φ g‖ ≤ B) ∧
          archCasimirAt Rat.isReal_infinitePlace φ = (laplaceEigenvalue P) • φ ∧
          (∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
              φ (adelicArchGLInclAt ℚ Rat.infinitePlace (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toRingHom
                (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ (RealArchParam.centralExponent P)) * φ g)) := by
    rw [hk₀]; exact hoccP
  rcases LanglandsTunnell.archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_or_twist_sign_of_archOccursInClassOf_rat c u (max d₁ (d₂ / 2)) d₂ T hc hdp hdp₂ hcovp Φ P hgen htype D k₀ hk₁ hk₂ hDW hDE hDnv hoccK with
    ⟨archC, dC, hFIB⟩ | ⟨D', archC, dC, hW', hFIB'⟩
  ·
    refine ⟨P, archC, fun _ _ => D, dC, (htr _).mpr hFIB, ?_, fun _ _ => hDE, fun _ _ => hDnv, hgen, htype, ?_⟩
    · intro w hw; rw [← hk₀]; exact hDW
    · exact (htr _).mpr (hoccP.mono fun φ hφ => hφ.1)
  ·
    obtain ⟨D'', hW'', hCEf, hWTf, hnvf⟩ := LanglandsTunnell.Converse.ArchDatumR.exists_twist_sign_W_eq_sign_det_mul P D
    have hWeq : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ((fun (_ : InfinitePlace ℚ) (_ : _) => D') w hw).W = ((fun (_ : InfinitePlace ℚ) (_ : _) => D'') w hw).W := by
      intro w hw; funext x; simp only []; rw [hW' x, hW'' x]
    have hFIB'' := hFIB'
    rw [Ws23.PEXR.archW_congr_R (fun _ _ => P.twist 0 1) archC (fun _ _ => D') (fun _ _ => D'') dC hWeq] at hFIB''
    refine ⟨P.twist 0 1, archC, fun _ _ => D'', dC, (htr _).mpr hFIB'', ?_, fun _ _ => hCEf hDE, fun _ _ => hnvf hDnv,
      Ws23.PEXR.hgen_twist01 P hgen, Ws23.PEXR.htype_twist01 P htype, ?_⟩
    · intro w hw; rw [Ws23.PEXR.k0_twist01, ← hk₀]; exact hWTf _ hDW
    · rw [Ws23.PEXR.k0_twist01]
      exact (htr _).mpr (hoccP.mono fun φ hφ => hφ.1)

#print axioms solution

end S_LanglandsTunnell_exists_realArchParam_archDatumR_whittakerCoefficient_fibre_eq_isCasimirEigen_of_archOccursInClassOf_rat
end P2MW
export P2MW.S_LanglandsTunnell_exists_realArchParam_archDatumR_whittakerCoefficient_fibre_eq_isCasimirEigen_of_archOccursInClassOf_rat (solution)
