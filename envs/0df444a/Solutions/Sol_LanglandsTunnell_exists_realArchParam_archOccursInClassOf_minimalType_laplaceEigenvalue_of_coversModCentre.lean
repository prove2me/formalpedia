-- Prove2me | solution 1 for LanglandsTunnell.exists_realArchParam_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/753d8bd3-ad08-53f8-afec-0786f12097b9

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ArchParam
import Theorems.Thm_AutomorphicForm_exists_forall_archCasimirAt_eq_and_archOccursInClassOf_isArchSmoothAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_forall_archOccursInClassOf_and_centralExponent
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_archWeightChar_neg_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre
import Theorems.Thm_AutomorphicForm_im_eq_zero_and_re_pos_and_eq_of_forall_archCasimirAt_eq_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_realArchParam_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply SemialgHom.baseChange_of_algebraMap_tmul_left"
p2m_attr_erase "simp" "SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.mem_inducedSectionSubmodule_iff"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open LanglandsTunnell LanglandsTunnell.RealArchParam

namespace ParamDefCore

def minType (P : RealArchParam) : ℤ :=
  match P with
  | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
  | .discrete _ m _ => (m : ℤ) + 1

theorem exists_realArchParam (lam c : ℂ) (k₀ : ℕ) (a₀ : ZMod 2)
    (hpar : (k₀ : ZMod 2) = a₀) (hreal : lam.im = 0)
    (h0 : k₀ = 0 → 0 < lam.re) (h1 : k₀ = 1 → (1 / 4 : ℝ) ≤ lam.re)
    (h2 : 2 ≤ k₀ → lam = ((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2)) :
    ∃ P : RealArchParam,
      P.laplaceEigenvalue = lam ∧ minType P = k₀ ∧ P.centralExponent = c ∧ P.centralSign = a₀ ∧
      (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = .principal u₁ a₁ u₂ a₂ →
        ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = .principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) := by
  rcases Nat.lt_or_ge k₀ 2 with hk | hk
  ·

    set r : ℝ := 1 - 4 * lam.re with hr
    have hlam : lam = (lam.re : ℂ) := by
      apply Complex.ext <;> simp [hreal]
    obtain ⟨ν, hν2, hνre⟩ : ∃ ν : ℂ, ν ^ 2 = (r : ℂ) ∧ |ν.re| < 1 := by
      rcases le_or_gt 0 r with hr0 | hr0
      · refine ⟨(Real.sqrt r : ℂ), ?_, ?_⟩
        · rw [← Complex.ofReal_pow, Real.sq_sqrt hr0]
        ·
          have hr1 : r < 1 := by
            rcases Nat.lt_succ_iff.mp (Nat.lt_succ_iff.mpr (Nat.le_of_lt_succ hk)) |>.lt_or_eq with hk0 | hk1
            · have : k₀ = 0 := by omega
              have := h0 this; rw [hr]; linarith
            · have := h1 hk1; rw [hr]; linarith
          rw [Complex.ofReal_re, abs_lt]
          constructor
          · have := Real.sqrt_nonneg r; linarith
          · calc Real.sqrt r < Real.sqrt 1 := Real.sqrt_lt_sqrt hr0 hr1
              _ = 1 := Real.sqrt_one
      · refine ⟨Complex.I * (Real.sqrt (-r) : ℂ), ?_, ?_⟩
        · rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith), Complex.ofReal_neg]
          ring
        · simp
    refine ⟨.principal ((c + ν) / 2) 0 ((c - ν) / 2) a₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
    ·
      rw [laplaceEigenvalue_principal]
      have : (c + ν) / 2 - (c - ν) / 2 = ν := by ring
      rw [this, div_pow, hν2, hlam]
      push_cast [hr]
      ring
    ·
      simp only [minType, zero_add]
      interval_cases k₀
      · have : a₀ = 0 := by simpa using hpar.symm
        simp [this]
      · have : a₀ = 1 := by simpa using hpar.symm
        subst this
        simp
    · simp [centralExponent]; ring
    · simp [centralSign]
    ·
      intro u₁ u₂ a₁ a₂ hP p hp hdiff
      simp only [RealArchParam.principal.injEq] at hP
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hP
      exfalso
      have hν : ν = (p : ℂ) := by rw [← hdiff]; ring
      rw [hν] at hνre
      simp only [Complex.intCast_re] at hνre
      have : (1 : ℝ) ≤ |(p : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hp
      linarith
    · intro u₁ u₂ a₁ a₂ hP
      simp only [RealArchParam.principal.injEq] at hP
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hP
      have : (c + ν) / 2 - (c - ν) / 2 = ν := by ring
      rwa [this]
  ·
    refine ⟨.discrete (c / 2) (k₀ - 1) (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [laplaceEigenvalue_discrete, h2 hk]
      have : ((k₀ - 1 : ℕ) : ℂ) = (k₀ : ℂ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this]; ring
    · simp only [minType]
      push_cast [Nat.cast_sub (show 1 ≤ k₀ by omega)]
      ring
    · simp [centralExponent]; ring
    · simp only [centralSign, ← hpar]
      rw [Nat.cast_sub (show 1 ≤ k₀ by omega)]
      push_cast
      ring
    · intro u₁ u₂ a₁ a₂ hP; exact absurd hP (by simp)
    · intro u₁ u₂ a₁ a₂ hP; exact absurd hP (by simp)

end ParamDefCore

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True)) :
    ∃ P : RealArchParam,
      (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧
            (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
            archCasimirAt hw φ = (laplaceEigenvalue P) • φ ∧
            (∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
              φ (adelicArchGLInclAt F w (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ (RealArchParam.centralExponent P)) * φ g)) := by
  classical

  obtain ⟨lam, hrig, hsmo⟩ :=
    AutomorphicForm.exists_forall_archCasimirAt_eq_and_archOccursInClassOf_isArchSmoothAt_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ w hw

  obtain ⟨c₀, hcen⟩ :=
    AutomorphicForm.exists_forall_archOccursInClassOf_and_centralExponent F c u d₁ d₂ T Θ w hw

  obtain ⟨hre, hpos, hquart, hdisc⟩ :=
    AutomorphicForm.im_eq_zero_and_re_pos_and_eq_of_forall_archCasimirAt_eq_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ w hw lam hrig

  obtain ⟨n, hn⟩ :=
    AutomorphicForm.exists_archOccursInClassOf_archWeightChar_of_coversModCentre F c u d₁ d₂ T hd hcov Θ hΘ w hw

  have hex : ∃ k : ℕ, ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ (k : ℤ)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) := by
    obtain ⟨k, hk | hk⟩ : ∃ k : ℕ, (k : ℤ) = n ∨ (k : ℤ) = -n := ⟨n.natAbs, by omega⟩
    · exact ⟨k, by rw [hk]; exact hn⟩
    · exact ⟨k, by
        rw [hk]
        exact AutomorphicForm.archOccursInClassOf_archWeightChar_neg_of_coversModCentre
          F c u d₁ d₂ T hd hcov Θ w hw n hn⟩

  obtain ⟨k₀, hk₀, hmin⟩ : ∃ k₀ : ℕ, ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ (k₀ : ℤ)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) ∧
      ∀ m : ℕ, m < k₀ → ¬ ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ (m : ℤ)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩

  have h0 : k₀ = 0 → 0 < lam.re := by
    rintro rfl
    exact hpos (by simpa only [Nat.cast_zero] using hk₀)
  have h1 : k₀ = 1 → (1 / 4 : ℝ) ≤ lam.re := by
    rintro rfl
    exact hquart (by simpa only [Nat.cast_one] using hk₀)
  have h2 : 2 ≤ k₀ → lam = ((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2) := by
    intro hk
    have hne : ¬ ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ ((k₀ : ℤ) - 2)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) := by
      have e : ((k₀ - 2 : ℕ) : ℤ) = (k₀ : ℤ) - 2 := by omega
      rw [← e]
      exact hmin (k₀ - 2) (by omega)
    have := hdisc (k₀ : ℤ) (by omega) hk₀ hne
    simpa only [Int.cast_natCast] using this

  obtain ⟨P, hle, hmt, hce, -, hgen, htype⟩ :=
    ParamDefCore.exists_realArchParam lam c₀ k₀ (k₀ : ZMod 2) rfl (hre (k₀ : ℤ) hk₀) h0 h1 h2
  refine ⟨P, hgen, htype, ?_⟩

  refine (hcen _ (hsmo (k₀ : ℤ) hk₀)).mono ?_
  rintro φ ⟨⟨hχ, hs, hD, hc⟩, hz⟩
  refine ⟨?_, hs, hD, ?_, ?_⟩
  · convert hχ using 4
    all_goals exact hmt
  · rw [hle]; exact hc
  · rw [hce]; exact hz

end S_LanglandsTunnell_exists_realArchParam_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre
end P2MW
export P2MW.S_LanglandsTunnell_exists_realArchParam_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre (solution)
