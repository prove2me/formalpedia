-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_whittakerLoc_one_eq_one_of_isBadPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c3e0459d-8457-5ca5-a630-5ca0f5386242

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittakerLoc_ne_zero_of_isCubicInductionDataOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_one_eq_one_of_isBadPlace
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.CubicInduction

namespace RENORM

theorem componentAt3_localToAdelic3_self (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v g) = g := by
  apply Units.ext
  change RingHom.mapMatrix ((NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp
      (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      (LanglandsTunnell.CubicInduction.finMatN (Fin 3) (𝓞 ℚ) ℚ
        (LanglandsTunnell.CubicInduction.localMatN (Fin 3) (𝓞 ℚ) ℚ v (g : Matrix (Fin 3) (Fin 3) _))) =
    (g : Matrix (Fin 3) (Fin 3) _)
  rw [RingHom.mapMatrix_apply, RingHom.coe_comp, ← Matrix.map_map, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, LanglandsTunnell.CubicInduction.mapMatrix_fin_finMatN,
    LanglandsTunnell.CubicInduction.mapMatrix_localMatN_self]

theorem componentAt3_localToAdelic3_of_ne
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 ℚ)) (hwv : w ≠ v) (g : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ w (localToAdelic3 v g) = 1 := by
  apply Units.ext
  change RingHom.mapMatrix ((NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp
      (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      (LanglandsTunnell.CubicInduction.finMatN (Fin 3) (𝓞 ℚ) ℚ
        (LanglandsTunnell.CubicInduction.localMatN (Fin 3) (𝓞 ℚ) ℚ v (g : Matrix (Fin 3) (Fin 3) _))) = _
  rw [RingHom.mapMatrix_apply, RingHom.coe_comp, ← Matrix.map_map, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, LanglandsTunnell.CubicInduction.mapMatrix_fin_finMatN,
    LanglandsTunnell.CubicInduction.mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hwv, Units.val_one]

noncomputable def archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.of fun i j => ((g i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
theorem mapMatrix_arch_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = g := by
  ext i j
  simp [archMat3, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, NumberField.AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = 1 := by
  ext i j
  simp [archMat3, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, NumberField.AdelicLevel.adeleFin_apply]

theorem archMat3_one : archMat3 1 = 1 :=
  LanglandsTunnell.CubicInduction.matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ (by rw [mapMatrix_arch_archMat3, map_one])
    (by rw [mapMatrix_fin_archMat3, map_one])

theorem archMat3_mul (g h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    archMat3 (g * h) = archMat3 g * archMat3 h :=
  LanglandsTunnell.CubicInduction.matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ
    (by rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3])
    (by rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mul_one])

noncomputable def archEmbed3 : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ where
  toFun g :=
    { val := archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      inv := archMat3 ((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      val_inv := by rw [← archMat3_mul, Units.mul_inv, archMat3_one]
      inv_val := by rw [← archMat3_mul, Units.inv_mul, archMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat3_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat3_mul _ _)

theorem archComponent3_archEmbed3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (archEmbed3 g) = g := by
  apply Units.ext
  change RingHom.mapMatrix (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ)
      (archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))) = (g : Matrix (Fin 3) (Fin 3) _)
  exact mapMatrix_arch_archMat3 _

theorem componentAt3_archEmbed3 (w : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ w (archEmbed3 g) = 1 := by
  apply Units.ext
  change RingHom.mapMatrix ((NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp
      (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      (archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))) = _
  rw [RingHom.mapMatrix_apply, RingHom.coe_comp, ← Matrix.map_map, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, mapMatrix_fin_archMat3, map_one, Units.val_one]

theorem exists_forall_componentAt3_eq_and_eq_one (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), LocalGL3 w) :
    ∃ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ w ∈ T, componentAt3 (𝓞 ℚ) ℚ w g = h w) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ T → componentAt3 (𝓞 ℚ) ℚ w g = 1) ∧
      archComponent3 (𝓞 ℚ) ℚ g = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, fun w hw => absurd hw (Finset.notMem_empty w), fun w _ => map_one _, map_one _⟩
  | insert a T haT ih =>
    obtain ⟨g, hg, hg', hga⟩ := ih
    refine ⟨localToAdelic3 a (h a) * g, fun w hw => ?_, fun w hw => ?_, ?_⟩
    · rw [(componentAt3 (𝓞 ℚ) ℚ w).map_mul]
      rcases Finset.mem_insert.mp hw with hwa | hwT
      · rw [hwa, componentAt3_localToAdelic3_self, hg' a haT, mul_one]
      · have hwa : w ≠ a := fun e => haT (e ▸ hwT)
        rw [componentAt3_localToAdelic3_of_ne a w hwa, one_mul, hg w hwT]
    · rw [(componentAt3 (𝓞 ℚ) ℚ w).map_mul]
      have hwa : w ≠ a := fun e => hw (e ▸ Finset.mem_insert_self a T)
      have hwT : w ∉ T := fun m => hw (Finset.mem_insert_of_mem m)
      rw [componentAt3_localToAdelic3_of_ne a w hwa, one_mul, hg' w hwT]
    · rw [(archComponent3 (𝓞 ℚ) ℚ).map_mul, hga, mul_one]
      exact Units.ext (LanglandsTunnell.CubicInduction.mapMatrix_arch_finMatN (Fin 3) (𝓞 ℚ) ℚ _)

theorem exists_forall_componentAt3_eq_and_archComponent3_eq (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), LocalGL3 w) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ∃ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ w ∈ T, componentAt3 (𝓞 ℚ) ℚ w g = h w) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ T → componentAt3 (𝓞 ℚ) ℚ w g = 1) ∧
      archComponent3 (𝓞 ℚ) ℚ g = gInf := by
  obtain ⟨g, hg, hg', hga⟩ := exists_forall_componentAt3_eq_and_eq_one T h
  refine ⟨g * archEmbed3 gInf, fun w hw => ?_, fun w hw => ?_, ?_⟩
  · rw [map_mul, componentAt3_archEmbed3, mul_one, hg w hw]
  · rw [map_mul, componentAt3_archEmbed3, mul_one, hg' w hw]
  · rw [map_mul, archComponent3_archEmbed3, hga, one_mul]

theorem whittaker3_zero (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ 0 g = 0 := by
  simp only [whittaker3, Pi.zero_apply, zero_mul, integral_zero]

theorem self_mem_gl3CyclicSubspace {F : Type*} [CommRing F] (W : GL (Fin 3) F → ℂ) : W ∈ gl3CyclicSubspace W := by
  refine Submodule.subset_span ⟨1, ?_⟩
  funext x
  simp [gl3AmbientRightTranslate_apply]

theorem gl3CyclicSubspace_le_of_mem {F : Type*} [CommRing F] {W X : GL (Fin 3) F → ℂ}
    (hX : X ∈ gl3CyclicSubspace W) : gl3CyclicSubspace X ≤ gl3CyclicSubspace W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, rfl⟩
  exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W h hX

theorem gl3CyclicSubspace_translate_eq {F : Type*} [CommRing F] (W : GL (Fin 3) F → ℂ) (g₀ : GL (Fin 3) F)
    (c : ℂ) (hc : c ≠ 0) :
    gl3CyclicSubspace (fun x => c⁻¹ * W (x * g₀)) = gl3CyclicSubspace W := by
  apply le_antisymm
  · apply gl3CyclicSubspace_le_of_mem
    have : (fun x => c⁻¹ * W (x * g₀)) = c⁻¹ • gl3AmbientRightTranslate (R := ℂ) g₀ W := by
      funext x; simp [gl3AmbientRightTranslate_apply]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g₀, rfl⟩)
  · apply gl3CyclicSubspace_le_of_mem
    have hmem : c • gl3AmbientRightTranslate (R := ℂ) g₀⁻¹ (fun x => c⁻¹ * W (x * g₀)) ∈
        gl3CyclicSubspace (fun x => c⁻¹ * W (x * g₀)) :=
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨g₀⁻¹, rfl⟩)
    have e : c • gl3AmbientRightTranslate (R := ℂ) g₀⁻¹ (fun x => c⁻¹ * W (x * g₀)) = W := by
      funext x
      simp [gl3AmbientRightTranslate_apply, mul_assoc, ← mul_assoc c, mul_inv_cancel₀ hc]
    rw [e] at hmem
    exact hmem

end RENORM

open RENORM in

theorem RENORM.rechoose
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker)
    (hcontW' : Continuous X.dualWhittaker)
    (hmaj : IsGaugeMajorised3 ℚ X.whittaker) (hmaj' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hform : X.form ≠ 0) (harch : X.whittakerArch ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (hT : ∀ v, IsBadPlace K μ v → v ∈ T)
    (hsm : ∀ v, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g)
    (hcen : ∀ v, IsBadPlace K μ v → ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      X.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
        ((NumberField.TateGlobal.localChar X.centralChar v t : ℂˣ) : ℂ) * X.whittakerLoc v h)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : IsBadPlace K μ w) :
    ∃ Y : CubicInductionData,
      IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} Y ∧
      Y.form ≠ 0 ∧
      Y.whittakerLoc w 1 = 1 ∧
      (∀ v, v ≠ w → Y.whittakerLoc v = X.whittakerLoc v) ∧
      (∀ v, gl3CyclicSubspace (Y.whittakerLoc v) = gl3CyclicSubspace (X.whittakerLoc v)) ∧
      Y.whittakerArch = X.whittakerArch ∧ Y.centralChar = X.centralChar ∧
      Continuous Y.form ∧ Continuous Y.whittaker ∧ Continuous Y.dualWhittaker ∧
      IsGaugeMajorised3 ℚ Y.whittaker ∧ IsGaugeMajorised3 ℚ Y.dualWhittaker ∧
      (∀ v, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, Y.whittakerLoc v (g * k) = Y.whittakerLoc v g) ∧
      (∀ v, IsBadPlace K μ v → ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
        Y.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((NumberField.TateGlobal.localChar Y.centralChar v t : ℂˣ) : ℂ) * Y.whittakerLoc v h) := by
  classical

  have hne : X.whittakerLoc w ≠ 0 :=
    LanglandsTunnell.CubicInduction.whittakerLoc_ne_zero_of_isCubicInductionDataOn K _ ψ μ X hX T hT hform w
  obtain ⟨g₀, hg₀⟩ : ∃ g, X.whittakerLoc w g ≠ 0 := Function.ne_iff.mp hne
  set c : ℂ := X.whittakerLoc w g₀ with hcdef
  set W' : LocalGL3 w → ℂ := fun x => c⁻¹ * X.whittakerLoc w (x * g₀) with hW'def
  have hW'mem : W' ∈ gl3CyclicSubspace (X.whittakerLoc w) := by
    rw [← gl3CyclicSubspace_translate_eq (X.whittakerLoc w) g₀ c hg₀]
    exact self_mem_gl3CyclicSubspace _
  have hW'1 : W' 1 = 1 := by
    simp only [hW'def, one_mul]
    exact inv_mul_cancel₀ hg₀

  obtain ⟨Y, hY, hYw, hYu, hYarch, hYcc, hYc, hYcw, hYcdw, hYg, hYdg⟩ :=
    LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen
      K ψ hψ μ D U gen {v | IsBadPlace K μ v} X hX hcont hcontW hcontW' hmaj hmaj' w hw (hsm w hw) W' hW'mem

  have hcyc : ∀ v, gl3CyclicSubspace (Y.whittakerLoc v) = gl3CyclicSubspace (X.whittakerLoc v) := by
    intro v
    by_cases hv : v = w
    · subst hv
      rw [hYw]
      exact gl3CyclicSubspace_translate_eq (X.whittakerLoc v) g₀ c hg₀
    · rw [hYu v hv]

  have hstab : ∀ v, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, Y.whittakerLoc v (g * k) = Y.whittakerLoc v g := by
    intro v hv
    by_cases hvw : v = w
    · subst hvw
      obtain ⟨Uv, hUo, hUs⟩ := hsm v hv
      refine ⟨Uv.comap (MulAut.conj g₀⁻¹).toMonoidHom, ?_, fun k hk g => ?_⟩
      · rw [Subgroup.coe_comap]
        refine hUo.preimage ?_
        have e : (⇑((MulAut.conj g₀⁻¹).toMonoidHom) : LocalGL3 v → LocalGL3 v) = fun k => g₀⁻¹ * k * g₀⁻¹⁻¹ := by
          funext k; rfl
        rw [e]
        exact (continuous_const.mul continuous_id).mul continuous_const
      · have hk' : g₀⁻¹ * k * g₀ ∈ Uv := by
          have := Subgroup.mem_comap.mp hk
          simpa [MulAut.conj_apply] using this
        rw [hYw]
        simp only [hW'def]
        have e : g * k * g₀ = g * g₀ * (g₀⁻¹ * k * g₀) := by group
        rw [e, hUs _ hk' (g * g₀)]
    · rw [hYu v hvw]
      exact hsm v hv

  have hcen' : ∀ v, IsBadPlace K μ v → ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      Y.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
        ((NumberField.TateGlobal.localChar Y.centralChar v t : ℂˣ) : ℂ) * Y.whittakerLoc v h := by
    intro v hv t h
    rw [hYcc]
    by_cases hvw : v = w
    · subst hvw
      rw [hYw]
      simp only [hW'def]
      rw [mul_assoc, hcen v hv t (h * g₀)]
      ring
    · rw [hYu v hvw]
      exact hcen v hv t h

  have hform' : Y.form ≠ 0 := by
    have hneY : ∀ v, Y.whittakerLoc v ≠ 0 := by
      intro v
      by_cases hvw : v = w
      · subst hvw
        rw [hYw]
        intro h0
        have := congr_fun h0 1
        rw [hW'1] at this
        exact one_ne_zero this
      · rw [hYu v hvw]
        exact LanglandsTunnell.CubicInduction.whittakerLoc_ne_zero_of_isCubicInductionDataOn K _ ψ μ X hX T hT hform v
    choose hpt hhpt using fun v => Function.ne_iff.mp (hneY v)
    obtain ⟨gInf, hgInf⟩ : ∃ gi, X.whittakerArch gi ≠ 0 := Function.ne_iff.mp harch
    obtain ⟨g, hg1, hg2, hg3⟩ := exists_forall_componentAt3_eq_and_archComponent3_eq T hpt gInf
    have hfac := hY.factorizable g T (fun v hv => hT v hv) (fun v hv => by
      rw [hg2 v hv]; exact Subgroup.one_mem _)
    have hWg : Y.whittaker g ≠ 0 := by
      rw [hfac, hg3, hYarch]
      refine mul_ne_zero hgInf (Finset.prod_ne_zero_iff.mpr fun v hv => ?_)
      rw [hg1 v hv]
      exact hhpt v
    intro h0
    apply hWg
    rw [hY.whittaker_eq, h0]
    exact whittaker3_zero _ _ _
  exact ⟨Y, hY, hform', by rw [hYw]; exact hW'1, hYu, hcyc, hYarch, hYcc, hYc, hYcw, hYcdw, hYg, hYdg, hstab, hcen'⟩

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker)
    (hcontW' : Continuous X.dualWhittaker)
    (hmaj : IsGaugeMajorised3 ℚ X.whittaker) (hmaj' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hform : X.form ≠ 0) (harch : X.whittakerArch ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (hT : ∀ v, IsBadPlace K μ v → v ∈ T)
    (hsm : ∀ v, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g)
    (hcen : ∀ v, IsBadPlace K μ v → ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      X.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
        ((NumberField.TateGlobal.localChar X.centralChar v t : ℂˣ) : ℂ) * X.whittakerLoc v h) :
    ∃ Y : CubicInductionData,
      IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} Y ∧
      Y.form ≠ 0 ∧
      (∀ w, IsBadPlace K μ w → Y.whittakerLoc w 1 = 1) ∧
      (∀ v, ¬ IsBadPlace K μ v → Y.whittakerLoc v = X.whittakerLoc v) ∧
      (∀ v, gl3CyclicSubspace (Y.whittakerLoc v) = gl3CyclicSubspace (X.whittakerLoc v)) ∧
      Y.whittakerArch = X.whittakerArch ∧ Y.centralChar = X.centralChar ∧
      Continuous Y.form ∧ Continuous Y.whittaker ∧ Continuous Y.dualWhittaker ∧
      IsGaugeMajorised3 ℚ Y.whittaker ∧ IsGaugeMajorised3 ℚ Y.dualWhittaker ∧
      (∀ v, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, Y.whittakerLoc v (g * k) = Y.whittakerLoc v g) ∧
      (∀ v, IsBadPlace K μ v → ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
        Y.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((NumberField.TateGlobal.localChar Y.centralChar v t : ℂˣ) : ℂ) * Y.whittakerLoc v h) := by
  classical

  suffices key : ∀ T' : Finset (HeightOneSpectrum (𝓞 ℚ)), ∃ Y : CubicInductionData,
      IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} Y ∧
      Y.form ≠ 0 ∧
      (∀ w ∈ T', IsBadPlace K μ w → Y.whittakerLoc w 1 = 1) ∧
      (∀ v, ¬ IsBadPlace K μ v → Y.whittakerLoc v = X.whittakerLoc v) ∧
      (∀ v, gl3CyclicSubspace (Y.whittakerLoc v) = gl3CyclicSubspace (X.whittakerLoc v)) ∧
      Y.whittakerArch = X.whittakerArch ∧ Y.centralChar = X.centralChar ∧
      Continuous Y.form ∧ Continuous Y.whittaker ∧ Continuous Y.dualWhittaker ∧
      IsGaugeMajorised3 ℚ Y.whittaker ∧ IsGaugeMajorised3 ℚ Y.dualWhittaker ∧
      (∀ v, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, Y.whittakerLoc v (g * k) = Y.whittakerLoc v g) ∧
      (∀ v, IsBadPlace K μ v → ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
        Y.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((NumberField.TateGlobal.localChar Y.centralChar v t : ℂˣ) : ℂ) * Y.whittakerLoc v h) by
    obtain ⟨Y, h1, h2, h3, h4⟩ := key T
    exact ⟨Y, h1, h2, fun w hw => h3 w (hT w hw) hw, h4⟩
  intro T'
  induction T' using Finset.induction_on with
  | empty =>
    exact ⟨X, hX, hform, fun w hw => absurd hw (Finset.notMem_empty w), fun _ _ => rfl, fun _ => rfl, rfl, rfl,
      hcont, hcontW, hcontW', hmaj, hmaj', hsm, hcen⟩
  | insert a T' haT ih =>
    obtain ⟨Y, hY, hYform, hY1, hYgood, hYcyc, hYarch, hYcc, hYc, hYcw, hYcdw, hYg, hYdg, hYsm, hYcen⟩ := ih
    by_cases ha : IsBadPlace K μ a
    · obtain ⟨Z, hZ, hZform, hZa, hZu, hZcyc, hZarch, hZcc, hZc, hZcw, hZcdw, hZg, hZdg, hZsm, hZcen⟩ :=
        RENORM.rechoose K ψ hψ μ D U gen Y hY hYc hYcw hYcdw hYg hYdg hYform (hYarch ▸ harch) T hT hYsm hYcen a ha
      refine ⟨Z, hZ, hZform, fun w hw hbw => ?_, fun v hv => ?_, fun v => (hZcyc v).trans (hYcyc v),
        hZarch.trans hYarch, hZcc.trans hYcc, hZc, hZcw, hZcdw, hZg, hZdg, hZsm, hZcen⟩
      · rcases Finset.mem_insert.mp hw with rfl | hwT
        · exact hZa
        · by_cases hwa : w = a
          · subst hwa; exact hZa
          · rw [hZu w hwa]; exact hY1 w hwT hbw
      · have hva : v ≠ a := fun e => hv (e ▸ ha)
        rw [hZu v hva]; exact hYgood v hv
    · refine ⟨Y, hY, hYform, fun w hw hbw => ?_, hYgood, hYcyc, hYarch, hYcc, hYc, hYcw, hYcdw, hYg, hYdg, hYsm, hYcen⟩
      rcases Finset.mem_insert.mp hw with rfl | hwT
      · exact absurd hbw ha
      · exact hY1 w hwT hbw

end S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_one_eq_one_of_isBadPlace
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_one_eq_one_of_isBadPlace (solution)
