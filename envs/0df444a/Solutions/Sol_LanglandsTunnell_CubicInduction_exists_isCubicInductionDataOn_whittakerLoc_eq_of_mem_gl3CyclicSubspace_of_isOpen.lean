-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/0af02bb6-3188-555f-b878-68b029a3b667

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_LanglandsTunnell_CubicInduction_isGaugeMajorised3_of_mem_gl3CyclicSubspace
import Theorems.Thm_LanglandsTunnell_CubicInduction_summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasIotaMoments_of_hasSum_mirabolicTranslate_of_isGaugeMajorised3
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_mem_gl3CyclicSubspace_of_isOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.CubicInduction

noncomputable section

namespace WhittakerTranslateClosure

open Topology Filter
open scoped ProbabilityTheory

section Cyclic

variable {F : Type} [CommRing F] {R : Type} [CommRing R]

private theorem isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace (ψ : AddChar F R) {W : GL (Fin 3) F → R}
    (hW : IsGL3PsiWhittakerFn ψ W) {W' : GL (Fin 3) F → R} (hW' : W' ∈ gl3CyclicSubspace W) :
    IsGL3PsiWhittakerFn ψ W' := by
  have hle : gl3CyclicSubspace W ≤ gl3PsiWhittakerFnSpace F R ψ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψ h ((mem_gl3PsiWhittakerFnSpace_iff ψ W).mpr hW)
  exact (mem_gl3PsiWhittakerFnSpace_iff ψ W').mp (hle hW')

private theorem gl3CyclicSubspace_le_of_mem {W W' : GL (Fin 3) F → R} (h : W' ∈ gl3CyclicSubspace W) :
    gl3CyclicSubspace W' ≤ gl3CyclicSubspace W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, rfl⟩
  exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W g h

private theorem gl3CyclicSubspace_eq_of_mem_of_mem {W W' : GL (Fin 3) F → R} (h₁ : W' ∈ gl3CyclicSubspace W)
    (h₂ : W ∈ gl3CyclicSubspace W') : gl3CyclicSubspace W' = gl3CyclicSubspace W :=
  le_antisymm (gl3CyclicSubspace_le_of_mem h₁) (gl3CyclicSubspace_le_of_mem h₂)

private def repOn (S : Submodule R (GL (Fin 3) F → R))
    (hS : ∀ g : GL (Fin 3) F, ∀ f ∈ S, gl3AmbientRightTranslate (R := R) g f ∈ S) :
    GL (Fin 3) F →* Module.End R S where
  toFun g := (gl3AmbientRightTranslate (R := R) g).restrict (fun f hf => hS g f hf)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    show (f : GL (Fin 3) F → R) (h * 1) = (f : GL (Fin 3) F → R) h
    rw [mul_one]
  map_mul' g₁ g₂ := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    show (f : GL (Fin 3) F → R) (h * (g₁ * g₂)) = (f : GL (Fin 3) F → R) (h * g₁ * g₂)
    rw [mul_assoc]

private theorem uniqueness_of_eq (ψ : AddChar F R) (S T : Submodule R (GL (Fin 3) F → R))
    (hS : ∀ g : GL (Fin 3) F, ∀ f ∈ S, gl3AmbientRightTranslate (R := R) g f ∈ S)
    (hT : ∀ g : GL (Fin 3) F, ∀ f ∈ T, gl3AmbientRightTranslate (R := R) g f ∈ T) (hST : S = T)
    (h : GL3WhittakerUniquenessStatement (repOn S hS) ψ) : GL3WhittakerUniquenessStatement (repOn T hT) ψ := by
  subst hST
  exact h

private theorem hasWhittakerMultOne_of_gl3CyclicSubspace_eq (ψ : AddChar F R) {W W' : GL (Fin 3) F → R}
    (h : gl3CyclicSubspace W = gl3CyclicSubspace W') (hW : HasWhittakerMultOne ψ W) :
    HasWhittakerMultOne ψ W' := by
  have hW₀ : GL3WhittakerUniquenessStatement
      (repOn (gl3CyclicSubspace W) (fun g f hf => gl3AmbientRightTranslate_mem_gl3CyclicSubspace W g hf)) ψ := hW
  exact uniqueness_of_eq ψ _ _ _ (fun g f hf => gl3AmbientRightTranslate_mem_gl3CyclicSubspace W' g hf) h hW₀

private theorem transposeInv3_mul (g h : GL (Fin 3) F) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3
    h := by
  apply Units.ext
  show (((g * h)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ =
    ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ * ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem transposeInv3_transposeInv3 (g : GL (Fin 3) F) : transposeInv3 (transposeInv3 g) = g := by
  apply Units.ext
  show ((g : Matrix (Fin 3) (Fin 3) F)ᵀ)ᵀ = (g : Matrix (Fin 3) (Fin 3) F)
  exact Matrix.transpose_transpose _

end Cyclic

section Components

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem componentAt3_localToAdelic3_self (h : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v h) = h := by
  apply Units.ext
  change (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
    (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))))) =
    (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
  rw [mapMatrix_fin_finMatN, mapMatrix_localMatN_self]

private theorem componentAt3_localToAdelic3_of_ne (h : LocalGL3 v) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    componentAt3 (𝓞 ℚ) ℚ w (localToAdelic3 v h) = 1 := by
  apply Units.ext
  change (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
    (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))))) =
    (1 : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ))
  rw [mapMatrix_fin_finMatN, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hw]

private theorem archComponent3_localToAdelic3 (h : LocalGL3 v) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v h) = 1 := by
  apply Units.ext
  change (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
    (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) =
    (1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
  exact mapMatrix_arch_finMatN (Fin 3) (𝓞 ℚ) ℚ _

end Components

section Global

private theorem dualForm_rightTranslate (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (e : AdelicGL 3 (𝓞 ℚ) ℚ) :
    dualForm (gl3AmbientRightTranslate e Φ) = gl3AmbientRightTranslate (transposeInv3 e) (dualForm Φ) := by
  funext g
  simp only [dualForm, gl3AmbientRightTranslate_apply, transposeInv3_mul, transposeInv3_transposeInv3]

private theorem whittaker3_rightTranslate (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (e g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ (gl3AmbientRightTranslate e Φ) g = whittaker3 pins ψ Φ (g * e) := by
  unfold whittaker3
  simp only [gl3AmbientRightTranslate_apply, mul_assoc]

private theorem continuous_rightTranslate {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ) (e : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous (gl3AmbientRightTranslate e Φ) :=
  hΦ.comp (continuous_mul_const e)

private theorem sum_smul_rightTranslate_mem {ι : Type} (s : Finset ι) (c : ι → ℂ) (e : ι → AdelicGL 3 (𝓞 ℚ) ℚ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    (∑ i ∈ s, c i • gl3AmbientRightTranslate (e i) W) ∈ gl3CyclicSubspace W :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨e i, rfl⟩)

private theorem continuous_sum_smul_rightTranslate {ι : Type} (s : Finset ι) (c : ι → ℂ) (e : ι → AdelicGL 3 (𝓞 ℚ) ℚ)
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : Continuous W) :
    Continuous (∑ i ∈ s, c i • gl3AmbientRightTranslate (e i) W) := by
  have h : (∑ i ∈ s, c i • gl3AmbientRightTranslate (e i) W) = fun g => ∑ i ∈ s, c i * W (g * e i) := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gl3AmbientRightTranslate_apply]
  rw [h]
  exact continuous_finsetSum s fun i _ => continuous_const.mul (hW.comp (continuous_mul_const (e i)))

end Global

private def comb {ι : Type} (s : Finset ι) (c : ι → ℂ) (e : ι → AdelicGL 3 (𝓞 ℚ) ℚ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  ∑ i ∈ s, c i • gl3AmbientRightTranslate (e i) Φ

private theorem comb_apply {ι : Type} (s : Finset ι) (c : ι → ℂ) (e : ι → AdelicGL 3 (𝓞 ℚ) ℚ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ
    → ℂ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : comb s c e Φ g = ∑ i ∈ s, c i * Φ (g * e i) := by
  simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gl3AmbientRightTranslate_apply]

section Continuity

private theorem continuous_upperUnipotent3 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      upperUnipotent3 p.1 p.2.1 p.2.2 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (!![1, p.1, p.2.2; 0, 1, p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> (try simp) <;> fun_prop
  · show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (!![1, -p.1, p.1 * p.2.1 - p.2.2; 0, 1, -p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> (try simp) <;> fun_prop

private theorem continuous_radicalP21 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => radicalP21 ![p.1, p.2] := by
  show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 0 p.2 p.1
  exact continuous_upperUnipotent3.comp (continuous_const.prodMk (continuous_snd.prodMk continuous_fst))

private theorem continuous_radicalP12 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => radicalP12 ![p.1, p.2] := by
  show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 p.1 0 p.2
  exact continuous_upperUnipotent3.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))

@[scoped fun_prop]
private theorem _root_.Continuous.upperUnipotent3 {β : Type} [TopologicalSpace β] {a b c : β → AdeleRing (𝓞 ℚ) ℚ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous fun t => upperUnipotent3 (a t) (b t) (c t) :=
  continuous_upperUnipotent3.comp (ha.prodMk (hb.prodMk hc))

p2m_alias "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.Continuous.upperUnipotent3" "Continuous.upperUnipotent3"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.WhittakerTranslateClosure.Continuous"

@[scoped fun_prop]
private theorem _root_.Continuous.radicalP21 {β : Type} [TopologicalSpace β] {a b : β → AdeleRing (𝓞 ℚ) ℚ} (ha :
    Continuous a)
    (hb : Continuous b) : Continuous fun t => radicalP21 ![a t, b t] :=
  continuous_radicalP21.comp (ha.prodMk hb)

p2m_alias "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.Continuous.radicalP21" "Continuous.radicalP21"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.WhittakerTranslateClosure.Continuous"

@[scoped fun_prop]
private theorem _root_.Continuous.radicalP12 {β : Type} [TopologicalSpace β] {a b : β → AdeleRing (𝓞 ℚ) ℚ} (ha :
    Continuous a)
    (hb : Continuous b) : Continuous fun t => radicalP12 ![a t, b t] :=
  continuous_radicalP12.comp (ha.prodMk hb)

p2m_alias "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.Continuous.radicalP12" "Continuous.radicalP12"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.WhittakerTranslateClosure.Continuous"

private theorem continuous_transposeInv3 :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => transposeInv3 g := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Units.continuous_coe_inv.matrix_transpose
  · exact Units.continuous_val.matrix_transpose

private theorem continuous_dualForm {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ) : Continuous (dualForm Φ) :=
  hΦ.comp continuous_transposeInv3

private theorem continuous_inv_char {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : Continuous ψ) :
    Continuous (ψ⁻¹ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) := by
  have h : ((ψ⁻¹ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) : AdeleRing (𝓞 ℚ) ℚ → ℂ) = fun a => ψ (-a) :=
    funext fun a => AddChar.inv_apply ψ a
  rw [h]
  exact hψ.comp continuous_neg

end Continuity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.WhittakerTranslateClosure.Continuous"

section Measure

variable (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
  (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)

private theorem borelSpace_nS :
    @BorelSpace (AdeleRing (𝓞 ℚ) ℚ) _ (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).nS :=
  AdelicHaar.borelSpace_adeleBorel (R := 𝓞 ℚ) (K := ℚ)

private theorem isProbabilityMeasure_ν :
    IsProbabilityMeasure (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν :=
  isProbabilityMeasure_productionPinsOf_ν ℚ D U gen _ (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
    (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne

private theorem ae_mem_adelicBox :
    ∀ᵐ x ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν, x ∈ AdelicBox.adelicBox ℚ := by
  rw [productionPinsOf_ν]
  exact ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)

private theorem integrable_of_continuous {f : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) :
    Integrable f (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  haveI := borelSpace_nS D U gen
  haveI := isProbabilityMeasure_ν D U gen
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  refine (integrable_const M).mono' hf.aestronglyMeasurable ?_
  exact (ae_mem_adelicBox D U gen).mono fun x hx => hM x (hsub hx)

private theorem continuous_integral_param {α : Type} [AddGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α]
    [LocallyCompactSpace α]
    (F : α → AdeleRing (𝓞 ℚ) ℚ → ℂ) (hF : Continuous fun p : α × AdeleRing (𝓞 ℚ) ℚ => F p.1 p.2) :
    Continuous fun a => ∫ x, F a x ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  haveI := borelSpace_nS D U gen
  haveI := isProbabilityMeasure_ν D U gen
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hint : ∀ a : α, Integrable (F a) (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := fun a =>
    integrable_of_continuous D U gen (hF.comp (continuous_const.prodMk continuous_id))
  refine continuous_iff_continuousAt.mpr fun a₀ => ?_
  have hunif : TendstoUniformly (fun a (z : C) => F a z) (fun z : C => F a₀ z) (𝓝 a₀) := by
    letI : UniformSpace α := IsTopologicalAddGroup.rightUniformSpace α
    letI : UniformSpace (AdeleRing (𝓞 ℚ) ℚ) := IsTopologicalAddGroup.rightUniformSpace _
    have hjoint : Continuous ↿(fun (a : α) (z : C) => F a z) :=
      hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact Continuous.tendstoUniformly (fun a (z : C) => F a z) hjoint a₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hunif (ε / 2) (half_pos hε)] with a ha
  show dist (∫ x, F a x ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
      (∫ x, F a₀ x ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) < ε
  rw [dist_eq_norm, ← integral_sub (hint a) (hint a₀)]
  calc ‖∫ x, F a x - F a₀ x ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν‖
      ≤ ∫ _x, ε / 2 ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
        refine norm_integral_le_of_norm_le (integrable_const _) ?_
        refine (ae_mem_adelicBox D U gen).mono fun x hx => ?_
        have h := ha ⟨x, hsub hx⟩
        rw [dist_eq_norm, norm_sub_rev] at h
        exact h.le
    _ = ε / 2 := by simp
    _ < ε := half_lt_self hε

private theorem integral_finset_comb {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    ∫ x, ∑ i ∈ s, c i * f i x ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν =
      ∑ i ∈ s, c i * ∫ x, f i x ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  rw [show (∫ x, ∑ i ∈ s, c i * f i x ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) =
      ∑ i ∈ s, ∫ x, c i * f i x ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν from
    integral_finsetSum s fun i hi => integrable_of_continuous D U gen (continuous_const.mul (hf i hi))]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul (c i) (f i)

end Measure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.WhittakerTranslateClosure.Continuous"

section Laws

variable (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
  (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)

private theorem continuous_inner_integral {χ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hχ : Continuous χ)
    {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      ∫ z, Φ (upperUnipotent3 p.1 p.2 z * h) * χ (-(p.1 + p.2))
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  have hjoint : Continuous fun q : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      Φ (upperUnipotent3 q.1.1 q.1.2 q.2 * h) * χ (-(q.1.1 + q.1.2)) :=
    (hΦ.comp ((continuous_fst.fst.upperUnipotent3 continuous_fst.snd continuous_snd).mul
      continuous_const)).mul (hχ.comp (continuous_fst.fst.add continuous_fst.snd).neg)
  exact continuous_integral_param D U gen
    (fun (p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) (z : AdeleRing (𝓞 ℚ) ℚ) =>
      Φ (upperUnipotent3 p.1 p.2 z * h) * χ (-(p.1 + p.2))) hjoint

private theorem continuous_iterated_integral {χ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hχ : Continuous χ)
    {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous fun x : AdeleRing (𝓞 ℚ) ℚ =>
      ∫ y, ∫ z, Φ (upperUnipotent3 x y z * h) * χ (-(x + y))
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν :=
  continuous_integral_param D U gen
    (fun (x y : AdeleRing (𝓞 ℚ) ℚ) => ∫ z, Φ (upperUnipotent3 x y z * h) * χ (-(x + y))
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
    (continuous_inner_integral D U gen hχ hΦ h)

private theorem whittaker3_comb {χ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hχ : Continuous χ) {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (e : ι → AdelicGL 3 (𝓞 ℚ) ℚ) {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) χ (comb s c e Φ) g =
      ∑ i ∈ s, c i * whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) χ Φ (g * e i) := by

  have hz : ∀ (i : ι) (x y : AdeleRing (𝓞 ℚ) ℚ),
      Continuous fun z : AdeleRing (𝓞 ℚ) ℚ => Φ (upperUnipotent3 x y z * (g * e i)) * χ (-(x + y)) := by
    intro i x y
    exact (hΦ.comp ((continuous_const.upperUnipotent3 continuous_const continuous_id').mul
      continuous_const)).mul continuous_const
  have hy : ∀ (i : ι) (x : AdeleRing (𝓞 ℚ) ℚ), Continuous fun y : AdeleRing (𝓞 ℚ) ℚ =>
      ∫ z, Φ (upperUnipotent3 x y z * (g * e i)) * χ (-(x + y))
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
    intro i x
    refine continuous_integral_param D U gen
      (fun y z => Φ (upperUnipotent3 x y z * (g * e i)) * χ (-(x + y))) ?_
    exact (hΦ.comp ((continuous_const.upperUnipotent3 continuous_fst continuous_snd).mul
      continuous_const)).mul (hχ.comp (continuous_const.add continuous_fst).neg)
  have hx : ∀ i : ι, Continuous fun x : AdeleRing (𝓞 ℚ) ℚ =>
      ∫ y, ∫ z, Φ (upperUnipotent3 x y z * (g * e i)) * χ (-(x + y))
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν :=
    fun i => continuous_iterated_integral D U gen hχ hΦ (g * e i)
  simp only [whittaker3]
  have h1 : ∀ x y : AdeleRing (𝓞 ℚ) ℚ,
      (∫ z, comb s c e Φ (upperUnipotent3 x y z * g) * χ (-(x + y))
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) =
        ∑ i ∈ s, c i * ∫ z, Φ (upperUnipotent3 x y z * (g * e i)) * χ (-(x + y))
              ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
    intro x y
    simp only [comb_apply, Finset.sum_mul, mul_assoc]
    exact integral_finset_comb D U gen s c _ fun i _ => hz i x y
  have h2 : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y, ∫ z, comb s c e Φ (upperUnipotent3 x y z * g) * χ (-(x + y))
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) =
        ∑ i ∈ s, c i * ∫ y, ∫ z, Φ (upperUnipotent3 x y z * (g * e i)) * χ (-(x + y))
              ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
    intro x
    simp only [h1]
    exact integral_finset_comb D U gen s c _ fun i _ => hy i x
  simp only [h2]
  exact integral_finset_comb D U gen s c _ fun i _ => hx i

private theorem isCuspidalAlongP21_comb {ι : Type} (s : Finset ι) (c : ι → ℂ) (e : ι → AdelicGL 3 (𝓞 ℚ) ℚ)
    {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ)
    (h : IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) Φ) :
    IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) (comb s c e Φ) := by
  simp only [IsCuspidalAlongP21] at h ⊢
  intro g
  have hy : ∀ (i : ι) (x : AdeleRing (𝓞 ℚ) ℚ),
      Continuous fun y : AdeleRing (𝓞 ℚ) ℚ => Φ (radicalP21 ![x, y] * (g * e i)) := by
    intro i x
    exact hΦ.comp ((continuous_const.radicalP21 continuous_id').mul continuous_const)
  have hx : ∀ i : ι, Continuous fun x : AdeleRing (𝓞 ℚ) ℚ =>
      ∫ y, Φ (radicalP21 ![x, y] * (g * e i)) ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
    intro i
    refine continuous_integral_param D U gen (fun x y => Φ (radicalP21 ![x, y] * (g * e i))) ?_
    exact hΦ.comp ((continuous_fst.radicalP21 continuous_snd).mul continuous_const)
  have h1 : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y, comb s c e Φ (radicalP21 ![x, y] * g) ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) =
        ∑ i ∈ s, c i * ∫ y, Φ (radicalP21 ![x, y] * (g * e i))
              ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
    intro x
    simp only [comb_apply, mul_assoc]
    exact integral_finset_comb D U gen s c _ fun i _ => hy i x
  have h2 : (∫ x, ∑ i ∈ s, c i * ∫ y, Φ (radicalP21 ![x, y] * (g * e i))
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) =
      ∑ i ∈ s, c i * ∫ x, ∫ y, Φ (radicalP21 ![x, y] * (g * e i))
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν :=
    integral_finset_comb D U gen s c _ fun i _ => hx i
  simp only [h1]
  rw [h2]
  simp only [h, mul_zero, Finset.sum_const_zero]

private theorem isCuspidalAlongP12_comb {ι : Type} (s : Finset ι) (c : ι → ℂ) (e : ι → AdelicGL 3 (𝓞 ℚ) ℚ)
    {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ)
    (h : IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) Φ) :
    IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) (comb s c e Φ) := by
  simp only [IsCuspidalAlongP12] at h ⊢
  intro g
  have hy : ∀ (i : ι) (x : AdeleRing (𝓞 ℚ) ℚ),
      Continuous fun y : AdeleRing (𝓞 ℚ) ℚ => Φ (radicalP12 ![x, y] * (g * e i)) := by
    intro i x
    exact hΦ.comp ((continuous_const.radicalP12 continuous_id').mul continuous_const)
  have hx : ∀ i : ι, Continuous fun x : AdeleRing (𝓞 ℚ) ℚ =>
      ∫ y, Φ (radicalP12 ![x, y] * (g * e i)) ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
    intro i
    refine continuous_integral_param D U gen (fun x y => Φ (radicalP12 ![x, y] * (g * e i))) ?_
    exact hΦ.comp ((continuous_fst.radicalP12 continuous_snd).mul continuous_const)
  have h1 : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y, comb s c e Φ (radicalP12 ![x, y] * g) ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) =
        ∑ i ∈ s, c i * ∫ y, Φ (radicalP12 ![x, y] * (g * e i))
              ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
    intro x
    simp only [comb_apply, mul_assoc]
    exact integral_finset_comb D U gen s c _ fun i _ => hy i x
  have h2 : (∫ x, ∑ i ∈ s, c i * ∫ y, Φ (radicalP12 ![x, y] * (g * e i))
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) =
      ∑ i ∈ s, c i * ∫ x, ∫ y, Φ (radicalP12 ![x, y] * (g * e i))
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν :=
    integral_finset_comb D U gen s c _ fun i _ => hx i
  simp only [h1]
  rw [h2]
  simp only [h, mul_zero, Finset.sum_const_zero]

end Laws
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.WhittakerTranslateClosure.Continuous"

section Analytic

private theorem comb_mem {ι : Type} (s : Finset ι) (c : ι → ℂ) (e : ι → AdelicGL 3 (𝓞 ℚ) ℚ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ →
    ℂ) :
    comb s c e Φ ∈ gl3CyclicSubspace Φ :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨e i, rfl⟩)

private theorem continuous_comb {ι : Type} (s : Finset ι) (c : ι → ℂ) (e : ι → AdelicGL 3 (𝓞 ℚ) ℚ)
    {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ) : Continuous (comb s c e Φ) := by
  have h : comb s c e Φ = fun g => ∑ i ∈ s, c i * Φ (g * e i) := funext (comb_apply s c e Φ)
  rw [h]
  exact continuous_finsetSum s fun i _ => continuous_const.mul (hΦ.comp (continuous_mul_const (e i)))

private theorem dualForm_comb {ι : Type} (s : Finset ι) (c : ι → ℂ) (e : ι → AdelicGL 3 (𝓞 ℚ) ℚ) (Φ : AdelicGL 3 (𝓞 ℚ)
    ℚ → ℂ) :
    dualForm (comb s c e Φ) = comb s c (fun i => transposeInv3 (e i)) (dualForm Φ) := by
  funext g
  simp only [dualForm, comb_apply, transposeInv3_mul, transposeInv3_transposeInv3]

private theorem dualForm_dualForm (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : dualForm (dualForm Φ) = Φ := by
  funext g
  simp only [dualForm, transposeInv3_transposeInv3]

end Analytic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.WhittakerTranslateClosure.Continuous"

section Datum

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private def modify (X : CubicInductionData) (v : HeightOneSpectrum (𝓞 ℚ)) (s : Finset (LocalGL3 v)) (c : LocalGL3 v
    → ℂ)
    (W' : LocalGL3 v → ℂ) : CubicInductionData where
  form := comb s c (fun h => localToAdelic3 v h) X.form
  whittaker := comb s c (fun h => localToAdelic3 v h) X.whittaker
  whittakerLoc := by
    classical
    exact Function.update X.whittakerLoc v W'
  whittakerArch := X.whittakerArch
  centralChar := X.centralChar
  dualWhittaker := comb s c (fun h => transposeInv3 (localToAdelic3 v h)) X.dualWhittaker

variable (X : CubicInductionData) (s : Finset (LocalGL3 v)) (c : LocalGL3 v → ℂ) (W' : LocalGL3 v → ℂ)

private theorem modify_form : (modify X v s c W').form = comb s c (fun h => localToAdelic3 v h) X.form := rfl

private theorem modify_whittaker : (modify X v s c W').whittaker = comb s c (fun h => localToAdelic3 v h) X.whittaker
    := rfl

private theorem modify_whittakerArch : (modify X v s c W').whittakerArch = X.whittakerArch := rfl

private theorem modify_centralChar : (modify X v s c W').centralChar = X.centralChar := rfl

private theorem modify_dualWhittaker :
    (modify X v s c W').dualWhittaker = comb s c (fun h => transposeInv3 (localToAdelic3 v h)) X.dualWhittaker := rfl

private theorem modify_whittakerLoc_self : (modify X v s c W').whittakerLoc v = W' := by
  simp only [modify, Function.update_self]

private theorem modify_whittakerLoc_of_ne {u : HeightOneSpectrum (𝓞 ℚ)} (hu : u ≠ v) :
    (modify X v s c W').whittakerLoc u = X.whittakerLoc u := by
  classical
  simp only [modify, Function.update_of_ne hu]

private theorem hasSum_comb {Φ W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hX : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) (Φ g))
    {ι : Type} (t : Finset ι) (a : ι → ℂ) (e : ι → AdelicGL 3 (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    HasSum (fun i : MirabolicIndex ℚ => comb t a e W (mirabolicTranslate i * g)) (comb t a e Φ g) := by
  simp only [comb_apply, mul_assoc]
  exact hasSum_sum fun j _ => (hX (g * e j)).mul_left (a j)

end Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.WhittakerTranslateClosure.Continuous"

end WhittakerTranslateClosure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.WhittakerTranslateClosure.Continuous P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.WhittakerTranslateClosure"

open WhittakerTranslateClosure in

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S X)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker)
    (hcontW' : Continuous X.dualWhittaker)
    (hmaj : IsGaugeMajorised3 ℚ X.whittaker) (hmaj' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g)
    (W' : LocalGL3 v → ℂ) (hW' : W' ∈ gl3CyclicSubspace (X.whittakerLoc v)) :
    ∃ Y : CubicInductionData,
      IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S Y ∧
        Y.whittakerLoc v = W' ∧ (∀ u, u ≠ v → Y.whittakerLoc u = X.whittakerLoc u) ∧
          Y.whittakerArch = X.whittakerArch ∧ Y.centralChar = X.centralChar ∧
            Continuous Y.form ∧ Continuous Y.whittaker ∧ Continuous Y.dualWhittaker ∧
              IsGaugeMajorised3 ℚ Y.whittaker ∧ IsGaugeMajorised3 ℚ Y.dualWhittaker := by
  classical

  have hW'span : W' ∈ Submodule.span ℂ
      (Set.range fun h : LocalGL3 v => gl3AmbientRightTranslate (R := ℂ) h (X.whittakerLoc v)) := hW'
  obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hW'span
  have hW'eq : W' = ∑ h ∈ cf.support, cf h • gl3AmbientRightTranslate (R := ℂ) h (X.whittakerLoc v) := by
    rw [← hcf]
    rfl
  have hW'apply : ∀ x : LocalGL3 v, W' x = ∑ h ∈ cf.support, cf h * X.whittakerLoc v (x * h) := by
    intro x
    rw [hW'eq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gl3AmbientRightTranslate_apply]

  have hmemW : (modify X v cf.support cf W').whittaker ∈ gl3CyclicSubspace X.whittaker := by
    rw [modify_whittaker]
    exact comb_mem _ _ _ _
  have hmemW' : (modify X v cf.support cf W').dualWhittaker ∈ gl3CyclicSubspace X.dualWhittaker := by
    rw [modify_dualWhittaker]
    exact comb_mem _ _ _ _
  have hYcont : Continuous (modify X v cf.support cf W').form := by
    rw [modify_form]
    exact continuous_comb _ _ _ hcont
  have hYcontW : Continuous (modify X v cf.support cf W').whittaker := by
    rw [modify_whittaker]
    exact continuous_comb _ _ _ hcontW
  have hYcontW' : Continuous (modify X v cf.support cf W').dualWhittaker := by
    rw [modify_dualWhittaker]
    exact continuous_comb _ _ _ hcontW'
  have hYmaj : IsGaugeMajorised3 ℚ (modify X v cf.support cf W').whittaker :=
    isGaugeMajorised3_of_mem_gl3CyclicSubspace ℚ hmaj hmemW
  have hYmaj' : IsGaugeMajorised3 ℚ (modify X v cf.support cf W').dualWhittaker :=
    isGaugeMajorised3_of_mem_gl3CyclicSubspace ℚ hmaj' hmemW'
  have hYexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum
      (fun i : MirabolicIndex ℚ => (modify X v cf.support cf W').whittaker (mirabolicTranslate i * g))
      ((modify X v cf.support cf W').form g) := by
    intro g
    rw [modify_whittaker, modify_form]
    exact hasSum_comb hX.expansion cf.support cf _ g
  have hYdualexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum
      (fun i : MirabolicIndex ℚ => (modify X v cf.support cf W').dualWhittaker (mirabolicTranslate i * g))
      (dualForm (modify X v cf.support cf W').form g) := by
    intro g
    rw [modify_dualWhittaker, modify_form, dualForm_comb]
    exact hasSum_comb hX.dual_expansion cf.support cf _ g
  have hYform : (modify X v cf.support cf W').form = fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      ∑' i : MirabolicIndex ℚ, (modify X v cf.support cf W').whittaker (mirabolicTranslate i * g) :=
    funext fun g => ((hYexp g).tsum_eq).symm
  have hwk4 := summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 _ hYcontW hYmaj
  have hwk4' := summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 _ hYcontW' hYmaj'
  have hvne : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ∉ S → u ≠ v := fun u hu huv => hu (huv ▸ hv)
  refine ⟨modify X v cf.support cf W', ?_, modify_whittakerLoc_self X cf.support cf W',
    fun u hu => modify_whittakerLoc_of_ne X cf.support cf W' hu, rfl, rfl, hYcont, hYcontW, hYcontW', hYmaj, hYmaj'⟩
  refine
    { automorphic := ?_, central := ?_, centralChar_ideleClass := hX.centralChar_ideleClass, cuspidalP21 := ?_,
      cuspidalP12 := ?_, whittaker_eq := ?_, whittaker_law := isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace ψ
          hX.whittaker_law hmemW,
      expansion := hYexp, whittakerLoc_law := ?_, factorizable := ?_, spherical := ?_, levelInvariant := ?_,
      multOne := ?_, moderateGrowth := ?_, kFinite := hX.kFinite, iotaMoments := ?_,
      whittakerHalfPlane := hwk4.2.2.2.1, dualWhittaker_eq := ?_,
      dualWhittaker_law := isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace ψ⁻¹ hX.dualWhittaker_law hmemW',
          dual_expansion := hYdualexp,
      dual_iotaMoments := ?_, dual_whittakerHalfPlane := hwk4'.2.2.2.1 }
  ·
    intro γ g
    simp only [modify_form, comb_apply, mul_assoc, hX.automorphic]
  ·
    intro z g
    simp only [modify_form, modify_centralChar, comb_apply, mul_assoc, hX.central, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  ·
    rw [modify_form]
    exact isCuspidalAlongP21_comb D U gen cf.support cf _ hcont hX.cuspidalP21
  ·
    rw [modify_form]
    exact isCuspidalAlongP12_comb D U gen cf.support cf _ hcont hX.cuspidalP12
  ·
    intro g
    rw [modify_whittaker, modify_form, whittaker3_comb D U gen hψ cf.support cf _ hcont g]
    simp only [comb_apply]
    exact Finset.sum_congr rfl fun h _ => by rw [hX.whittaker_eq]
  ·
    intro u
    by_cases hu : u = v
    · subst hu
      rw [modify_whittakerLoc_self]
      exact isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace _ (hX.whittakerLoc_law _) hW'
    · rw [modify_whittakerLoc_of_ne X cf.support cf W' hu]
      exact hX.whittakerLoc_law u
  ·
    intro g T hST hg
    have hvT : v ∈ T := hST v hv
    have hcomp : ∀ h : LocalGL3 v, ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v →
        componentAt3 (𝓞 ℚ) ℚ u (g * localToAdelic3 v h) = componentAt3 (𝓞 ℚ) ℚ u g := by
      intro h u hu
      rw [map_mul, componentAt3_localToAdelic3_of_ne v h hu, mul_one]
    have hcompv : ∀ h : LocalGL3 v,
        componentAt3 (𝓞 ℚ) ℚ v (g * localToAdelic3 v h) = componentAt3 (𝓞 ℚ) ℚ v g * h := by
      intro h
      rw [map_mul, componentAt3_localToAdelic3_self]
    have harch : ∀ h : LocalGL3 v,
        archComponent3 (𝓞 ℚ) ℚ (g * localToAdelic3 v h) = archComponent3 (𝓞 ℚ) ℚ g := by
      intro h
      rw [map_mul, archComponent3_localToAdelic3, mul_one]
    have hXfac : ∀ h : LocalGL3 v, X.whittaker (g * localToAdelic3 v h) =
        X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
          (X.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v g * h) *
            ∏ u ∈ T.erase v, X.whittakerLoc u (componentAt3 (𝓞 ℚ) ℚ u g)) := by
      intro h
      have hg' : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ∉ T →
          componentAt3 (𝓞 ℚ) ℚ u (g * localToAdelic3 v h) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ u := by
        intro u hu
        rw [hcomp h u fun huv => hu (huv ▸ hvT)]
        exact hg u hu
      rw [hX.factorizable (g * localToAdelic3 v h) T hST hg', harch h, ← Finset.mul_prod_erase T _ hvT, hcompv h]
      congr 2
      exact Finset.prod_congr rfl fun u hu => by rw [hcomp h u (Finset.ne_of_mem_erase hu)]
    have hprod : ∏ u ∈ T.erase v, (modify X v cf.support cf W').whittakerLoc u (componentAt3 (𝓞 ℚ) ℚ u g) =
        ∏ u ∈ T.erase v, X.whittakerLoc u (componentAt3 (𝓞 ℚ) ℚ u g) :=
      Finset.prod_congr rfl fun u hu => by
        rw [modify_whittakerLoc_of_ne X cf.support cf W' (Finset.ne_of_mem_erase hu)]
    rw [modify_whittaker, modify_whittakerArch, ← Finset.mul_prod_erase T _ hvT, hprod, modify_whittakerLoc_self,
      hW'apply]
    simp only [comb_apply]
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by rw [hXfac h]; ring
  ·
    intro u hu
    rw [modify_whittakerLoc_of_ne X cf.support cf W' (hvne u hu)]
    exact hX.spherical u hu
  ·
    intro u hu hram
    rw [modify_whittakerLoc_of_ne X cf.support cf W' (hvne u hu)]
    exact hX.levelInvariant u hu hram
  ·
    intro u
    by_cases hu : u = v
    · subst hu
      rw [modify_whittakerLoc_self]
      refine hasWhittakerMultOne_of_mem_gl3CyclicSubspace_of_isOpen _ _ ?_ _ hsm (hX.multOne _) W' hW'
      unfold psiLoc
      exact hψ.comp (NumberField.StandardAddChar.continuous_adeleSingleAt ℚ _)
    · rw [modify_whittakerLoc_of_ne X cf.support cf W' hu]
      exact hX.multOne u
  ·
    rw [hYform]
    exact hwk4.2.1
  ·
    exact hasIotaMoments_of_hasSum_mirabolicTranslate_of_isGaugeMajorised3 _ _ _ hYcontW hYmaj hYcontW' hYmaj'
        hYexp hYdualexp
  ·
    intro g
    rw [modify_dualWhittaker, modify_form, dualForm_comb,
      whittaker3_comb D U gen (continuous_inv_char hψ) cf.support cf _ (continuous_dualForm hcont) g]
    simp only [comb_apply]
    exact Finset.sum_congr rfl fun h _ => by rw [hX.dualWhittaker_eq]
  ·
    refine hasIotaMoments_of_hasSum_mirabolicTranslate_of_isGaugeMajorised3 _ _ _ hYcontW' hYmaj' hYcontW hYmaj
        hYdualexp ?_
    rw [dualForm_dualForm]
    exact hYexp

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.WhittakerTranslateClosure.Continuous P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.WhittakerTranslateClosure"

end S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen (solution)
