-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/392efe67-3bd8-52b7-a103-b4bbd9c04fdb

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_toL2_eq_zero_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_psiQ
import Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_WhittakerBlock_isHaarMeasure_unipotentHaar3
import Theorems.Thm_WhittakerBlock_isMulRightInvariant_unipotentHaar3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.fnTwist3_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support"
p2m_attr_erase "simp" "RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction.SlabL2
open LanglandsTunnell.CubicInduction
open scoped ENNReal InnerProductSpace
attribute [local instance] NumberField.AdelicHaar.glBorel

section LeviSections

noncomputable section

namespace MirabolicLeviFibration

section Furniture

private def bottomRow (g : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) : Fin 3 → AdeleRing (𝓞 ℚ) ℚ :=
  fun j => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j

private theorem bottomRow_mul (g h : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) :
    bottomRow (g * h) = fun j => ∑ k, bottomRow g k * (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) k j := by
  funext j
  simp [bottomRow, Units.val_mul, Matrix.mul_apply]

private def e₃ : Fin 3 → AdeleRing (𝓞 ℚ) ℚ := fun j => if j = 2 then 1 else 0

private theorem bottomRow_one : bottomRow (1 : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) = e₃ := by
  funext j
  simp [bottomRow, e₃, Matrix.one_apply, eq_comm]

private def mirabolic : Subgroup (LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) where
  carrier := {g | bottomRow g = e₃}
  one_mem' := bottomRow_one
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [bottomRow_mul, hg]
    funext j
    have := congrFun hh j
    simp only [bottomRow] at this
    simp [e₃, this]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h1 : bottomRow (g * g⁻¹) = e₃ := by rw [mul_inv_cancel, bottomRow_one]
    rw [bottomRow_mul, hg] at h1
    funext j
    have := congrFun h1 j
    simpa [e₃, Fin.sum_univ_three, bottomRow] using this

private theorem continuous_bottomRow : Continuous bottomRow := by
  refine continuous_pi fun j => ?_
  exact (continuous_apply j).comp ((continuous_apply (2 : Fin 3)).comp
    (Units.continuous_val (M := Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))))

private theorem isClosed_mirabolic :
    IsClosed ((mirabolic : Subgroup (LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ)) :
      Set (LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ)) :=
  isClosed_singleton.preimage continuous_bottomRow
end Furniture

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private abbrev evalHom (q : HeightOneSpectrum (𝓞 ℚ)) : AdeleRing (𝓞 ℚ) ℚ →+* q.adicCompletion ℚ :=
  (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ q).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private def leviRow (p : ↥mirabolic) : Fin 2 → AdeleRing (𝓞 ℚ) ℚ :=
  fun i => ((p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
    1 (Fin.castSucc i)

private def e₂ : Fin 2 → AdeleRing (𝓞 ℚ) ℚ := fun i => if i = 1 then 1 else 0

private def LeviPrimitiveAt (q : HeightOneSpectrum (𝓞 ℚ)) (r : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  (∀ i, evalHom q (r i) ∈ q.adicCompletionIntegers ℚ) ∧ ∃ i, Valued.v (evalHom q (r i)) = 1

private def LeviNonzeroAt (q : HeightOneSpectrum (𝓞 ℚ)) (r : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  ∃ i, evalHom q (r i) ≠ 0

private def LeviNonzeroArch (r : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  ∃ i, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (r i) ≠ 0

private def goodLeviRows (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) :=
  {r | (∀ q, q ∉ S → LeviPrimitiveAt q r) ∧ (∀ q ∈ S, LeviNonzeroAt q r) ∧ LeviNonzeroArch r}

private def leviRowDomain : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) :=
  {r | (∀ q, LeviNonzeroAt q r) ∧ LeviNonzeroArch r ∧ ∀ᶠ q in Filter.cofinite, LeviPrimitiveAt q r}

private abbrev leviHaar : Measure (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) :=
  Measure.pi fun _ : Fin 2 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

private def leviAct (r : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) (p : ↥mirabolic) : Fin 2 → AdeleRing (𝓞 ℚ) ℚ :=
  fun j => ∑ i : Fin 2, r i *
    ((p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
      (Fin.castSucc i) (Fin.castSucc j)

end RowSets

section Modulus

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private def modulus (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g))

private theorem modulus_pos (g : AdelicGL 3 (𝓞 ℚ) ℚ) : 0 < modulus g :=
  ENNReal.ofReal_pos.2 (NumberField.TateGlobal.ideleNorm_pos _)

private theorem modulus_ne_zero (g : AdelicGL 3 (𝓞 ℚ) ℚ) : modulus g ≠ 0 :=
  (modulus_pos g).ne'

private theorem modulus_ne_top (g : AdelicGL 3 (𝓞 ℚ) ℚ) : modulus g ≠ ⊤ :=
  ENNReal.ofReal_ne_top

private theorem modulus_mul (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    modulus (g * h) = modulus g * modulus h := by
  unfold modulus
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul,
    ENNReal.ofReal_mul (NumberField.TateGlobal.ideleNorm_pos _).le]

private theorem modulus_one : modulus (1 : AdelicGL 3 (𝓞 ℚ) ℚ) = 1 := by
  have h := modulus_mul (1 : AdelicGL 3 (𝓞 ℚ) ℚ) 1
  rw [one_mul] at h
  have h2 : modulus (1 : AdelicGL 3 (𝓞 ℚ) ℚ) * modulus 1 = modulus 1 * 1 := by
    rw [mul_one]
    exact h.symm
  exact (ENNReal.mul_right_inj (modulus_ne_zero 1) (modulus_ne_top 1)).1 h2

private theorem modulus_inv (g : AdelicGL 3 (𝓞 ℚ) ℚ) : modulus g⁻¹ = (modulus g)⁻¹ := by
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  rw [← modulus_mul, inv_mul_cancel, modulus_one]

private theorem modulus_mul_inv_mul (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    modulus g * (modulus g)⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (modulus_ne_zero g) (modulus_ne_top g)

private theorem inv_mul_modulus (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (modulus g)⁻¹ * modulus g = 1 :=
  ENNReal.inv_mul_cancel (modulus_ne_zero g) (modulus_ne_top g)

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel in
private theorem measurable_modulus : Measurable modulus :=
  ENNReal.measurable_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp
    Matrix.GeneralLinearGroup.continuous_det).measurable

private def mirabolicChart (p : ↥mirabolic) :
    (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) :=
  (Matrix.GeneralLinearGroup.det (p : AdelicGL 3 (𝓞 ℚ) ℚ),
    (((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 0 1,
      (((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 0 2,
        ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 1 2)))

end Modulus

section GenericDevice

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] {Y : Type} [MeasurableSpace Y]

private def fibMeasure (P : Subgroup G) (sec : Y → G) (δ : G → ℝ≥0∞) (μP : Measure ↥P) (lam : Measure Y)
    (R : Set Y) : Measure G :=
  Measure.map (fun z : Y × ↥P => (z.2 : G) * sec z.1)
    (((lam.restrict R).withDensity fun x => (δ (sec x))⁻¹).prod μP)

end GenericDevice

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private def PrimitiveAt (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  (∀ j, evalHom p (x j) ∈ p.adicCompletionIntegers ℚ) ∧ ∃ j, Valued.v (evalHom p (x j)) = 1

private def NonzeroAt (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  ∃ j, evalHom p (x j) ≠ 0

private def NonzeroArch (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  ∃ j, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j) ≠ 0

private def explicitRows (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  {x | (∀ p, p ∉ S → PrimitiveAt p x) ∧ (∀ p ∈ S, NonzeroAt p x) ∧ NonzeroArch x}

private def rowDomain : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  {x | (∀ p, NonzeroAt p x) ∧ NonzeroArch x ∧ ∀ᶠ p in Filter.cofinite, PrimitiveAt p x}

end RowSets

section ShellCondition

section Shell

private def ShellCond (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
    ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
      k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k

end Shell

end ShellCondition

section RowsOfTheShell

section ShellRows

private theorem primitiveAt_bottomRow_of_shellCond (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : ShellCond S g) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∉ S) : PrimitiveAt p (bottomRow g) := by
  obtain ⟨x, y, z, k, hk, hgk⟩ := hg p hp
  rw [mem_localMaximalCompact3_iff] at hk

  have hrow : ∀ j : Fin 3, evalHom p (bottomRow g j) = (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j := by
    intro j
    have h1 : evalHom p (bottomRow g j) =
        ((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))
          2 j := rfl
    rw [h1, hgk, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, upperUnipotent3_coe]
    simp
  refine ⟨fun j => ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hrow]
    exact hk.1 2 j
  ·
    by_contra hne
    have hlt : ∀ j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j) < 1 := fun j =>
      lt_of_le_of_ne (hk.1 2 j) fun h => hne ⟨j, by rw [hrow]; exact h⟩
    have hkk : ∑ j : Fin 3, (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j *
        ((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) j 2 = 1 := by
      have h := congrFun (congrFun k.mul_inv 2) 2
      rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h
    have hone : Valued.v (∑ j : Fin 3, (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j *
        ((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) j 2) < 1 := by
      refine Valuation.map_sum_lt Valued.v one_ne_zero fun j _ => ?_
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hk.2 j 2)) (hlt j)
    rw [hkk, map_one] at hone
    exact lt_irrefl _ hone

private theorem nonzeroAt_bottomRow (g : AdelicGL 3 (𝓞 ℚ) ℚ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    NonzeroAt p (bottomRow g) := by
  by_contra hne
  have h0 : ∀ j : Fin 3,
      ((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j
        = 0 := fun j => by
    by_contra h
    exact hne ⟨j, h⟩
  have hdet := Matrix.det_eq_zero_of_row_eq_zero 2 h0
  rw [← Matrix.GeneralLinearGroup.val_det_apply] at hdet
  exact (Matrix.GeneralLinearGroup.det (componentAt3 (𝓞 ℚ) ℚ p g)).ne_zero hdet

private theorem nonzeroArch_bottomRow (g : AdelicGL 3 (𝓞 ℚ) ℚ) : NonzeroArch (bottomRow g) := by
  by_contra hne
  have h0 : ∀ j : Fin 3,
      ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
        2 j = 0 := fun j => by
    by_contra h
    exact hne ⟨j, h⟩
  have hdet := Matrix.det_eq_zero_of_row_eq_zero 2 h0
  rw [← Matrix.GeneralLinearGroup.val_det_apply] at hdet
  exact (Matrix.GeneralLinearGroup.det (archComponent3 (𝓞 ℚ) ℚ g)).ne_zero hdet

private theorem bottomRow_mem_explicitRows_of_shellCond (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : ShellCond S g) : bottomRow g ∈ explicitRows S := by
  exact ⟨fun p hp => primitiveAt_bottomRow_of_shellCond S hg p hp, fun p _ => nonzeroAt_bottomRow g p,
    nonzeroArch_bottomRow g⟩

end ShellRows

end RowsOfTheShell

section SectionAndRowSets

section SectionHeads

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

open scoped RestrictedProduct

open Topology

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

private theorem arch_mul_apply (a b : 𝔸) (w : InfinitePlace ℚ) : (a * b).1 w = a.1 w * b.1 w := rfl

private theorem arch_add_apply (a b : 𝔸) (w : InfinitePlace ℚ) : (a + b).1 w = a.1 w + b.1 w := rfl

private theorem arch_one_apply (w : InfinitePlace ℚ) : (1 : 𝔸).1 w = 1 := rfl

private theorem arch_zero_apply (w : InfinitePlace ℚ) : (0 : 𝔸).1 w = 0 := rfl

private theorem fin_mul_apply (a b : 𝔸) (p : HeightOneSpectrum (𝓞 ℚ)) : (a * b).2 p = a.2 p * b.2 p := rfl

private theorem fin_add_apply (a b : 𝔸) (p : HeightOneSpectrum (𝓞 ℚ)) : (a + b).2 p = a.2 p + b.2 p := rfl

private theorem fin_one_apply (p : HeightOneSpectrum (𝓞 ℚ)) : (1 : 𝔸).2 p = 1 := rfl

private theorem fin_zero_apply (p : HeightOneSpectrum (𝓞 ℚ)) : (0 : 𝔸).2 p = 0 := rfl

private theorem ext_of_places {a b : 𝔸} (h₁ : ∀ w, a.1 w = b.1 w) (h₂ : ∀ p, a.2 p = b.2 p) : a = b :=
  Prod.ext (funext h₁) (FiniteAdeleRing.ext ℚ h₂)

private theorem evalHom_eq (p : HeightOneSpectrum (𝓞 ℚ)) (a : 𝔸) : evalHom p a = a.2 p := rfl

private theorem adeleArch_eq (a : 𝔸) : AdelicLevel.adeleArch (𝓞 ℚ) ℚ a = a.1 := rfl

private def rowAt (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) : Fin 3 → p.adicCompletion ℚ := fun j => (x j).2 p

private def rowArch (w : InfinitePlace ℚ) (x : Fin 3 → 𝔸) : Fin 3 → w.Completion := fun j => (x j).1 w

private theorem rowAt_apply (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) (j : Fin 3) : rowAt p x j = (x j).2 p := rfl

private theorem rowArch_apply (w : InfinitePlace ℚ) (x : Fin 3 → 𝔸) (j : Fin 3) : rowArch w x j = (x j).1 w := rfl

private theorem mem_rowDomain {x : Fin 3 → 𝔸} :
    x ∈ rowDomain ↔ (∀ p, NonzeroAt p x) ∧ NonzeroArch x ∧ ∀ᶠ p in Filter.cofinite, PrimitiveAt p x :=
  Iff.rfl

private theorem primitiveAt_iff (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) :
    PrimitiveAt p x ↔ (∀ j, Valued.v (rowAt p x j) ≤ 1) ∧ ∃ j, Valued.v (rowAt p x j) = 1 :=
  Iff.rfl

private theorem nonzeroAt_iff (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) : NonzeroAt p x ↔ ∃ j, rowAt p x j ≠ 0 :=
  Iff.rfl

private theorem exists_rowArch_ne_zero {x : Fin 3 → 𝔸} (hx : NonzeroArch x) (w : InfinitePlace ℚ) :
    ∃ j, rowArch w x j ≠ 0 := by
  obtain ⟨j, hj⟩ := hx
  refine ⟨j, fun h0 => hj ?_⟩
  rw [adeleArch_eq]
  funext w'
  rw [Subsingleton.elim w' w]
  exact h0

private theorem nonzeroArch_of_rowArch {x : Fin 3 → 𝔸} {w : InfinitePlace ℚ} (h : ∃ j, rowArch w x j ≠ 0) :
    NonzeroArch x := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun h0 => hj (by rw [rowArch_apply, ← adeleArch_eq, h0]; rfl)⟩

private def preferredIndex (P : Fin 3 → Prop) [DecidablePred P] : Fin 3 :=
  if P 2 then 2 else if P 1 then 1 else 0

private theorem preferredIndex_spec {P : Fin 3 → Prop} [DecidablePred P] (h : ∃ j, P j) : P (preferredIndex P) := by
  unfold preferredIndex
  split_ifs with h2 h1
  · exact h2
  · exact h1
  · obtain ⟨j, hj⟩ := h
    fin_cases j
    · exact hj
    · exact absurd hj h1
    · exact absurd hj h2

private def unitPattern (p : HeightOneSpectrum (𝓞 ℚ)) (y : Fin 3 → p.adicCompletion ℚ) : Fin 3 :=
  preferredIndex fun j => Valued.v (y j) = 1

private theorem valued_unitPattern (p : HeightOneSpectrum (𝓞 ℚ)) {y : Fin 3 → p.adicCompletion ℚ}
    (h : ∃ j, Valued.v (y j) = 1) : Valued.v (y (unitPattern p y)) = 1 :=
  preferredIndex_spec h

open scoped Classical in

private def finitePivot (p : HeightOneSpectrum (𝓞 ℚ)) (y : Fin 3 → p.adicCompletion ℚ) : Fin 3 :=
  if ∃ j, Valued.v (y j) = 1 then unitPattern p y else preferredIndex fun j => y j ≠ 0

private theorem finitePivot_of_exists_unit (p : HeightOneSpectrum (𝓞 ℚ)) {y : Fin 3 → p.adicCompletion ℚ}
    (h : ∃ j, Valued.v (y j) = 1) : finitePivot p y = unitPattern p y := by
  unfold finitePivot
  rw [if_pos h]

private theorem valued_finitePivot (p : HeightOneSpectrum (𝓞 ℚ)) {y : Fin 3 → p.adicCompletion ℚ}
    (h : ∃ j, Valued.v (y j) = 1) : Valued.v (y (finitePivot p y)) = 1 := by
  rw [finitePivot_of_exists_unit p h]
  exact valued_unitPattern p h

open scoped Classical in
private theorem finitePivot_ne_zero (p : HeightOneSpectrum (𝓞 ℚ)) {y : Fin 3 → p.adicCompletion ℚ} (h : ∃ j, y j ≠ 0) :
    y (finitePivot p y) ≠ 0 := by
  unfold finitePivot
  split_ifs with hu
  · intro h0
    have h1 := valued_unitPattern p hu
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  · exact preferredIndex_spec h

open scoped Classical in

private def archPivot (w : InfinitePlace ℚ) (y : Fin 3 → w.Completion) : Fin 3 :=
  preferredIndex fun j => y j ≠ 0

open scoped Classical in
private theorem archPivot_ne_zero (w : InfinitePlace ℚ) {y : Fin 3 → w.Completion} (h : ∃ j, y j ≠ 0) :
    y (archPivot w y) ≠ 0 :=
  preferredIndex_spec h

private def pivotIdempotent (x : Fin 3 → 𝔸) (j : Fin 3) : 𝔸 :=
  (fun w => if archPivot w (rowArch w x) = j then 1 else 0,
    ⟨fun p => if finitePivot p (rowAt p x) = j then 1 else 0, Filter.Eventually.of_forall fun p => by
      by_cases h : finitePivot p (rowAt p x) = j
      · simp only [h, if_true, SetLike.mem_coe]
        exact one_mem _
      · simp only [h, if_false, SetLike.mem_coe]
        exact zero_mem _⟩)

private theorem pivotIdempotent_arch (x : Fin 3 → 𝔸) (j : Fin 3) (w : InfinitePlace ℚ) :
    (pivotIdempotent x j).1 w = if archPivot w (rowArch w x) = j then 1 else 0 := rfl

private theorem pivotIdempotent_fin (x : Fin 3 → 𝔸) (j : Fin 3) (p : HeightOneSpectrum (𝓞 ℚ)) :
    (pivotIdempotent x j).2 p = if finitePivot p (rowAt p x) = j then 1 else 0 := rfl

open scoped Classical in

private def pivotInverse (x : Fin 3 → 𝔸) : 𝔸 :=
  if hx : x ∈ rowDomain then
    (fun w => (rowArch w x (archPivot w (rowArch w x)))⁻¹,
      ⟨fun p => (rowAt p x (finitePivot p (rowAt p x)))⁻¹, by
        filter_upwards [hx.2.2] with p hp
        simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀,
          valued_finitePivot p ((primitiveAt_iff p x).mp hp).2, inv_one, le_refl]⟩)
  else 0

private theorem pivotInverse_arch {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) (w : InfinitePlace ℚ) :
    (pivotInverse x).1 w = (rowArch w x (archPivot w (rowArch w x)))⁻¹ := by
  unfold pivotInverse
  rw [dif_pos hx]

private theorem pivotInverse_fin {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) (p : HeightOneSpectrum (𝓞 ℚ)) :
    (pivotInverse x).2 p = (rowAt p x (finitePivot p (rowAt p x)))⁻¹ := by
  unfold pivotInverse
  rw [dif_pos hx]
  rfl

private theorem pivotIdempotent_mul_self (x : Fin 3 → 𝔸) (j : Fin 3) :
    pivotIdempotent x j * pivotIdempotent x j = pivotIdempotent x j :=
  ext_of_places
    (fun w => by
      rw [arch_mul_apply, pivotIdempotent_arch]
      split_ifs <;> simp)
    (fun p => by
      rw [fin_mul_apply, pivotIdempotent_fin]
      split_ifs <;> simp)

private theorem pivotIdempotent_mul_of_ne (x : Fin 3 → 𝔸) {i j : Fin 3} (hij : i ≠ j) :
    pivotIdempotent x i * pivotIdempotent x j = 0 :=
  ext_of_places
    (fun w => by
      rw [arch_mul_apply, arch_zero_apply, pivotIdempotent_arch, pivotIdempotent_arch]
      split_ifs with hi hj
      · exact absurd (hi.symm.trans hj) hij
      all_goals simp)
    (fun p => by
      rw [fin_mul_apply, fin_zero_apply, pivotIdempotent_fin, pivotIdempotent_fin]
      split_ifs with hi hj
      · exact absurd (hi.symm.trans hj) hij
      all_goals simp)

private theorem pivotIdempotent_sum (x : Fin 3 → 𝔸) :
    pivotIdempotent x 0 + pivotIdempotent x 1 + pivotIdempotent x 2 = 1 :=
  ext_of_places
    (fun w => by
      rw [arch_add_apply, arch_add_apply, arch_one_apply, pivotIdempotent_arch, pivotIdempotent_arch,
        pivotIdempotent_arch]
      generalize archPivot w (rowArch w x) = k
      fin_cases k <;> simp)
    (fun p => by
      rw [fin_add_apply, fin_add_apply, fin_one_apply, pivotIdempotent_fin, pivotIdempotent_fin, pivotIdempotent_fin]
      generalize finitePivot p (rowAt p x) = k
      fin_cases k <;> simp)

private theorem pivotIdempotent_mul_pivotInverse {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) (j : Fin 3) :
    pivotIdempotent x j * (x j * pivotInverse x) = pivotIdempotent x j :=
  ext_of_places
    (fun w => by
      rw [arch_mul_apply, arch_mul_apply, pivotIdempotent_arch, pivotInverse_arch hx]
      split_ifs with h
      · have hne := archPivot_ne_zero w (exists_rowArch_ne_zero hx.2.1 w)
        rw [h] at hne ⊢
        rw [one_mul]
        exact mul_inv_cancel₀ hne
      · exact zero_mul _)
    (fun p => by
      rw [fin_mul_apply, fin_mul_apply, pivotIdempotent_fin, pivotInverse_fin hx]
      split_ifs with h
      · have hne := finitePivot_ne_zero p ((nonzeroAt_iff p x).mp (hx.1 p))
        rw [h] at hne ⊢
        rw [one_mul]
        exact mul_inv_cancel₀ hne
      · exact zero_mul _)

section Chart

variable {A : Type*} [CommRing A]

private def chartMatrix (e y : Fin 3 → A) : Matrix (Fin 3) (Fin 3) A :=
  !![e 2 + e 1, e 0, 0; 0, e 2, e 1 + e 0; y 0, y 1, y 2]

private def chartInverse (e y : Fin 3 → A) (d : A) : Matrix (Fin 3) (Fin 3) A :=
  !![e 2 + e 1 - e 0 * (y 1 * d), -(e 0 * (y 2 * d)), e 0 * d;
    e 0 - e 1 * (y 0 * d), e 2 - e 1 * (y 2 * d), e 1 * d;
    -(e 2 * (y 0 * d)), e 1 + e 0 - e 2 * (y 1 * d), e 2 * d]

private theorem chartMatrix_mul_chartInverse (e y : Fin 3 → A) (d : A) (h00 : e 0 * e 0 = e 0)
    (h11 : e 1 * e 1 = e 1) (h22 : e 2 * e 2 = e 2) (h01 : e 0 * e 1 = 0) (h02 : e 0 * e 2 = 0) (h12 : e 1 * e 2 = 0)
    (hsum : e 0 + e 1 + e 2 = 1) (hp0 : e 0 * (y 0 * d) = e 0) (hp1 : e 1 * (y 1 * d) = e 1)
    (hp2 : e 2 * (y 2 * d) = e 2) : chartMatrix e y * chartInverse e y d = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartMatrix, chartInverse, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
    | linear_combination h22 + h11 + h00 + 2 * h12 - (y 1 * d) * h02 - (y 1 * d) * h01 - (y 0 * d) * h01 + hsum
    | linear_combination (1 - y 2 * d) * h02 - 2 * (y 2 * d) * h01
    | linear_combination d * h02 + 2 * d * h01
    | linear_combination (1 - y 0 * d) * h02 - 2 * (y 0 * d) * h12
    | linear_combination h22 + h11 + h00 + 2 * h01 - (y 2 * d) * h12 - (y 1 * d) * h12 - (y 1 * d) * h02 + hsum
    | linear_combination 2 * d * h12 + d * h02
    | linear_combination (-(y 1)) * hp0 - y 0 * hp1 - y 0 * hp2
    | linear_combination (-(y 2)) * hp0 - y 2 * hp1 - y 1 * hp2
    | linear_combination hp0 + hp1 + hp2 + hsum

private theorem chartMatrix_map {B : Type*} [CommRing B] (f : A →+* B) (e y : Fin 3 → A) :
    (chartMatrix e y).map f = chartMatrix (f ∘ e) (f ∘ y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartMatrix]

private theorem chartInverse_map {B : Type*} [CommRing B] (f : A →+* B) (e y : Fin 3 → A) (d : A) :
    (chartInverse e y d).map f = chartInverse (f ∘ e) (f ∘ y) (f d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartInverse]

private theorem chartMatrix_apply_mem {S : Type*} [SetLike S A] [SubringClass S A] (O : S) {e y : Fin 3 → A}
    (he : ∀ j, e j ∈ O) (hy : ∀ j, y j ∈ O) (i j : Fin 3) : chartMatrix e y i j ∈ O := by
  fin_cases i <;> fin_cases j <;> simp [chartMatrix] <;>
    first
    | exact add_mem (he _) (he _)
    | exact he _
    | exact hy _

private theorem chartInverse_apply_mem {S : Type*} [SetLike S A] [SubringClass S A] (O : S) {e y : Fin 3 → A} {d : A}
    (he : ∀ j, e j ∈ O) (hy : ∀ j, y j ∈ O) (hd : d ∈ O) (i j : Fin 3) : chartInverse e y d i j ∈ O := by
  fin_cases i <;> fin_cases j <;> simp [chartInverse] <;>
    first
    | exact sub_mem (add_mem (he _) (he _)) (mul_mem (he _) (mul_mem (hy _) hd))
    | exact mul_mem (he _) (mul_mem (hy _) hd)
    | exact neg_mem (mul_mem (he _) (mul_mem (hy _) hd))
    | exact mul_mem (he _) hd
    | exact sub_mem (he _) (mul_mem (he _) (mul_mem (hy _) hd))

end Chart

private theorem chartMatrix_mul_chartInverse_pivot {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) :
    chartMatrix (pivotIdempotent x) x * chartInverse (pivotIdempotent x) x (pivotInverse x) = 1 :=
  chartMatrix_mul_chartInverse _ _ _ (pivotIdempotent_mul_self x 0) (pivotIdempotent_mul_self x 1)
    (pivotIdempotent_mul_self x 2) (pivotIdempotent_mul_of_ne x (by decide)) (pivotIdempotent_mul_of_ne x (by decide))
    (pivotIdempotent_mul_of_ne x (by decide)) (pivotIdempotent_sum x) (pivotIdempotent_mul_pivotInverse hx 0)
    (pivotIdempotent_mul_pivotInverse hx 1) (pivotIdempotent_mul_pivotInverse hx 2)

open scoped Classical in

private def sectionUnit (x : Fin 3 → 𝔸) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  if hx : x ∈ rowDomain then
    ⟨chartMatrix (pivotIdempotent x) x, chartInverse (pivotIdempotent x) x (pivotInverse x),
      chartMatrix_mul_chartInverse_pivot hx, _root_.mul_eq_one_comm.mp (chartMatrix_mul_chartInverse_pivot hx)⟩
  else 1

private theorem val_componentAt3 (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (componentAt3 (𝓞 ℚ) ℚ p g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      (g : Matrix (Fin 3) (Fin 3) 𝔸).map (evalHom p) := rfl

private theorem val_componentAt3_inv (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (((componentAt3 (𝓞 ℚ) ℚ p g)⁻¹ : Matrix.GeneralLinearGroup (Fin 3) (p.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      ((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸).map (evalHom p) := rfl

private theorem val_archComponent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (archComponent3 (𝓞 ℚ) ℚ g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (g : Matrix (Fin 3) (Fin 3) 𝔸).map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) := rfl

private theorem mem_localMaximalCompact3_of_forall {p : HeightOneSpectrum (𝓞 ℚ)}
    {k : Matrix.GeneralLinearGroup (Fin 3) (p.adicCompletion ℚ)}
    (h₁ : ∀ i j, (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈ p.adicCompletionIntegers ℚ)
    (h₂ : ∀ i j, ((k⁻¹ : Matrix.GeneralLinearGroup (Fin 3) (p.adicCompletion ℚ)) :
      Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈ p.adicCompletionIntegers ℚ) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p :=
  (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ p).mpr
    ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mp (h₁ i j),
      fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mp (h₂ i j)⟩

private theorem eventually_componentAt3_mem (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∀ᶠ p in Filter.cofinite, componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have hmat : ∀ M : Matrix (Fin 3) (Fin 3) 𝔸,
      ∀ᶠ p in Filter.cofinite, ∀ i j, evalHom p (M i j) ∈ p.adicCompletionIntegers ℚ := fun M => by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    filter_upwards [RestrictedProduct.eventually _ _ (M i j).2] with p hp
    exact hp
  filter_upwards [hmat (g : Matrix (Fin 3) (Fin 3) 𝔸), hmat ((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸)]
    with p h₁ h₂
  refine mem_localMaximalCompact3_of_forall (fun i j => ?_) (fun i j => ?_)
  · rw [val_componentAt3, Matrix.map_apply]
    exact h₁ i j
  · rw [val_componentAt3_inv, Matrix.map_apply]
    exact h₂ i j

private theorem rowAt_vecMul (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) (M : Matrix (Fin 3) (Fin 3) 𝔸) :
    rowAt p (x ᵥ* M) = rowAt p x ᵥ* M.map (evalHom p) := by
  funext j
  simp only [rowAt_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, fin_add_apply, fin_mul_apply,
    Matrix.map_apply, evalHom_eq]

private theorem exists_vecMul_ne_zero {A : Type*} [CommRing A] (u : (Matrix (Fin 3) (Fin 3) A)ˣ) {y : Fin 3 → A}
    (hy : ∃ j, y j ≠ 0) : ∃ j, (y ᵥ* (u : Matrix (Fin 3) (Fin 3) A)) j ≠ 0 := by
  by_contra hall
  have h0 : y ᵥ* (u : Matrix (Fin 3) (Fin 3) A) = 0 := funext fun j => not_not.mp fun h => hall ⟨j, h⟩
  have h1 : y = y ᵥ* ((u : Matrix (Fin 3) (Fin 3) A) *
      ((u⁻¹ : (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A)) := by
    rw [Units.mul_inv, Matrix.vecMul_one]
  have hy0 : y = 0 := by
    rw [h1, ← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul]
  obtain ⟨j, hj⟩ := hy
  exact hj (congrFun hy0 j)

private theorem valued_vecMul_le {p : HeightOneSpectrum (𝓞 ℚ)} {C : WithZero (Multiplicative ℤ)}
    {y : Fin 3 → p.adicCompletion ℚ} {k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)} (hy : ∀ i, Valued.v (y i) ≤ C)
    (hk : ∀ i j, Valued.v (k i j) ≤ 1) (j : Fin 3) : Valued.v ((y ᵥ* k) j) ≤ C := by
  have hterm : ∀ i, Valued.v (y i * k i j) ≤ C := fun i => by
    rw [map_mul]
    exact (mul_le_mul' (hy i) (hk i j)).trans_eq (mul_one C)
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private theorem primitiveAt_vecMul {p : HeightOneSpectrum (𝓞 ℚ)} {x : Fin 3 → 𝔸} (hx : PrimitiveAt p x)
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    PrimitiveAt p (x ᵥ* (g : Matrix (Fin 3) (Fin 3) 𝔸)) := by
  obtain ⟨hk, hk'⟩ := (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ p).mp hg
  rw [val_componentAt3] at hk
  rw [val_componentAt3_inv] at hk'
  rw [primitiveAt_iff] at hx ⊢
  rw [rowAt_vecMul]
  refine ⟨fun j => valued_vecMul_le hx.1 hk j, ?_⟩
  by_contra hall

  set z := rowAt p x ᵥ* (g : Matrix (Fin 3) (Fin 3) 𝔸).map (evalHom p) with hz
  have hzlt : ∀ j, Valued.v (z j) < 1 := fun j => lt_of_le_of_ne (valued_vecMul_le hx.1 hk j) fun h => hall ⟨j, h⟩
  set C := max (max (Valued.v (z 0)) (Valued.v (z 1))) (Valued.v (z 2)) with hC
  have hCle : ∀ j, Valued.v (z j) ≤ C := by
    intro j
    rw [hC]
    fin_cases j <;> simp
  have hClt : C < 1 := max_lt (max_lt (hzlt 0) (hzlt 1)) (hzlt 2)
  have hback : rowAt p x = z ᵥ* ((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸).map (evalHom p) := by
    rw [hz, Matrix.vecMul_vecMul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one (evalHom p) (map_zero _) (map_one _),
      Matrix.vecMul_one]
  obtain ⟨i, hi⟩ := hx.2
  have : Valued.v (rowAt p x i) ≤ C := by
    rw [hback]
    exact valued_vecMul_le hCle hk' i
  rw [hi] at this
  exact absurd (lt_of_le_of_lt this hClt) (lt_irrefl _)

private theorem eq_one_of_le_one_of_not_le {γ : WithZero (Multiplicative ℤ)} (h1 : γ ≤ 1)
    (h2 : ¬ γ ≤ WithZero.exp (-1 : ℤ)) : γ = 1 := by
  have hne : γ ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
  have hl1 : WithZero.log γ ≤ 0 := (WithZero.log_le_iff_le_exp hne).mpr (by rwa [WithZero.exp_zero])
  have hl2 : ¬ WithZero.log γ ≤ -1 := fun h => h2 ((WithZero.log_le_iff_le_exp hne).mp h)
  have hl : WithZero.log γ = 0 := by omega
  rw [← WithZero.exp_log hne, hl, WithZero.exp_zero]

private theorem isClopen_setOf_valued_eq_one (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsClopen {y : p.adicCompletion ℚ | Valued.v y = 1} := by
  obtain ⟨t, ht0, ht⟩ := AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) p 1
  simp only [Nat.cast_one] at ht
  have hset : {y : p.adicCompletion ℚ | Valued.v y = 1} =
      {y : p.adicCompletion ℚ | Valued.v y ≤ Valued.v (1 : p.adicCompletion ℚ)} \
        {y : p.adicCompletion ℚ | Valued.v y ≤ Valued.v t} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_diff, map_one, ht]
    constructor
    · intro h
      rw [h]
      refine ⟨le_rfl, fun h' => ?_⟩
      rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h'
      omega
    · rintro ⟨h1, h2⟩
      exact eq_one_of_le_one_of_not_le h1 h2
  rw [hset]
  exact IsClopen.diff
    ⟨AdelicLevel.isClosed_setOf_valued_le p (1 : p.adicCompletion ℚ) one_ne_zero,
      AdelicLevel.isOpen_setOf_valued_le p (1 : p.adicCompletion ℚ) one_ne_zero⟩
    ⟨AdelicLevel.isClosed_setOf_valued_le p t ht0, AdelicLevel.isOpen_setOf_valued_le p t ht0⟩

private scoped instance : Countable (HeightOneSpectrum (𝓞 ℚ)) :=
  Countable.of_equiv _ Rat.HeightOneSpectrum.primesEquiv.symm

private theorem continuous_rowAt (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    Continuous fun x : Fin 3 → 𝔸 => rowAt p x j :=
  ((AdelicLevel.continuous_finAdeleEval (R := 𝓞 ℚ) (K := ℚ) p).comp
    (AdelicLevel.continuous_adeleFin (R := 𝓞 ℚ) (K := ℚ))).comp (continuous_apply j)

private theorem continuous_rowArch (w : InfinitePlace ℚ) (j : Fin 3) : Continuous fun x : Fin 3 → 𝔸 => rowArch w x j :=
  ((AdelicLevel.continuous_archEval (K := ℚ) w).comp (AdelicLevel.continuous_adeleArch (R := 𝓞 ℚ) (K := ℚ))).comp
    (continuous_apply j)

private theorem isClopen_valued_rowAt_eq_one (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    IsClopen {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) = 1} :=
  (isClopen_setOf_valued_eq_one p).preimage (continuous_rowAt p j)

private theorem measurableSet_valued_rowAt_eq_one (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) = 1} :=
  (isClopen_valued_rowAt_eq_one p j).isClosed.measurableSet

private theorem measurableSet_valued_rowAt_le_one (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) ≤ 1} := by
  have h : IsClosed {y : p.adicCompletion ℚ | Valued.v y ≤ 1} := by
    simpa using AdelicLevel.isClosed_setOf_valued_le p (1 : p.adicCompletion ℚ) one_ne_zero
  exact (h.preimage (continuous_rowAt p j)).measurableSet

private theorem measurableSet_rowAt_ne_zero (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → 𝔸 | rowAt p x j ≠ 0} := by
  have h : IsOpen {y : p.adicCompletion ℚ | y ≠ 0} := isOpen_ne
  exact (h.preimage (continuous_rowAt p j)).measurableSet

private theorem measurableSet_rowArch_ne_zero (w : InfinitePlace ℚ) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → 𝔸 | rowArch w x j ≠ 0} := by
  have h : IsOpen {y : w.Completion | y ≠ 0} := isOpen_ne
  exact (h.preimage (continuous_rowArch w j)).measurableSet

private theorem measurableSet_primitiveAt (p : HeightOneSpectrum (𝓞 ℚ)) :
    MeasurableSet {x : Fin 3 → 𝔸 | PrimitiveAt p x} := by
  have h : {x : Fin 3 → 𝔸 | PrimitiveAt p x} =
      (⋂ j, {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) ≤ 1}) ∩ ⋃ j, {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) = 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, primitiveAt_iff]
  rw [h]
  exact (MeasurableSet.iInter fun j => measurableSet_valued_rowAt_le_one p j).inter
    (MeasurableSet.iUnion fun j => measurableSet_valued_rowAt_eq_one p j)

private theorem measurableSet_nonzeroAt (p : HeightOneSpectrum (𝓞 ℚ)) :
    MeasurableSet {x : Fin 3 → 𝔸 | NonzeroAt p x} := by
  have h : {x : Fin 3 → 𝔸 | NonzeroAt p x} = ⋃ j, {x : Fin 3 → 𝔸 | rowAt p x j ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, nonzeroAt_iff]
  rw [h]
  exact MeasurableSet.iUnion fun j => measurableSet_rowAt_ne_zero p j

private theorem measurableSet_nonzeroArch : MeasurableSet {x : Fin 3 → 𝔸 | NonzeroArch x} := by
  have h : {x : Fin 3 → 𝔸 | NonzeroArch x} = ⋃ j, {x : Fin 3 → 𝔸 | rowArch default x j ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun hx => exists_rowArch_ne_zero hx default, fun hx => nonzeroArch_of_rowArch hx⟩
  rw [h]
  exact MeasurableSet.iUnion fun j => measurableSet_rowArch_ne_zero default j

private theorem setOf_eventually_cofinite_eq {P : HeightOneSpectrum (𝓞 ℚ) → (Fin 3 → 𝔸) → Prop} :
    {x | ∀ᶠ p in Filter.cofinite, P p x} =
      ⋃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), ⋂ p, ⋂ (_ : p ∉ T), {x | P p x} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
  constructor
  · intro h
    have hfin := Filter.eventually_cofinite.mp h
    refine ⟨hfin.toFinset, fun p hp => ?_⟩
    by_contra hnp
    exact hp (hfin.mem_toFinset.mpr hnp)
  · rintro ⟨T, hT⟩
    refine Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun p hp => ?_)
    by_contra hpT
    exact hp (hT p fun h => hpT (Finset.mem_coe.mpr h))

private theorem rowDomain_measurableSet : MeasurableSet rowDomain := by
  have h : rowDomain = (⋂ p, {x : Fin 3 → 𝔸 | NonzeroAt p x}) ∩
      ({x : Fin 3 → 𝔸 | NonzeroArch x} ∩ {x : Fin 3 → 𝔸 | ∀ᶠ p in Filter.cofinite, PrimitiveAt p x}) := by
    ext x
    simp only [mem_rowDomain, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [h, setOf_eventually_cofinite_eq]
  refine (MeasurableSet.iInter fun p => measurableSet_nonzeroAt p).inter (measurableSet_nonzeroArch.inter ?_)
  exact MeasurableSet.iUnion fun T =>
    MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => measurableSet_primitiveAt p

private theorem measurable_finitePivot (p : HeightOneSpectrum (𝓞 ℚ)) :
    Measurable fun x : Fin 3 → 𝔸 => finitePivot p (rowAt p x) := by
  have hunit : ∀ j, MeasurableSet {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) = 1} := measurableSet_valued_rowAt_eq_one p
  have hne : ∀ j, MeasurableSet {x : Fin 3 → 𝔸 | rowAt p x j ≠ 0} := measurableSet_rowAt_ne_zero p
  simp only [finitePivot, unitPattern, preferredIndex]
  refine Measurable.ite ?_ ?_ ?_
  · rw [Set.setOf_exists]
    exact MeasurableSet.iUnion hunit
  · exact Measurable.ite (hunit 2) measurable_const (Measurable.ite (hunit 1) measurable_const measurable_const)
  · exact Measurable.ite (hne 2) measurable_const (Measurable.ite (hne 1) measurable_const measurable_const)

private theorem measurable_archPivot (w : InfinitePlace ℚ) :
    Measurable fun x : Fin 3 → 𝔸 => archPivot w (rowArch w x) := by
  have hne : ∀ j, MeasurableSet {x : Fin 3 → 𝔸 | rowArch w x j ≠ 0} := measurableSet_rowArch_ne_zero w
  simp only [archPivot, preferredIndex]
  exact Measurable.ite (hne 2) measurable_const (Measurable.ite (hne 1) measurable_const measurable_const)

private def piece (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3) : Set (Fin 3 → 𝔸) :=
  {x | x ∈ rowDomain ∧ (∀ p, p ∉ T → PrimitiveAt p x) ∧ (∀ p (hp : p ∈ T), finitePivot p (rowAt p x) = π ⟨p, hp⟩) ∧
    ∀ w, archPivot w (rowArch w x) = a}

private theorem mem_piece {T : Finset (HeightOneSpectrum (𝓞 ℚ))} {π : T → Fin 3} {a : Fin 3} {x : Fin 3 → 𝔸} :
    x ∈ piece T π a ↔ x ∈ rowDomain ∧ (∀ p, p ∉ T → PrimitiveAt p x) ∧
      (∀ p (hp : p ∈ T), finitePivot p (rowAt p x) = π ⟨p, hp⟩) ∧ ∀ w, archPivot w (rowArch w x) = a :=
  Iff.rfl

private theorem piece_subset_rowDomain (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3) :
    piece T π a ⊆ rowDomain :=
  fun _ hx => hx.1

private theorem measurableSet_piece (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3) :
    MeasurableSet (piece T π a) := by
  have h : piece T π a = rowDomain ∩ ((⋂ p, ⋂ (_ : p ∉ T), {x : Fin 3 → 𝔸 | PrimitiveAt p x}) ∩
      ((⋂ p, ⋂ (hp : p ∈ T), {x : Fin 3 → 𝔸 | finitePivot p (rowAt p x) = π ⟨p, hp⟩}) ∩
        ⋂ w, {x : Fin 3 → 𝔸 | archPivot w (rowArch w x) = a})) := by
    ext x
    simp only [mem_piece, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [h]
  refine rowDomain_measurableSet.inter
    ((MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => measurableSet_primitiveAt p).inter
      ((MeasurableSet.iInter fun p => MeasurableSet.iInter fun hp => ?_).inter (MeasurableSet.iInter fun w => ?_)))
  · exact measurable_finitePivot p (measurableSet_singleton (π ⟨p, hp⟩))
  · exact measurable_archPivot w (measurableSet_singleton a)

private theorem exists_mem_piece {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) :
    ∃ i : (Σ T : Finset (HeightOneSpectrum (𝓞 ℚ)), (T → Fin 3)) × Fin 3, x ∈ piece i.1.1 i.1.2 i.2 := by
  have hfin : {p | ¬ PrimitiveAt p x}.Finite := Filter.eventually_cofinite.mp hx.2.2
  refine ⟨⟨⟨hfin.toFinset, fun p => finitePivot p.1 (rowAt p.1 x)⟩, archPivot default (rowArch default x)⟩,
    mem_piece.mpr ⟨hx, fun p hp => ?_, fun p hp => rfl, fun w => ?_⟩⟩
  · by_contra h
    exact hp (hfin.mem_toFinset.mpr h)
  · rw [Subsingleton.elim w default]

private theorem continuous_ite_of_isClopen {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {P : X → Prop}
    [DecidablePred P] (hP : IsClopen {x | P x}) {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => if P x then f x else g x := by
  rw [continuous_def]
  intro u hu
  have h : (fun x => if P x then f x else g x) ⁻¹' u = ({x | P x} ∩ f ⁻¹' u) ∪ ({x | P x}ᶜ ∩ g ⁻¹' u) := by
    ext x
    by_cases hx : P x <;> simp [hx]
  rw [h]
  exact (hP.isOpen.inter (hu.preimage hf)).union (hP.compl.isOpen.inter (hu.preimage hg))

private theorem continuous_unitPattern (p : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous fun x : Fin 3 → 𝔸 => unitPattern p (rowAt p x) := by
  have hc : ∀ j, IsClopen {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) = 1} := isClopen_valued_rowAt_eq_one p
  simp only [unitPattern, preferredIndex]
  exact continuous_ite_of_isClopen (hc 2) continuous_const
    (continuous_ite_of_isClopen (hc 1) continuous_const continuous_const)

private theorem continuousOn_inv_unitPattern (p : HeightOneSpectrum (𝓞 ℚ)) :
    ContinuousOn (fun x : Fin 3 → 𝔸 => (rowAt p x (unitPattern p (rowAt p x)))⁻¹)
      {x : Fin 3 → 𝔸 | ∃ j, Valued.v (rowAt p x j) = 1} := by
  intro x₀ hx₀
  have hU : {x : Fin 3 → 𝔸 | unitPattern p (rowAt p x) = unitPattern p (rowAt p x₀)} ∈ 𝓝 x₀ :=
    ((isOpen_discrete {unitPattern p (rowAt p x₀)}).preimage (continuous_unitPattern p)).mem_nhds rfl
  have hne : rowAt p x₀ (unitPattern p (rowAt p x₀)) ≠ 0 := fun h0 => by
    have h1 := valued_unitPattern p hx₀
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hG : ContinuousAt (fun x : Fin 3 → 𝔸 => (rowAt p x (unitPattern p (rowAt p x₀)))⁻¹) x₀ :=
    (continuous_rowAt p _).continuousAt.inv₀ hne
  refine (hG.congr ?_).continuousWithinAt
  filter_upwards [hU] with x hx
  show (rowAt p x (unitPattern p (rowAt p x₀)))⁻¹ = (rowAt p x (unitPattern p (rowAt p x)))⁻¹
  rw [hx]

private theorem continuousOn_finiteAdele {X : Type*} [TopologicalSpace X] {s : Set X}
    {T : Set (HeightOneSpectrum (𝓞 ℚ))} (hT : T.Finite) (f : X → FiniteAdeleRing (𝓞 ℚ) ℚ)
    (hint : ∀ x ∈ s, ∀ p, p ∉ T → f x p ∈ p.adicCompletionIntegers ℚ)
    (hcont : ∀ p, ContinuousOn (fun x => f x p) s) : ContinuousOn f s := by
  have hle : Filter.cofinite ≤ Filter.principal Tᶜ := Filter.le_principal_iff.mpr hT.compl_mem_cofinite
  let g : s → Πʳ p : HeightOneSpectrum (𝓞 ℚ), [p.adicCompletion ℚ, p.adicCompletionIntegers ℚ]_[Filter.principal Tᶜ] :=
    fun z => ⟨fun p => f z.1 p, Filter.eventually_principal.mpr fun p hp => hint z.1 z.2 p hp⟩
  have hg : Continuous g := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_pi fun p => continuousOn_iff_continuous_restrict.mp (hcont p)
  have hfg : s.domRestrict f = RestrictedProduct.inclusion _ _ hle ∘ g :=
    funext fun z => FiniteAdeleRing.ext ℚ fun p => rfl
  rw [continuousOn_iff_continuous_restrict, hfg]
  exact (RestrictedProduct.continuous_inclusion hle).comp hg

private theorem continuousOn_adele {X : Type*} [TopologicalSpace X] {F : X → 𝔸} {s : Set X}
    (h₁ : ∀ w, ContinuousOn (fun x => (F x).1 w) s) (h₂ : ContinuousOn (fun x => (F x).2) s) : ContinuousOn F s :=
  ContinuousOn.prodMk (continuousOn_pi.mpr h₁) h₂

section ChartContinuity

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {X : Type*} [TopologicalSpace X]

private theorem continuous_chartMatrix {e y : X → Fin 3 → A} (he : ∀ j, Continuous fun x => e x j)
    (hy : ∀ j, Continuous fun x => y x j) : Continuous fun x => chartMatrix (e x) (y x) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [chartMatrix] <;>
    first
    | exact continuous_const
    | exact (he _).add (he _)
    | exact he _
    | exact hy _

private theorem continuous_chartInverse {e y : X → Fin 3 → A} {d : X → A} (he : ∀ j, Continuous fun x => e x j)
    (hy : ∀ j, Continuous fun x => y x j) (hd : Continuous d) :
    Continuous fun x => chartInverse (e x) (y x) (d x) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [chartInverse] <;>
    first
    | exact continuous_const
    | exact ((he _).add (he _)).sub ((he _).mul ((hy _).mul hd))
    | exact ((he _).mul ((hy _).mul hd)).neg
    | exact (he _).mul ((hy _).mul hd)
    | exact (he _).mul hd
    | exact (he _).sub ((he _).mul ((hy _).mul hd))

end ChartContinuity

private theorem pivotIdempotent_fin_mem (x : Fin 3 → 𝔸) (j : Fin 3) (p : HeightOneSpectrum (𝓞 ℚ)) :
    (pivotIdempotent x j).2 p ∈ p.adicCompletionIntegers ℚ := by
  rw [pivotIdempotent_fin]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

private theorem pivotInverse_fin_mem {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) {p : HeightOneSpectrum (𝓞 ℚ)}
    (hp : PrimitiveAt p x) : (pivotInverse x).2 p ∈ p.adicCompletionIntegers ℚ := by
  simp only [pivotInverse_fin hx, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀,
    valued_finitePivot p ((primitiveAt_iff p x).mp hp).2, inv_one, le_refl]

private theorem continuousOn_pivotIdempotent (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3)
    (j : Fin 3) : ContinuousOn (fun x => pivotIdempotent x j) (piece T π a) := by
  refine continuousOn_adele (fun w => ?_) ?_
  · refine ContinuousOn.congr (continuousOn_const : ContinuousOn (fun _ => if a = j then (1 : w.Completion) else 0) _)
      fun x hx => ?_
    show (pivotIdempotent x j).1 w = if a = j then 1 else 0
    rw [pivotIdempotent_arch, hx.2.2.2 w]
  · refine continuousOn_finiteAdele T.finite_toSet _ (fun x _ p _ => pivotIdempotent_fin_mem x j p) fun p => ?_
    by_cases hp : p ∈ T
    · refine ContinuousOn.congr
        (continuousOn_const : ContinuousOn (fun _ => if π ⟨p, hp⟩ = j then (1 : p.adicCompletion ℚ) else 0) _)
        fun x hx => ?_
      show (pivotIdempotent x j).2 p = if π ⟨p, hp⟩ = j then 1 else 0
      rw [pivotIdempotent_fin, hx.2.2.1 p hp]
    · have hcont : Continuous fun x : Fin 3 → 𝔸 =>
          if unitPattern p (rowAt p x) = j then (1 : p.adicCompletion ℚ) else 0 :=
        (continuous_of_discreteTopology (f := fun k : Fin 3 => if k = j then (1 : p.adicCompletion ℚ) else 0)).comp
          (continuous_unitPattern p)
      refine hcont.continuousOn.congr fun x hx => ?_
      show (pivotIdempotent x j).2 p = if unitPattern p (rowAt p x) = j then 1 else 0
      rw [pivotIdempotent_fin, finitePivot_of_exists_unit p ((primitiveAt_iff p x).mp (hx.2.1 p hp)).2]

private theorem continuousOn_pivotInverse (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3) :
    ContinuousOn pivotInverse (piece T π a) := by
  refine continuousOn_adele (fun w => ?_) ?_
  · have hc : ContinuousOn (fun x : Fin 3 → 𝔸 => (rowArch w x a)⁻¹) (piece T π a) :=
      (continuous_rowArch w a).continuousOn.inv₀ fun x hx => by
        have h := archPivot_ne_zero w (exists_rowArch_ne_zero hx.1.2.1 w)
        rwa [hx.2.2.2 w] at h
    refine hc.congr fun x hx => ?_
    show (pivotInverse x).1 w = (rowArch w x a)⁻¹
    rw [pivotInverse_arch hx.1, hx.2.2.2 w]
  · refine continuousOn_finiteAdele T.finite_toSet _ (fun x hx p hp => pivotInverse_fin_mem hx.1 (hx.2.1 p hp))
      fun p => ?_
    by_cases hp : p ∈ T
    · have hc : ContinuousOn (fun x : Fin 3 → 𝔸 => (rowAt p x (π ⟨p, hp⟩))⁻¹) (piece T π a) :=
        (continuous_rowAt p _).continuousOn.inv₀ fun x hx => by
          have h := finitePivot_ne_zero p ((nonzeroAt_iff p x).mp (hx.1.1 p))
          rwa [hx.2.2.1 p hp] at h
      refine hc.congr fun x hx => ?_
      show (pivotInverse x).2 p = (rowAt p x (π ⟨p, hp⟩))⁻¹
      rw [pivotInverse_fin hx.1, hx.2.2.1 p hp]
    · have hsub : piece T π a ⊆ {x : Fin 3 → 𝔸 | ∃ j, Valued.v (rowAt p x j) = 1} :=
        fun x hx => ((primitiveAt_iff p x).mp (hx.2.1 p hp)).2
      refine ((continuousOn_inv_unitPattern p).mono hsub).congr fun x hx => ?_
      show (pivotInverse x).2 p = (rowAt p x (unitPattern p (rowAt p x)))⁻¹
      rw [pivotInverse_fin hx.1, finitePivot_of_exists_unit p ((primitiveAt_iff p x).mp (hx.2.1 p hp)).2]

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private def sec0 (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  sectionUnit x

private theorem coe_sec0 {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) :
    (sec0 x : Matrix (Fin 3) (Fin 3) 𝔸) = chartMatrix (pivotIdempotent x) x := by
  unfold sec0 sectionUnit
  rw [dif_pos hx]

private theorem coe_sec0_inv {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) :
    (((sec0 x)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) =
      chartInverse (pivotIdempotent x) x (pivotInverse x) := by
  unfold sec0 sectionUnit
  rw [dif_pos hx]
  rfl

private theorem sec0_of_notMem {x : Fin 3 → 𝔸} (hx : x ∉ rowDomain) : sec0 x = 1 := by
  unfold sec0 sectionUnit
  rw [dif_neg hx]

private theorem measurable_of_pieces {X Y ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Countable ι] {f : X → Y} {s : Set X}
    (hs : MeasurableSet s) (t : ι → Set X) (ht : ∀ i, MeasurableSet (t i)) (hts : ∀ i, t i ⊆ s)
    (hcov : ∀ x ∈ s, ∃ i, x ∈ t i) (hf : ∀ i, ContinuousOn f (t i)) {c : Y} (hc : ∀ x, x ∉ s → f x = c) :
    Measurable f := by
  refine measurable_of_isOpen fun u hu => ?_
  have h1 : f ⁻¹' u ∩ s = ⋃ i, f ⁻¹' u ∩ t i := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨hxu, hxs⟩
      obtain ⟨i, hi⟩ := hcov x hxs
      exact ⟨i, hxu, hi⟩
    · rintro ⟨i, hxu, hi⟩
      exact ⟨hxu, hts i hi⟩
  have h1m : MeasurableSet (f ⁻¹' u ∩ s) := by
    rw [h1]
    refine MeasurableSet.iUnion fun i => ?_
    obtain ⟨v, hv, hvu⟩ := continuousOn_iff'.mp (hf i) u hu
    rw [hvu]
    exact hv.measurableSet.inter (ht i)
  have h2m : MeasurableSet (f ⁻¹' u ∩ sᶜ) := by
    by_cases hcu : c ∈ u
    · have h : f ⁻¹' u ∩ sᶜ = sᶜ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, and_iff_right_iff_imp]
        intro hxs
        rw [hc x hxs]
        exact hcu
      rw [h]
      exact hs.compl
    · have h : f ⁻¹' u ∩ sᶜ = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro hxu hxs
        rw [hc x hxs] at hxu
        exact hcu hxu
      rw [h]
      exact MeasurableSet.empty
  have h : f ⁻¹' u = (f ⁻¹' u ∩ s) ∪ (f ⁻¹' u ∩ sᶜ) := (Set.inter_union_compl _ _).symm
  rw [h]
  exact h1m.union h2m

private theorem continuousOn_sec0_piece (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3) :
    ContinuousOn sec0 (piece T π a) := by
  rw [continuousOn_iff_continuous_restrict]
  have hε : ∀ j, Continuous fun z : piece T π a => pivotIdempotent z.1 j := fun j =>
    continuousOn_iff_continuous_restrict.mp (continuousOn_pivotIdempotent T π a j)
  have hd : Continuous fun z : piece T π a => pivotInverse z.1 :=
    continuousOn_iff_continuous_restrict.mp (continuousOn_pivotInverse T π a)
  have hx : ∀ j, Continuous fun z : piece T π a => z.1 j := fun j => (continuous_apply j).comp continuous_subtype_val
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_chartMatrix (fun j => hε j) hx).congr fun z => (coe_sec0 z.2.1).symm
  · exact (continuous_chartInverse (fun j => hε j) hx hd).congr fun z => (coe_sec0_inv z.2.1).symm

private theorem bottomRow_sec0 {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ rowDomain) : bottomRow (sec0 x) = x := by
  funext j
  simp only [bottomRow, coe_sec0 hx]
  fin_cases j <;> simp [chartMatrix]

private theorem componentAt3_sec0_mem {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ rowDomain)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : PrimitiveAt p x) :
    componentAt3 (𝓞 ℚ) ℚ p (sec0 x) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have hunit : ∃ j, Valued.v (rowAt p x j) = 1 := hp.2
  have he : ∀ j, evalHom p (pivotIdempotent x j) ∈ p.adicCompletionIntegers ℚ := fun j => by
    rw [evalHom_eq, pivotIdempotent_fin]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hd : evalHom p (pivotInverse x) ∈ p.adicCompletionIntegers ℚ := by
    simp only [evalHom_eq, pivotInverse_fin hx, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀,
      valued_finitePivot p hunit, inv_one, le_refl]
  refine mem_localMaximalCompact3_of_forall (fun i j => ?_) (fun i j => ?_)
  · rw [val_componentAt3, coe_sec0 hx, chartMatrix_map]
    exact chartMatrix_apply_mem _ he hp.1 i j
  · rw [val_componentAt3_inv, coe_sec0_inv hx, chartInverse_map]
    exact chartInverse_apply_mem _ he hp.1 hd i j

private theorem measurable_sec0 : Measurable sec0 := by
  exact measurable_of_pieces rowDomain_measurableSet
    (fun i : (Σ T : Finset (HeightOneSpectrum (𝓞 ℚ)), (T → Fin 3)) × Fin 3 => piece i.1.1 i.1.2 i.2)
    (fun i => measurableSet_piece _ _ _) (fun i => piece_subset_rowDomain _ _ _) (fun _ hx => exists_mem_piece hx)
    (fun i => continuousOn_sec0_piece _ _ _) fun _ hx => sec0_of_notMem hx

private theorem measurableSet_rowDomain : MeasurableSet rowDomain := by
  exact rowDomain_measurableSet

private theorem vecMul_mem_rowDomain {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ rowDomain) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    x ᵥ* (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) ∈ rowDomain := by
  obtain ⟨hnz, harch, hprim⟩ := mem_rowDomain.mp hx
  refine mem_rowDomain.mpr ⟨fun p => ?_, ?_, ?_⟩
  · rw [nonzeroAt_iff, rowAt_vecMul, ← val_componentAt3]
    exact exists_vecMul_ne_zero _ ((nonzeroAt_iff p x).mp (hnz p))
  · obtain ⟨j, hj⟩ := exists_vecMul_ne_zero (archComponent3 (𝓞 ℚ) ℚ g)
      (y := fun j => AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j)) (by simpa [NonzeroArch] using harch)
    refine ⟨j, fun h0 => hj ?_⟩
    rw [val_archComponent3, ← h0]
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.map_apply, map_add, map_mul]
  · filter_upwards [hprim, eventually_componentAt3_mem g] with p hp hg
    exact primitiveAt_vecMul hp hg

end SectionHeads

end SectionAndRowSets

section LeviFibration

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private def OnShell (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : ↥mirabolic) : Prop :=
  ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
    ∃ (x y z : q.adicCompletion ℚ) (k : GL (Fin 3) (q.adicCompletion ℚ)),
      k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q ∧
        componentAt3 (𝓞 ℚ) ℚ q (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) = upperUnipotent3 x y z * k

section LeviFibrationConstruction

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdeleRing.secondCountableTopology

open scoped Classical

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

section Completion

variable {A : Type} [CommRing A]

private def leviCompletion (r₀ r₁ u v : A) : Matrix (Fin 3) (Fin 3) A :=
  !![-v, u, 0; r₀, r₁, 0; 0, 0, 1]

private def leviCompletionInv (r₀ r₁ u v d' : A) : Matrix (Fin 3) (Fin 3) A :=
  !![-(d' * r₁), d' * u, 0; d' * r₀, d' * v, 0; 0, 0, 1]

private theorem leviCompletion_mul_inv {r₀ r₁ u v d d' : A} (hrel : r₀ * u + r₁ * v = d) (hd : d * d' = 1) :
    leviCompletion r₀ r₁ u v * leviCompletionInv r₀ r₁ u v d' = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviCompletion, leviCompletionInv, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | ring1
      | linear_combination d' * hrel + hd

private theorem continuous_leviCompletion {X : Type} [TopologicalSpace X] [TopologicalSpace A] [IsTopologicalRing A]
    {r₀ r₁ u v : X → A} (h₀ : Continuous r₀) (h₁ : Continuous r₁) (hu : Continuous u) (hv : Continuous v) :
    Continuous fun x => leviCompletion (r₀ x) (r₁ x) (u x) (v x) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [leviCompletion] <;>
    first | exact continuous_const | exact h₀ | exact h₁ | exact hu | exact hv | exact hv.neg

private theorem continuous_leviCompletionInv {X : Type} [TopologicalSpace X] [TopologicalSpace A]
    [IsTopologicalRing A] {r₀ r₁ u v d' : X → A} (h₀ : Continuous r₀) (h₁ : Continuous r₁) (hu : Continuous u)
    (hv : Continuous v) (hd : Continuous d') :
    Continuous fun x => leviCompletionInv (r₀ x) (r₁ x) (u x) (v x) (d' x) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [leviCompletionInv] <;>
    first | exact continuous_const | exact (hd.mul h₁).neg | exact hd.mul hu | exact hd.mul h₀ | exact hd.mul hv

end Completion

private def completionUnit (r₀ r₁ u v d d' : 𝔸) (hrel : r₀ * u + r₁ * v = d) (hd : d * d' = 1) :
    AdelicGL 3 (𝓞 ℚ) ℚ :=
  ⟨leviCompletion r₀ r₁ u v, leviCompletionInv r₀ r₁ u v d', leviCompletion_mul_inv hrel hd,
    _root_.mul_eq_one_comm.mp (leviCompletion_mul_inv hrel hd)⟩

private theorem completionUnit_mem_mirabolic (r₀ r₁ u v d d' : 𝔸) (hrel : r₀ * u + r₁ * v = d) (hd : d * d' = 1) :
    completionUnit r₀ r₁ u v d d' hrel hd ∈ mirabolic := by
  show bottomRow _ = e₃
  funext j
  fin_cases j <;> simp [bottomRow, completionUnit, leviCompletion, e₃]

private def completionMirabolic (r₀ r₁ u v d d' : 𝔸) (hrel : r₀ * u + r₁ * v = d) (hd : d * d' = 1) :
    ↥mirabolic :=
  ⟨completionUnit r₀ r₁ u v d d' hrel hd, completionUnit_mem_mirabolic r₀ r₁ u v d d' hrel hd⟩

private theorem leviRow_completionMirabolic (r₀ r₁ u v d d' : 𝔸) (hrel : r₀ * u + r₁ * v = d) (hd : d * d' = 1) :
    leviRow (completionMirabolic r₀ r₁ u v d d' hrel hd) = ![r₀, r₁] := by
  funext i
  fin_cases i <;> simp [leviRow, completionMirabolic, completionUnit, leviCompletion]

private def liftRow (r : Fin 2 → 𝔸) : Fin 3 → 𝔸 :=
  ![r 0, r 1, 0]

private theorem continuous_liftRow : Continuous liftRow := by
  refine continuous_pi fun j => ?_
  fin_cases j
  · exact continuous_apply (0 : Fin 2)
  · exact continuous_apply (1 : Fin 2)
  · exact continuous_const

private theorem liftRow_castSucc (r : Fin 2 → 𝔸) (i : Fin 2) : liftRow r (Fin.castSucc i) = r i := by
  fin_cases i <;> rfl

private def cofactorU (g : AdelicGL 3 (𝓞 ℚ) ℚ) : 𝔸 :=
  (g : Matrix (Fin 3) (Fin 3) 𝔸) 0 1 * (g : Matrix (Fin 3) (Fin 3) 𝔸) 1 2 -
    (g : Matrix (Fin 3) (Fin 3) 𝔸) 0 2 * (g : Matrix (Fin 3) (Fin 3) 𝔸) 1 1

private def cofactorV (g : AdelicGL 3 (𝓞 ℚ) ℚ) : 𝔸 :=
  (g : Matrix (Fin 3) (Fin 3) 𝔸) 0 2 * (g : Matrix (Fin 3) (Fin 3) 𝔸) 1 0 -
    (g : Matrix (Fin 3) (Fin 3) 𝔸) 0 0 * (g : Matrix (Fin 3) (Fin 3) 𝔸) 1 2

private def detInv (g : AdelicGL 3 (𝓞 ℚ) ℚ) : 𝔸 :=
  ((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸).det

private theorem det_mul_detInv (g : AdelicGL 3 (𝓞 ℚ) ℚ) : (g : Matrix (Fin 3) (Fin 3) 𝔸).det * detInv g = 1 := by
  rw [detInv, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

private theorem cofactor_rel {r : Fin 2 → 𝔸} (hr : liftRow r ∈ rowDomain) :
    r 0 * cofactorU (sec0 (liftRow r)) + r 1 * cofactorV (sec0 (liftRow r)) =
      ((sec0 (liftRow r) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸).det := by
  have hb := bottomRow_sec0 hr
  have h20 : ((sec0 (liftRow r) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 2 0 = r 0 := congrFun hb 0
  have h21 : ((sec0 (liftRow r) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 2 1 = r 1 := congrFun hb 1
  have h22 : ((sec0 (liftRow r) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 2 2 = 0 := congrFun hb 2
  rw [Matrix.det_fin_three, h20, h21, h22]
  simp only [cofactorU, cofactorV]
  ring1

private def leviSection (r : Fin 2 → 𝔸) : ↥mirabolic :=
  if hr : liftRow r ∈ rowDomain then
    completionMirabolic (r 0) (r 1) (cofactorU (sec0 (liftRow r))) (cofactorV (sec0 (liftRow r)))
      ((sec0 (liftRow r) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸).det (detInv (sec0 (liftRow r)))
      (cofactor_rel hr) (det_mul_detInv _)
  else 1

private theorem leviRow_leviSection {r : Fin 2 → 𝔸} (hr : liftRow r ∈ rowDomain) : leviRow (leviSection r) = r := by
  rw [leviSection, dif_pos hr, leviRow_completionMirabolic]
  funext i
  fin_cases i <;> rfl

private theorem leviSection_of_notMem {r : Fin 2 → 𝔸} (hr : liftRow r ∉ rowDomain) : leviSection r = 1 := by
  rw [leviSection, dif_neg hr]

private theorem continuousOn_leviSection_piece (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3) :
    ContinuousOn leviSection (liftRow ⁻¹' piece T π a) := by
  rw [continuousOn_iff_continuous_restrict]
  have hmem : ∀ z : liftRow ⁻¹' piece T π a, liftRow z.1 ∈ rowDomain := fun z =>
    piece_subset_rowDomain T π a z.2
  have hM : Continuous fun z : liftRow ⁻¹' piece T π a => sec0 (liftRow z.1) :=
    (continuousOn_sec0_piece T π a).comp_continuous (continuous_liftRow.comp continuous_subtype_val) fun z => z.2
  obtain ⟨hMv, hMi⟩ := Units.continuous_iff.mp hM
  have hent : ∀ i j : Fin 3, Continuous fun z : liftRow ⁻¹' piece T π a =>
      ((sec0 (liftRow z.1) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) i j :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hMv)
  have hu : Continuous fun z : liftRow ⁻¹' piece T π a => cofactorU (sec0 (liftRow z.1)) :=
    ((hent 0 1).mul (hent 1 2)).sub ((hent 0 2).mul (hent 1 1))
  have hv : Continuous fun z : liftRow ⁻¹' piece T π a => cofactorV (sec0 (liftRow z.1)) :=
    ((hent 0 2).mul (hent 1 0)).sub ((hent 0 0).mul (hent 1 2))
  have hd' : Continuous fun z : liftRow ⁻¹' piece T π a => detInv (sec0 (liftRow z.1)) := hMi.matrix_det
  have h0 : Continuous fun z : liftRow ⁻¹' piece T π a => z.1 0 :=
    (continuous_apply (0 : Fin 2)).comp continuous_subtype_val
  have h1 : Continuous fun z : liftRow ⁻¹' piece T π a => z.1 1 :=
    (continuous_apply (1 : Fin 2)).comp continuous_subtype_val
  have hval : Continuous fun z : liftRow ⁻¹' piece T π a =>
      leviCompletion (z.1 0) (z.1 1) (cofactorU (sec0 (liftRow z.1))) (cofactorV (sec0 (liftRow z.1))) :=
    continuous_leviCompletion h0 h1 hu hv
  have hinv : Continuous fun z : liftRow ⁻¹' piece T π a =>
      leviCompletionInv (z.1 0) (z.1 1) (cofactorU (sec0 (liftRow z.1))) (cofactorV (sec0 (liftRow z.1)))
        (detInv (sec0 (liftRow z.1))) :=
    continuous_leviCompletionInv h0 h1 hu hv hd'
  have hunit : Continuous fun z : liftRow ⁻¹' piece T π a =>
      completionUnit (z.1 0) (z.1 1) (cofactorU (sec0 (liftRow z.1))) (cofactorV (sec0 (liftRow z.1)))
        ((sec0 (liftRow z.1) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸).det (detInv (sec0 (liftRow z.1)))
        (cofactor_rel (hmem z)) (det_mul_detInv _) :=
    Units.continuous_iff.mpr ⟨hval, hinv⟩
  refine (hunit.subtype_mk fun z => completionUnit_mem_mirabolic _ _ _ _ _ _ _ _).congr fun z => ?_
  simp only [Set.domRestrict_apply, leviSection, dif_pos (hmem z), completionMirabolic]

private theorem measurable_leviSection : Measurable leviSection := by
  refine measurable_of_pieces (continuous_liftRow.measurable measurableSet_rowDomain)
    (fun i : (Σ T : Finset (HeightOneSpectrum (𝓞 ℚ)), (T → Fin 3)) × Fin 3 => liftRow ⁻¹' piece i.1.1 i.1.2 i.2)
    (fun i => continuous_liftRow.measurable (measurableSet_piece _ _ _))
    (fun i r hr => piece_subset_rowDomain _ _ _ hr) (fun _ hr => exists_mem_piece hr)
    (fun i => continuousOn_leviSection_piece _ _ _) fun _ hr => leviSection_of_notMem hr

private theorem mirabolic_apply_two_castSucc (p : ↥mirabolic) (j : Fin 2) :
    ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 2 (Fin.castSucc j) = 0 := by
  have h : bottomRow (p : AdelicGL 3 (𝓞 ℚ) ℚ) = e₃ := p.2
  have hj := congrFun h (Fin.castSucc j)
  simp only [bottomRow] at hj
  rw [hj]
  fin_cases j <;> simp [e₃]

private theorem leviRow_mul (q p : ↥mirabolic) : leviRow (q * p) = leviAct (leviRow q) p := by
  funext j
  have h2 := mirabolic_apply_two_castSucc p j
  simp [leviRow, leviAct, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h2]

private theorem leviAct_e₂ (p : ↥mirabolic) : leviAct e₂ p = leviRow p := by
  funext j
  simp [leviAct, leviRow, e₂]

private theorem leviRow_one : leviRow (1 : ↥mirabolic) = e₂ := by
  funext i
  fin_cases i <;> simp [leviRow, e₂]

private theorem leviAct_leviAct (r : Fin 2 → 𝔸) (p q : ↥mirabolic) : leviAct (leviAct r p) q = leviAct r (p * q) := by
  funext j
  have h2 := mirabolic_apply_two_castSucc q j
  simp only [leviAct, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
    Fin.castSucc_zero, Fin.castSucc_one]
  rw [h2]
  ring1

private theorem leviAct_one (r : Fin 2 → 𝔸) : leviAct r (1 : ↥mirabolic) = r := by
  funext j
  fin_cases j <;> simp [leviAct, Fin.sum_univ_two, Matrix.one_apply]

private def leviKernel : Subgroup ↥mirabolic where
  carrier := {p | leviRow p = e₂}
  one_mem' := leviRow_one
  mul_mem' := by
    intro q p hq hp
    simp only [Set.mem_setOf_eq] at hq hp ⊢
    rw [leviRow_mul, hq, leviAct_e₂, hp]
  inv_mem' := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    have h := leviRow_mul p p⁻¹
    rw [mul_inv_cancel, leviRow_one, hp, leviAct_e₂] at h
    exact h.symm

private def sectionDomain : Set (Fin 2 → 𝔸) :=
  liftRow ⁻¹' rowDomain

private theorem measurableSet_sectionDomain : MeasurableSet sectionDomain :=
  continuous_liftRow.measurable measurableSet_rowDomain

private theorem liftRow_leviAct (r : Fin 2 → 𝔸) (p : ↥mirabolic) :
    liftRow (leviAct r p) =
      (liftRow r ᵥ* ((upperUnipotent3 (0 : 𝔸) (-((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 1 2)
          (-((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 0 2) : AdelicGL 3 (𝓞 ℚ) ℚ) :
            Matrix (Fin 3) (Fin 3) 𝔸)) ᵥ* ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) := by
  have h20 := mirabolic_apply_two_castSucc p 0
  have h21 := mirabolic_apply_two_castSucc p 1
  have h22 : ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 2 2 = 1 := by
    have h : bottomRow (p : AdelicGL 3 (𝓞 ℚ) ℚ) = e₃ := p.2
    have h2 := congrFun h 2
    simpa [bottomRow, e₃] using h2
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at h20 h21
  funext j
  fin_cases j
  · simp [liftRow, leviAct, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, h20]
  · simp [liftRow, leviAct, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, h21]
  · simp [liftRow, leviAct, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, h22]
    ring1

private theorem leviAct_mem_sectionDomain {r : Fin 2 → 𝔸} (hr : r ∈ sectionDomain) (p : ↥mirabolic) :
    leviAct r p ∈ sectionDomain := by
  show liftRow (leviAct r p) ∈ rowDomain
  rw [liftRow_leviAct]
  exact vecMul_mem_rowDomain (vecMul_mem_rowDomain hr _) _

private theorem leviAct_mem_sectionDomain_iff (r : Fin 2 → 𝔸) (p : ↥mirabolic) :
    leviAct r p ∈ sectionDomain ↔ r ∈ sectionDomain := by
  refine ⟨fun h => ?_, fun h => leviAct_mem_sectionDomain h p⟩
  have h' := leviAct_mem_sectionDomain h p⁻¹
  rwa [leviAct_leviAct, mul_inv_cancel, leviAct_one] at h'

private theorem goodLeviRows_subset_sectionDomain (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    goodLeviRows S ⊆ sectionDomain := by
  intro r hr
  obtain ⟨hprim, hnz, harch⟩ := hr
  refine mem_rowDomain.mpr ⟨fun q => ?_, ?_, ?_⟩
  · by_cases hq : q ∈ S
    · obtain ⟨i, hi⟩ := hnz q hq
      exact ⟨Fin.castSucc i, by rwa [liftRow_castSucc]⟩
    · obtain ⟨i, hi⟩ := (hprim q hq).2
      refine ⟨Fin.castSucc i, ?_⟩
      rw [liftRow_castSucc]
      intro h0
      rw [h0, map_zero] at hi
      exact zero_ne_one hi
  · obtain ⟨i, hi⟩ := harch
    exact ⟨Fin.castSucc i, by rwa [liftRow_castSucc]⟩
  · refine Filter.eventually_cofinite.mpr (S.finite_toSet.subset fun q hq => ?_)
    by_contra hqS
    have hqS' : q ∉ S := fun h => hqS (Finset.mem_coe.mpr h)
    obtain ⟨hint, i, hi⟩ := hprim q hqS'
    refine hq ⟨fun j => ?_, Fin.castSucc i, by rwa [liftRow_castSucc]⟩
    fin_cases j
    · exact hint 0
    · exact hint 1
    · simp [liftRow]

section KernelRow

variable {F : Type} [CommRing F]

private theorem row_one_pairing (k : GL (Fin 3) F) (h20 : (k : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (k : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) (h22 : (k : Matrix (Fin 3) (Fin 3) F) 2 2 = 1) :
    (k : Matrix (Fin 3) (Fin 3) F) 1 0 * ((k⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 +
      (k : Matrix (Fin 3) (Fin 3) F) 1 1 * ((k⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 := by
  have hmul : (k : Matrix (Fin 3) (Fin 3) F) * ((k⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinv21 : ((k⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
    have h := congrFun (congrFun hmul 2) 1
    rw [Matrix.mul_apply, Fin.sum_univ_three, h20, h21, h22, Matrix.one_apply_ne (by decide)] at h
    simpa using h
  have h := congrFun (congrFun hmul 1) 1
  rw [Matrix.mul_apply, Fin.sum_univ_three, hinv21, Matrix.one_apply_eq] at h
  simpa using h

end KernelRow

private theorem mirabolic_row_two (p : ↥mirabolic) (j : Fin 3) :
    ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 2 j = e₃ j := by
  have h : bottomRow (p : AdelicGL 3 (𝓞 ℚ) ℚ) = e₃ := p.2
  exact congrFun h j

private theorem evalHom_leviRow (q : HeightOneSpectrum (𝓞 ℚ)) (p : ↥mirabolic) (i : Fin 2) :
    evalHom q (leviRow p i) =
      (componentAt3 (𝓞 ℚ) ℚ q (p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) 1
        (Fin.castSucc i) := by
  simp only [val_componentAt3, Matrix.map_apply, leviRow]

private theorem componentAt3_row_two (q : HeightOneSpectrum (𝓞 ℚ)) (p : ↥mirabolic) (j : Fin 3) :
    (componentAt3 (𝓞 ℚ) ℚ q (p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) 2 j =
      evalHom q (e₃ j) := by
  simp only [val_componentAt3, Matrix.map_apply, mirabolic_row_two]

private theorem adeleArch_leviRow (p : ↥mirabolic) (i : Fin 2) :
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ (leviRow p i) =
      (archComponent3 (𝓞 ℚ) ℚ (p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) 1
        (Fin.castSucc i) := by
  simp only [val_archComponent3, Matrix.map_apply, leviRow]

private theorem archComponent3_row_two (p : ↥mirabolic) (j : Fin 3) :
    (archComponent3 (𝓞 ℚ) ℚ (p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) 2 j =
      AdelicLevel.adeleArch (𝓞 ℚ) ℚ (e₃ j) := by
  simp only [val_archComponent3, Matrix.map_apply, mirabolic_row_two]

private theorem leviNonzeroAt_leviRow (q : HeightOneSpectrum (𝓞 ℚ)) (p : ↥mirabolic) :
    LeviNonzeroAt q (leviRow p) := by
  by_contra hne
  have h0 : ∀ i : Fin 2, evalHom q (leviRow p i) = 0 := fun i => by
    by_contra h
    exact hne ⟨i, h⟩
  have hpair := row_one_pairing (componentAt3 (𝓞 ℚ) ℚ q (p : AdelicGL 3 (𝓞 ℚ) ℚ))
    (by rw [componentAt3_row_two]; simp [e₃]) (by rw [componentAt3_row_two]; simp [e₃])
    (by rw [componentAt3_row_two]; simp [e₃])
  have h10 := h0 0
  have h11 := h0 1
  rw [evalHom_leviRow] at h10 h11
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at h10 h11
  rw [h10, h11, zero_mul, zero_mul, add_zero] at hpair
  exact zero_ne_one hpair

private theorem leviNonzeroArch_leviRow (p : ↥mirabolic) : LeviNonzeroArch (leviRow p) := by
  by_contra hne
  have h0 : ∀ i : Fin 2, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (leviRow p i) = 0 := fun i => by
    by_contra h
    exact hne ⟨i, h⟩
  have hpair := row_one_pairing (archComponent3 (𝓞 ℚ) ℚ (p : AdelicGL 3 (𝓞 ℚ) ℚ))
    (by rw [archComponent3_row_two]; simp [e₃]) (by rw [archComponent3_row_two]; simp [e₃])
    (by rw [archComponent3_row_two]; simp [e₃])
  have h10 := h0 0
  have h11 := h0 1
  rw [adeleArch_leviRow] at h10 h11
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at h10 h11
  rw [h10, h11, zero_mul, zero_mul, add_zero] at hpair
  exact zero_ne_one hpair

private theorem leviPrimitiveAt_leviRow_of_onShell (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {p : ↥mirabolic}
    (hp : OnShell S p) (q : HeightOneSpectrum (𝓞 ℚ)) (hq : q ∉ S) : LeviPrimitiveAt q (leviRow p) := by
  obtain ⟨x, y, z, k, hk, hpk⟩ := hp q hq
  rw [mem_localMaximalCompact3_iff] at hk

  have hk2 : ∀ j : Fin 3, (k : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) 2 j = evalHom q (e₃ j) := by
    intro j
    rw [← componentAt3_row_two q p j, hpk, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, upperUnipotent3_coe]
    simp
  have hk20 : (k : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) 2 0 = 0 := by rw [hk2]; simp [e₃]
  have hk21 : (k : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) 2 1 = 0 := by rw [hk2]; simp [e₃]
  have hk22 : (k : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) 2 2 = 1 := by rw [hk2]; simp [e₃]

  have hrow : ∀ i : Fin 2,
      evalHom q (leviRow p i) = (k : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) 1 (Fin.castSucc i) := by
    intro i
    rw [evalHom_leviRow, hpk, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, upperUnipotent3_coe]
    fin_cases i <;> simp [hk20, hk21]
  refine ⟨fun i => ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hrow]
    exact hk.1 1 _
  · by_contra hne
    have hlt : ∀ i : Fin 2, Valued.v ((k : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) 1 (Fin.castSucc i)) < 1 :=
      fun i => lt_of_le_of_ne (hk.1 1 _) fun h => hne ⟨i, by rw [hrow]; exact h⟩
    have hpair := row_one_pairing k hk20 hk21 hk22
    have hlt0 := hlt 0
    have hlt1 := hlt 1
    simp only [Fin.castSucc_zero, Fin.castSucc_one] at hlt0 hlt1
    have ht0 : Valued.v ((k : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) 1 0 *
        ((k⁻¹ : GL (Fin 3) (q.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) 0 1) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hk.2 0 1)) hlt0
    have ht1 : Valued.v ((k : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) 1 1 *
        ((k⁻¹ : GL (Fin 3) (q.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) 1 1) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hk.2 1 1)) hlt1
    have hsum := lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt ht0 ht1)
    rw [hpair, map_one] at hsum
    exact lt_irrefl _ hsum

private theorem primitiveAt_liftRow {q : HeightOneSpectrum (𝓞 ℚ)} {r : Fin 2 → 𝔸} (h : LeviPrimitiveAt q r) :
    PrimitiveAt q (liftRow r) := by
  obtain ⟨hint, i, hi⟩ := h
  refine ⟨fun j => ?_, ⟨Fin.castSucc i, by rw [liftRow_castSucc]; exact hi⟩⟩
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [liftRow]
  · rw [liftRow_castSucc]
    exact hint j

private theorem primitiveAt_liftRow_iff (q : HeightOneSpectrum (𝓞 ℚ)) (r : Fin 2 → 𝔸) :
    PrimitiveAt q (liftRow r) ↔ LeviPrimitiveAt q r := by
  refine ⟨fun h => ⟨fun i => ?_, ?_⟩, primitiveAt_liftRow⟩
  · have := h.1 (Fin.castSucc i)
    rwa [liftRow_castSucc] at this
  · obtain ⟨j, hj⟩ := h.2
    refine Fin.lastCases ?_ (fun i hi => ⟨i, ?_⟩) j hj
    · intro h0
      simp [liftRow] at h0
    · rwa [liftRow_castSucc] at hi

private theorem nonzeroAt_liftRow_iff (q : HeightOneSpectrum (𝓞 ℚ)) (r : Fin 2 → 𝔸) :
    NonzeroAt q (liftRow r) ↔ LeviNonzeroAt q r := by
  constructor
  · rintro ⟨j, hj⟩
    refine Fin.lastCases ?_ (fun i hi => ⟨i, ?_⟩) j hj
    · intro h0
      simp [liftRow] at h0
    · rwa [liftRow_castSucc] at hi
  · rintro ⟨i, hi⟩
    exact ⟨Fin.castSucc i, by rwa [liftRow_castSucc]⟩

private theorem nonzeroArch_liftRow_iff (r : Fin 2 → 𝔸) : NonzeroArch (liftRow r) ↔ LeviNonzeroArch r := by
  constructor
  · rintro ⟨j, hj⟩
    refine Fin.lastCases ?_ (fun i hi => ⟨i, ?_⟩) j hj
    · intro h0
      simp [liftRow] at h0
    · rwa [liftRow_castSucc] at hi
  · rintro ⟨i, hi⟩
    exact ⟨Fin.castSucc i, by rwa [liftRow_castSucc]⟩

private theorem measurableSet_goodLeviRows (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    MeasurableSet (goodLeviRows S) := by
  have h : goodLeviRows S = liftRow ⁻¹' ((⋂ q, ⋂ (_ : q ∉ S), {x : Fin 3 → 𝔸 | PrimitiveAt q x}) ∩
      ((⋂ q ∈ S, {x : Fin 3 → 𝔸 | NonzeroAt q x}) ∩ {x : Fin 3 → 𝔸 | NonzeroArch x})) := by
    ext r
    simp only [goodLeviRows, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter,
      primitiveAt_liftRow_iff, nonzeroAt_liftRow_iff, nonzeroArch_liftRow_iff]
  rw [h]
  refine continuous_liftRow.measurable ?_
  refine (MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => measurableSet_primitiveAt q).inter ?_
  exact (MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => measurableSet_nonzeroAt q).inter
    measurableSet_nonzeroArch

private theorem componentAt3_leviSection_mem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {r : Fin 2 → 𝔸}
    (hr : r ∈ goodLeviRows S) {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ∉ S) :
    componentAt3 (𝓞 ℚ) ℚ q (leviSection r : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q := by
  have hdom : liftRow r ∈ rowDomain := goodLeviRows_subset_sectionDomain S hr
  obtain ⟨h₁, h₂⟩ := (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ q).mp
    (componentAt3_sec0_mem hdom (primitiveAt_liftRow (hr.1 q hq)))
  have e : ∀ i j, evalHom q (((sec0 (liftRow r) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) i j) ∈
      q.adicCompletionIntegers ℚ := fun i j => by
    have h := h₁ i j
    rw [val_componentAt3, Matrix.map_apply] at h
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ q).mpr h
  have e' : ∀ i j, evalHom q ((((sec0 (liftRow r))⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) i j) ∈
      q.adicCompletionIntegers ℚ := fun i j => by
    have h := h₂ i j
    rw [val_componentAt3_inv, Matrix.map_apply] at h
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ q).mpr h
  have hr0 : evalHom q (r 0) ∈ q.adicCompletionIntegers ℚ := (hr.1 q hq).1 0
  have hr1 : evalHom q (r 1) ∈ q.adicCompletionIntegers ℚ := (hr.1 q hq).1 1
  have hu : evalHom q (cofactorU (sec0 (liftRow r))) ∈ q.adicCompletionIntegers ℚ := by
    unfold cofactorU
    rw [map_sub, map_mul, map_mul]
    exact sub_mem (mul_mem (e 0 1) (e 1 2)) (mul_mem (e 0 2) (e 1 1))
  have hv : evalHom q (cofactorV (sec0 (liftRow r))) ∈ q.adicCompletionIntegers ℚ := by
    unfold cofactorV
    rw [map_sub, map_mul, map_mul]
    exact sub_mem (mul_mem (e 0 2) (e 1 0)) (mul_mem (e 0 0) (e 1 2))
  have hd : evalHom q (detInv (sec0 (liftRow r))) ∈ q.adicCompletionIntegers ℚ := by
    unfold detInv
    rw [RingHom.map_det, Matrix.det_fin_three]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    refine sub_mem (add_mem (add_mem (sub_mem (sub_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
      exact mul_mem (mul_mem (e' _ _) (e' _ _)) (e' _ _)
  have hval : ((leviSection r : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) =
      leviCompletion (r 0) (r 1) (cofactorU (sec0 (liftRow r))) (cofactorV (sec0 (liftRow r))) := by
    rw [leviSection, dif_pos hdom]
    rfl
  have hinv : (((leviSection r : AdelicGL 3 (𝓞 ℚ) ℚ)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) =
      leviCompletionInv (r 0) (r 1) (cofactorU (sec0 (liftRow r))) (cofactorV (sec0 (liftRow r)))
        (detInv (sec0 (liftRow r))) := by
    rw [leviSection, dif_pos hdom]
    rfl
  refine mem_localMaximalCompact3_of_forall (fun i j => ?_) (fun i j => ?_)
  · rw [val_componentAt3, Matrix.map_apply, hval]
    fin_cases i <;> fin_cases j <;> simp [leviCompletion] <;>
      first | exact hr0 | exact hr1 | exact hu | exact hv
  · rw [val_componentAt3_inv, Matrix.map_apply, hinv]
    fin_cases i <;> fin_cases j <;> simp [leviCompletionInv] <;>
      first | exact mul_mem hd hr1 | exact mul_mem hd hu | exact mul_mem hd hr0 | exact mul_mem hd hv

private theorem leviRow_mem_goodLeviRows_of_onShell (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {p : ↥mirabolic}
    (hp : OnShell S p) : leviRow p ∈ goodLeviRows S :=
  ⟨fun q hq => leviPrimitiveAt_leviRow_of_onShell S hp q hq, fun q _ => leviNonzeroAt_leviRow q p,
    leviNonzeroArch_leviRow p⟩

private theorem exists_levi_section (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ (P₂ : Subgroup ↥mirabolic) (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic)
      (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)),
      (∀ p : ↥mirabolic, p ∈ P₂ ↔ leviRow p = e₂) ∧
      Measurable sec ∧
      (∀ r ∈ R, leviRow (sec r) = r) ∧
      MeasurableSet R ∧
      (∀ r, ∀ p : ↥mirabolic, leviAct r p ∈ R ↔ r ∈ R) ∧
      (∀ q p : ↥mirabolic, leviRow (q * p) = leviAct (leviRow q) p) ∧
      goodLeviRows S ⊆ R ∧
      (∀ p : ↥mirabolic, OnShell S p → leviRow p ∈ goodLeviRows S) ∧
      (∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
        componentAt3 (𝓞 ℚ) ℚ q (sec r : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) ∈
          localMaximalCompact3 (𝓞 ℚ) ℚ q) ∧
      MeasurableSet (goodLeviRows S) := by
  refine ⟨leviKernel, leviSection, sectionDomain, fun p => Iff.rfl, measurable_leviSection,
    fun r hr => leviRow_leviSection hr, measurableSet_sectionDomain, leviAct_mem_sectionDomain_iff, leviRow_mul,
    goodLeviRows_subset_sectionDomain S, fun p hp => leviRow_mem_goodLeviRows_of_onShell S hp,
    fun r hr q hq => componentAt3_leviSection_mem S hr hq, measurableSet_goodLeviRows S⟩

end LeviFibrationConstruction

end LeviFibration

end MirabolicLeviFibration
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end LeviSections
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowMass

noncomputable section

namespace MirabolicLeviFibration

section Furniture

end Furniture
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end RowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Modulus

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end Modulus
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section GenericDevice

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] {Y : Type} [MeasurableSpace Y]

end GenericDevice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private def PrimitiveAt₂ (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  (∀ j, evalHom p (x j) ∈ p.adicCompletionIntegers ℚ) ∧ ∃ j, Valued.v (evalHom p (x j)) = 1

private def NonzeroAt₂ (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  ∃ j, evalHom p (x j) ≠ 0

private def NonzeroArch₂ (x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  ∃ j, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j) ≠ 0

private def explicitRows₂ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) :=
  {x | (∀ p, p ∉ S → PrimitiveAt₂ p x) ∧ (∀ p ∈ S, NonzeroAt₂ p x) ∧ NonzeroArch₂ x}

private abbrev rowHaar₂ : Measure (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) :=
  Measure.pi fun _ : Fin 2 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

end RowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section SectionAndRowSets

section SectionHeads

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

open scoped RestrictedProduct

open Topology

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

private def rowAt₂ (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 2 → 𝔸) : Fin 2 → p.adicCompletion ℚ := fun j => (x j).2 p

private def rowArch₂ (w : InfinitePlace ℚ) (x : Fin 2 → 𝔸) : Fin 2 → w.Completion := fun j => (x j).1 w

private theorem rowAt_apply₂ (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 2 → 𝔸) (j : Fin 2) :
    rowAt₂ p x j = (x j).2 p := rfl

private theorem rowArch_apply₂ (w : InfinitePlace ℚ) (x : Fin 2 → 𝔸) (j : Fin 2) : rowArch₂ w x j = (x j).1 w := rfl

private theorem mem_explicitRows₂ {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {x : Fin 2 → 𝔸} :
    x ∈ explicitRows₂ S ↔ (∀ p, p ∉ S → PrimitiveAt₂ p x) ∧ (∀ p ∈ S, NonzeroAt₂ p x) ∧ NonzeroArch₂ x :=
  Iff.rfl

private theorem primitiveAt_iff₂ (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 2 → 𝔸) :
    PrimitiveAt₂ p x ↔ (∀ j, Valued.v (rowAt₂ p x j) ≤ 1) ∧ ∃ j, Valued.v (rowAt₂ p x j) = 1 :=
  Iff.rfl

private theorem nonzeroAt_iff₂ (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 2 → 𝔸) :
    NonzeroAt₂ p x ↔ ∃ j, rowAt₂ p x j ≠ 0 :=
  Iff.rfl

private theorem nonzeroArch_of_rowArch₂ {x : Fin 2 → 𝔸} {w : InfinitePlace ℚ} (h : ∃ j, rowArch₂ w x j ≠ 0) :
    NonzeroArch₂ x := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun h0 => hj (by rw [rowArch_apply₂, ← adeleArch_eq, h0]; rfl)⟩

private theorem continuous_rowAt₂ (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 2) :
    Continuous fun x : Fin 2 → 𝔸 => rowAt₂ p x j :=
  ((AdelicLevel.continuous_finAdeleEval (R := 𝓞 ℚ) (K := ℚ) p).comp
    (AdelicLevel.continuous_adeleFin (R := 𝓞 ℚ) (K := ℚ))).comp (continuous_apply j)

private theorem continuous_rowArch₂ (w : InfinitePlace ℚ) (j : Fin 2) :
    Continuous fun x : Fin 2 → 𝔸 => rowArch₂ w x j :=
  ((AdelicLevel.continuous_archEval (K := ℚ) w).comp (AdelicLevel.continuous_adeleArch (R := 𝓞 ℚ) (K := ℚ))).comp
    (continuous_apply j)

private theorem isClopen_valued_rowAt_eq_one₂ (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 2) :
    IsClopen {x : Fin 2 → 𝔸 | Valued.v (rowAt₂ p x j) = 1} :=
  (isClopen_setOf_valued_eq_one p).preimage (continuous_rowAt₂ p j)

private theorem measurableSet_valued_rowAt_eq_one₂ (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 2) :
    MeasurableSet {x : Fin 2 → 𝔸 | Valued.v (rowAt₂ p x j) = 1} :=
  (isClopen_valued_rowAt_eq_one₂ p j).isClosed.measurableSet

private theorem measurableSet_valued_rowAt_le_one₂ (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 2) :
    MeasurableSet {x : Fin 2 → 𝔸 | Valued.v (rowAt₂ p x j) ≤ 1} := by
  have h : IsClosed {y : p.adicCompletion ℚ | Valued.v y ≤ 1} := by
    simpa using AdelicLevel.isClosed_setOf_valued_le p (1 : p.adicCompletion ℚ) one_ne_zero
  exact (h.preimage (continuous_rowAt₂ p j)).measurableSet

private theorem measurableSet_rowArch_ne_zero₂ (w : InfinitePlace ℚ) (j : Fin 2) :
    MeasurableSet {x : Fin 2 → 𝔸 | rowArch₂ w x j ≠ 0} := by
  have h : IsOpen {y : w.Completion | y ≠ 0} := isOpen_ne
  exact (h.preimage (continuous_rowArch₂ w j)).measurableSet

private theorem rowAt_e₂₂ (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 2) : rowAt₂ p e₂ j = if j = 1 then 1 else 0 := by
  fin_cases j <;> rfl

private theorem rowArch_e₂₂ (w : InfinitePlace ℚ) (j : Fin 2) : rowArch₂ w e₂ j = if j = 1 then 1 else 0 := by
  fin_cases j <;> rfl

private theorem valued_rowAt_e₂_one₂ (p : HeightOneSpectrum (𝓞 ℚ)) : Valued.v (rowAt₂ p e₂ 1) = 1 := by
  rw [rowAt_e₂₂, if_pos rfl]
  exact map_one _

private theorem rowArch_e₂_one_ne_zero₂ (w : InfinitePlace ℚ) : rowArch₂ w e₂ 1 ≠ 0 := by
  rw [rowArch_e₂₂, if_pos rfl]
  exact one_ne_zero

private theorem primitiveAt_e₂₂ (p : HeightOneSpectrum (𝓞 ℚ)) : PrimitiveAt₂ p e₂ := by
  refine (primitiveAt_iff₂ p e₂).mpr ⟨fun j => ?_, 1, valued_rowAt_e₂_one₂ p⟩
  rw [rowAt_e₂₂]
  split_ifs <;> simp

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private abbrev residueChar (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.natGenerator v

private theorem residueChar_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (residueChar v).Prime :=
  Rat.HeightOneSpectrum.prime_natGenerator v

private theorem residueChar_injective : Function.Injective residueChar := fun _ _ h =>
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

private theorem natCast_mem_asIdeal_of_dvd {v : HeightOneSpectrum (𝓞 ℚ)} {n : ℕ} (h : residueChar v ∣ n) :
    (n : 𝓞 ℚ) ∈ v.asIdeal := by
  obtain ⟨x, hx, hxn⟩ := (Ideal.mem_map_iff_of_surjective
    (hf := (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).surjective)).mp ((Rat.HeightOneSpectrum.natGenerator_dvd_iff v).mp h)
  have hxn' : x = (n : 𝓞 ℚ) := (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective (by rw [hxn, map_natCast])
  exact hxn' ▸ hx

private theorem natCast_notMem_asIdeal_of_not_dvd {v : HeightOneSpectrum (𝓞 ℚ)} {n : ℕ} (h : ¬ residueChar v ∣ n) :
    (n : 𝓞 ℚ) ∉ v.asIdeal := fun hmem =>
  h ((Rat.HeightOneSpectrum.natGenerator_dvd_iff v).mpr
    (by simpa using Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem))

private abbrev levelRadius (N : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) : WithZero (Multiplicative ℤ) :=
  Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (N : 𝓞 ℚ))

private theorem levelRadius_le_one (N : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) : levelRadius N v ≤ 1 := by
  simp only [levelRadius]
  rw [AdelicTrace.valued_algebraMap]
  exact v.intValuation_le_one _

private theorem levelRadius_eq_one {N : ℕ} {v : HeightOneSpectrum (𝓞 ℚ)} (h : ¬ residueChar v ∣ N) :
    levelRadius N v = 1 := by
  simp only [levelRadius]
  rw [AdelicTrace.valued_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.mpr (natCast_notMem_asIdeal_of_not_dvd h)

private theorem levelRadius_lt_one {N : ℕ} {v : HeightOneSpectrum (𝓞 ℚ)} (h : residueChar v ∣ N) :
    levelRadius N v < 1 := by
  simp only [levelRadius]
  rw [AdelicTrace.valued_algebraMap]
  exact (v.intValuation_lt_one_iff_mem _).mpr (natCast_mem_asIdeal_of_dvd h)

private theorem levelRadius_le_of_dvd {M N : ℕ} (h : M ∣ N) (v : HeightOneSpectrum (𝓞 ℚ)) :
    levelRadius N v ≤ levelRadius M v := by
  obtain ⟨k, rfl⟩ := h
  simp only [levelRadius]
  rw [Nat.cast_mul, map_mul, map_mul]
  exact mul_le_of_le_one_right' (levelRadius_le_one k v)

private theorem valued_natCast_eq_one {v : HeightOneSpectrum (𝓞 ℚ)} {n : ℕ} (h : ¬ residueChar v ∣ n) :
    Valued.v (n : v.adicCompletion ℚ) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ)) n]
  exact levelRadius_eq_one h

private theorem valued_natCast_le_one (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Valued.v (n : v.adicCompletion ℚ) ≤ 1 := by
  rw [← map_natCast (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ)) n]
  exact levelRadius_le_one n v

private theorem valued_add_le_one_iff {v : HeightOneSpectrum (𝓞 ℚ)} {r : v.adicCompletion ℚ} (hr : Valued.v r ≤ 1)
    (y : v.adicCompletion ℚ) : Valued.v (y + r) ≤ 1 ↔ Valued.v y ≤ 1 :=
  ⟨fun h => by
    have h' : Valued.v (y + r - r) ≤ 1 := Valuation.map_sub_le _ h hr
    rwa [add_sub_cancel_right] at h', fun h => Valuation.map_add_le _ h hr⟩

private theorem forall_place_iff {P : HeightOneSpectrum (𝓞 ℚ) → Prop} (v : HeightOneSpectrum (𝓞 ℚ)) :
    (∀ w, P w) ↔ P v ∧ ∀ w, w ≠ v → P w :=
  ⟨fun h => ⟨h v, fun w _ => h w⟩, fun h w => by
    by_cases hw : w = v
    · exact hw ▸ h.1
    · exact h.2 w hw⟩

private theorem continuous_finPart_apply (v : HeightOneSpectrum (𝓞 ℚ)) : Continuous fun a : 𝔸 => a.2 v :=
  (AdelicLevel.continuous_finAdeleEval (R := 𝓞 ℚ) (K := ℚ) v).comp
    (AdelicLevel.continuous_adeleFin (R := 𝓞 ℚ) (K := ℚ))

private def finBox (N : ℕ) (a : 𝔸) : Set 𝔸 :=
  {b | ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((b - a).2 v) ≤ levelRadius N v}

private theorem mem_finBox {N : ℕ} {a b : 𝔸} :
    b ∈ finBox N a ↔ ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((b - a).2 v) ≤ levelRadius N v :=
  Iff.rfl

private theorem finBox_antitone {M N : ℕ} (h : M ∣ N) (a : 𝔸) : finBox N a ⊆ finBox M a := fun _ hb v =>
  (hb v).trans (levelRadius_le_of_dvd h v)

private theorem measurableSet_finBox (N : ℕ) (a : 𝔸) : MeasurableSet (finBox N a) := by
  have : finBox N a = ⋂ v : HeightOneSpectrum (𝓞 ℚ),
      (fun b : 𝔸 => (b - a).2 v) ⁻¹' {y | Valued.v y ≤ levelRadius N v} := by
    ext b
    simp only [finBox, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  refine MeasurableSet.iInter fun v => ?_
  exact ((AdelicTrace.isClosed_setOf_valued_le v _).preimage
    ((continuous_finPart_apply v).comp (continuous_id.sub continuous_const))).measurableSet

private def intMap (z : Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) : FiniteAdeleRing (𝓞 ℚ) ℚ :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) Filter.cofinite z

private theorem intMap_apply (z : Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) : intMap z v = (z v : v.adicCompletion ℚ) := rfl

private theorem nhds_zero_eq_map_intMap : nhds (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) = Filter.map intMap (nhds 0) := by
  have h0 : intMap 0 = 0 := FiniteAdeleRing.ext ℚ fun _ => rfl
  rw [← h0]
  exact RestrictedProduct.nhds_zero_eq_map_structureMap (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (B := fun v => v.adicCompletionIntegers ℚ) fun _ => Valued.isOpen_valuationSubring _

private theorem finBox_mem_nhds {N : ℕ} (hN : N ≠ 0) (a : 𝔸) : finBox N a ∈ nhds a := by
  have himg : intMap '' AdelicTrace.valBox ℚ N ∈ nhds (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    rw [nhds_zero_eq_map_intMap]
    exact Filter.image_mem_map (AdelicTrace.valBox_mem_nhds_zero (F := ℚ) hN)
  have hpre : (fun b : 𝔸 => b.2 - a.2) ⁻¹' (intMap '' AdelicTrace.valBox ℚ N) ∈ nhds a :=
    (continuous_snd.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using himg)
  refine Filter.mem_of_superset hpre fun b hb => mem_finBox.mpr fun v => ?_
  obtain ⟨z, hz, hzb⟩ := hb
  have h : (b - a).2 v = (z v : v.adicCompletion ℚ) := by
    rw [← intMap_apply, hzb]
    rfl
  rw [h]
  exact hz v

private theorem exists_finBox_subset {a : 𝔸} {U : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hU : U ∈ nhds a.2) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ b : 𝔸, b ∈ finBox N a → b.2 ∈ U := by
  have hU0 : (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => a.2 + y) ⁻¹' U ∈ nhds (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
  rw [nhds_zero_eq_map_intMap, Filter.mem_map] at hU0
  obtain ⟨N, hN, hbox⟩ := AdelicTrace.exists_valBox_subset hU0
  refine ⟨N, hN, fun b hb => ?_⟩
  have hint : ∀ v : HeightOneSpectrum (𝓞 ℚ), (b - a).2 v ∈ v.adicCompletionIntegers ℚ := fun v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ((hb v).trans (levelRadius_le_one N v))
  let z : Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ := fun v => ⟨(b - a).2 v, hint v⟩
  have hz : z ∈ AdelicTrace.valBox ℚ N := AdelicTrace.mem_valBox.mpr fun v => hb v
  have hmem := hbox hz
  have heq : intMap z = b.2 - a.2 := FiniteAdeleRing.ext ℚ fun _ => rfl
  rw [Set.mem_preimage, Set.mem_preimage, heq, add_sub_cancel] at hmem
  exact hmem

private theorem exists_open_finBox_subset {a : 𝔸} {V : Set 𝔸} (hV : V ∈ nhds a) :
    ∃ (W : Set (InfiniteAdeleRing ℚ)) (K : Set (InfiniteAdeleRing ℚ)) (N : ℕ), IsOpen W ∧ a.1 ∈ W ∧ IsCompact K ∧
      W ⊆ K ∧ N ≠ 0 ∧ ∀ b : 𝔸, b.1 ∈ W → b ∈ finBox N a → b ∈ V := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨u, hu, s, hs, hus⟩ := mem_nhds_prod_iff.mp hV
  obtain ⟨K, hKa, -, hK⟩ := LocallyCompactSpace.local_compact_nhds a₁ Set.univ Filter.univ_mem
  obtain ⟨W, hWuK, hWo, haW⟩ := mem_nhds_iff.mp (Filter.inter_mem hu hKa)
  obtain ⟨N, hN, hbox⟩ := exists_finBox_subset (a := (a₁, a₂)) hs
  exact ⟨W, K, N, hWo, haW, hK, fun y hy => (hWuK hy).2, hN, fun b hb1 hb2 =>
    hus (Set.mem_prod.mpr ⟨(hWuK hb1).1, hbox b hb2⟩)⟩

private theorem e₂_one_fin₂ (v : HeightOneSpectrum (𝓞 ℚ)) : (e₂ 1).2 v = 1 := rfl

private theorem valued_e₂_fin_le_one₂ (j : Fin 2) (v : HeightOneSpectrum (𝓞 ℚ)) : Valued.v ((e₂ j).2 v) ≤ 1 :=
  ((primitiveAt_iff₂ v e₂).mp (primitiveAt_e₂₂ v)).1 j

private def goodRows₂ (W : Fin 2 → Set (InfiniteAdeleRing ℚ)) (N : ℕ) : Set (Fin 2 → 𝔸) :=
  {x | (∀ j, (x j).1 ∈ W j ∧ x j ∈ finBox N (e₂ j)) ∧ rowArch₂ default x 1 ≠ 0}

private theorem mem_goodRows₂ {W : Fin 2 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 2 → 𝔸} :
    x ∈ goodRows₂ W N ↔ (∀ j, (x j).1 ∈ W j ∧ x j ∈ finBox N (e₂ j)) ∧ rowArch₂ default x 1 ≠ 0 :=
  Iff.rfl

private theorem measurableSet_goodRows₂ {W : Fin 2 → Set (InfiniteAdeleRing ℚ)} (hW : ∀ j, IsOpen (W j)) (N : ℕ) :
    MeasurableSet (goodRows₂ W N) := by
  have : goodRows₂ W N = (⋂ j, (fun x : Fin 2 → 𝔸 => x j) ⁻¹' ((fun b : 𝔸 => b.1) ⁻¹' W j ∩ finBox N (e₂ j))) ∩
      {x | rowArch₂ default x 1 ≠ 0} := by
    ext x
    simp only [goodRows₂, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  refine (MeasurableSet.iInter fun j => measurable_pi_apply j ?_).inter (measurableSet_rowArch_ne_zero₂ default 1)
  have hWj : IsOpen ((fun b : 𝔸 => b.1) ⁻¹' W j) := (hW j).preimage continuous_fst
  exact hWj.measurableSet.inter (measurableSet_finBox N (e₂ j))

private theorem goodRows_mem_nhds₂ {W : Fin 2 → Set (InfiniteAdeleRing ℚ)} (hW : ∀ j, IsOpen (W j))
    (hW₃ : ∀ j, (e₂ j).1 ∈ W j) {N : ℕ} (hN : N ≠ 0) : goodRows₂ W N ∈ nhds e₂ := by
  have hj : ∀ j : Fin 2, (fun x : Fin 2 → 𝔸 => x j) ⁻¹' (Prod.fst ⁻¹' W j ∩ finBox N (e₂ j)) ∈ nhds e₂ := fun j =>
    (continuous_apply j).continuousAt.preimage_mem_nhds
      (Filter.inter_mem (continuous_fst.continuousAt.preimage_mem_nhds ((hW j).mem_nhds (hW₃ j)))
        (finBox_mem_nhds hN (e₂ j)))
  have harch : {x : Fin 2 → 𝔸 | rowArch₂ default x 1 ≠ 0} ∈ nhds e₂ :=
    (continuous_rowArch₂ default 1).continuousAt.eventually_ne (rowArch_e₂_one_ne_zero₂ default)
  filter_upwards [Filter.iInter_mem.mpr hj, harch] with x hx hx'
  exact mem_goodRows₂.mpr ⟨fun j => Set.mem_iInter.mp hx j, hx'⟩

private theorem goodRows_subset_pi₂ {W K : Fin 2 → Set (InfiniteAdeleRing ℚ)} (hWK : ∀ j, W j ⊆ K j) (N : ℕ) :
    goodRows₂ W N ⊆ Set.univ.pi fun j => K j ×ˢ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro x hx j _
  obtain ⟨hx, -⟩ := mem_goodRows₂.mp hx
  refine Set.mem_prod.mpr ⟨hWK j (hx j).1, fun v => ?_⟩
  have h : (x j).2 v = (x j - e₂ j).2 v + (e₂ j).2 v := by rw [← fin_add_apply, sub_add_cancel]
  rw [h]
  refine add_mem ?_ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (valued_e₂_fin_le_one₂ j v))
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (((hx j).2 v).trans (levelRadius_le_one N v))

private theorem measure_goodRows_ne_top₂ {W K : Fin 2 → Set (InfiniteAdeleRing ℚ)} (hK : ∀ j, IsCompact (K j))
    (hWK : ∀ j, W j ⊆ K j) (N : ℕ) : rowHaar₂ (goodRows₂ W N) ≠ ⊤ :=
  ((measure_mono (goodRows_subset_pi₂ hWK N)).trans_lt (IsFiniteMeasureOnCompacts.lt_top_of_isCompact
    (isCompact_univ_pi fun j => (hK j).prod (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 ℚ) ℚ)))).ne

private theorem valued_rowAt_le_one_of_mem_goodRows₂ {W : Fin 2 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 2 → 𝔸}
    (hx : x ∈ goodRows₂ W N) (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 2) : Valued.v (rowAt₂ v x j) ≤ 1 := by
  have h : rowAt₂ v x j = (x j - e₂ j).2 v + (e₂ j).2 v := by rw [rowAt_apply₂, ← fin_add_apply, sub_add_cancel]
  rw [h]
  exact Valuation.map_add_le _ (((mem_goodRows₂.mp hx).1 j).2 v |>.trans (levelRadius_le_one N v))
    (valued_e₂_fin_le_one₂ j v)

private theorem valued_rowAt_one_of_mem_goodRows₂ {W : Fin 2 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 2 → 𝔸}
    (hx : x ∈ goodRows₂ W N) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : residueChar v ∣ N) : Valued.v (rowAt₂ v x 1) = 1 := by
  have h : rowAt₂ v x 1 = 1 + (x 1 - e₂ 1).2 v := by
    rw [rowAt_apply₂, add_comm, ← e₂_one_fin₂ v, ← fin_add_apply, sub_add_cancel]
  rw [h]
  exact Valuation.map_one_add_of_lt _ (((mem_goodRows₂.mp hx).1 1).2 v |>.trans_lt (levelRadius_lt_one hv))

private theorem primitiveAt_of_mem_goodRows₂ {W : Fin 2 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 2 → 𝔸}
    (hx : x ∈ goodRows₂ W N) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : residueChar v ∣ N) : PrimitiveAt₂ v x :=
  (primitiveAt_iff₂ v x).mpr ⟨valued_rowAt_le_one_of_mem_goodRows₂ hx v, 1, valued_rowAt_one_of_mem_goodRows₂ hx hv⟩

private theorem nonzeroAt_of_mem_goodRows₂ {W : Fin 2 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 2 → 𝔸}
    (hx : x ∈ goodRows₂ W N) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : residueChar v ∣ N) : NonzeroAt₂ v x :=
  (nonzeroAt_iff₂ v x).mpr ⟨1, fun h => by
    have h1 := valued_rowAt_one_of_mem_goodRows₂ hx hv
    rw [h, map_zero] at h1
    exact zero_ne_one h1⟩

private abbrev singleAt (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ) : 𝔸 :=
  StandardAddChar.adeleSingleAt ℚ v r

private theorem singleAt_arch (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ) (w : InfinitePlace ℚ) :
    (singleAt v r).1 w = 0 := rfl

private theorem singleAt_fin_self (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ) : (singleAt v r).2 v = r :=
  StandardAddChar.finAdeleSingleAt_apply_self ℚ v r

private theorem singleAt_fin_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ) {w : HeightOneSpectrum (𝓞 ℚ)}
    (h : w ≠ v) : (singleAt v r).2 w = 0 :=
  StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ v r h

private theorem fst_add_singleAt (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ) (b : 𝔸) :
    (b + singleAt v r).1 = b.1 := by
  funext w
  rw [arch_add_apply, singleAt_arch, add_zero]

private theorem add_singleAt_mem_finBox_iff {N : ℕ} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : levelRadius N v = 1)
    {r : v.adicCompletion ℚ} (hr : Valued.v r ≤ 1) (a b : 𝔸) : b + singleAt v r ∈ finBox N a ↔ b ∈ finBox N a := by
  have hcomp : ∀ w : HeightOneSpectrum (𝓞 ℚ), (b + singleAt v r - a).2 w = (b - a).2 w + (singleAt v r).2 w :=
    fun w => by rw [add_sub_right_comm, fin_add_apply]
  simp only [mem_finBox, hcomp]
  refine (forall_place_iff v).trans (Iff.trans ?_ (forall_place_iff v).symm)
  rw [singleAt_fin_self, hv]
  refine and_congr (valued_add_le_one_iff hr _) (forall_congr' fun w => forall_congr' fun hw => ?_)
  rw [singleAt_fin_of_ne v r hw, add_zero]

private abbrev shiftRow₂ (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 2) (r : v.adicCompletion ℚ) : Fin 2 → 𝔸 :=
  Pi.single j (singleAt v r)

private theorem shiftRow_apply_fst₂ (v : HeightOneSpectrum (𝓞 ℚ)) (j i : Fin 2) (r : v.adicCompletion ℚ)
    (w : InfinitePlace ℚ) : (shiftRow₂ v j r i).1 w = 0 := by
  by_cases h : i = j
  · rw [h]
    simp only [shiftRow₂, Pi.single_eq_same, singleAt_arch]
  · simp only [shiftRow₂, Pi.single_eq_of_ne h, arch_zero_apply]

private theorem rowArch_add_shiftRow₂ (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 2) (r : v.adicCompletion ℚ)
    (x : Fin 2 → 𝔸) (w : InfinitePlace ℚ) (i : Fin 2) : rowArch₂ w (x + shiftRow₂ v j r) i = rowArch₂ w x i := by
  rw [rowArch_apply₂, rowArch_apply₂, Pi.add_apply, arch_add_apply, shiftRow_apply_fst₂, add_zero]

private theorem rowAt_add_shiftRow_of_ne₂ (v : HeightOneSpectrum (𝓞 ℚ)) (j i : Fin 2) (h : i ≠ j)
    (r : v.adicCompletion ℚ) (x : Fin 2 → 𝔸) : rowAt₂ v (x + shiftRow₂ v j r) i = rowAt₂ v x i := by
  simp only [rowAt_apply₂, Pi.add_apply, shiftRow₂, Pi.single_eq_of_ne h, add_zero]

private theorem rowAt_shiftRow_add₂ (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 2) (r : v.adicCompletion ℚ)
    (x : Fin 2 → 𝔸) : rowAt₂ v (shiftRow₂ v j r + x) j = r + rowAt₂ v x j := by
  simp only [rowAt_apply₂, Pi.add_apply, shiftRow₂, Pi.single_eq_same, fin_add_apply, singleAt_fin_self]

private theorem add_shiftRow_mem_goodRows_iff₂ {W : Fin 2 → Set (InfiniteAdeleRing ℚ)} {N : ℕ}
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : levelRadius N v = 1) (j : Fin 2) {r : v.adicCompletion ℚ} (hr : Valued.v r ≤ 1)
    (x : Fin 2 → 𝔸) : x + shiftRow₂ v j r ∈ goodRows₂ W N ↔ x ∈ goodRows₂ W N := by
  simp only [mem_goodRows₂, rowArch_add_shiftRow₂]
  refine and_congr (forall_congr' fun i => ?_) Iff.rfl
  by_cases h : i = j
  · rw [h]
    simp only [Pi.add_apply, shiftRow₂, Pi.single_eq_same]
    rw [fst_add_singleAt, add_singleAt_mem_finBox_iff hv hr]
  · simp only [Pi.add_apply, shiftRow₂, Pi.single_eq_of_ne h, add_zero]

private theorem measurableSet_valued_rowAt_lt_one₂ (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 2) :
    MeasurableSet {x : Fin 2 → 𝔸 | Valued.v (rowAt₂ v x j) < 1} := by
  have : {x : Fin 2 → 𝔸 | Valued.v (rowAt₂ v x j) < 1} =
      {x | Valued.v (rowAt₂ v x j) ≤ 1} \ {x | Valued.v (rowAt₂ v x j) = 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_diff, lt_iff_le_and_ne]
  rw [this]
  exact (measurableSet_valued_rowAt_le_one₂ v j).diff (measurableSet_valued_rowAt_eq_one₂ v j)

private theorem residueChar_mul_measure_le₂ {Q : Set (Fin 2 → 𝔸)} (hQ : MeasurableSet Q) (v : HeightOneSpectrum (𝓞 ℚ))
    (j : Fin 2) (hstab : ∀ r : v.adicCompletion ℚ, Valued.v r ≤ 1 → ∀ x, x + shiftRow₂ v j r ∈ Q ↔ x ∈ Q) :
    (residueChar v : ℝ≥0∞) * rowHaar₂ (Q ∩ {x | Valued.v (rowAt₂ v x j) < 1}) ≤ rowHaar₂ Q := by
  have hDm : MeasurableSet (Q ∩ {x | Valued.v (rowAt₂ v x j) < 1}) :=
    hQ.inter (measurableSet_valued_rowAt_lt_one₂ v j)
  let T : ℕ → Set (Fin 2 → 𝔸) := fun k =>
    (fun x => shiftRow₂ v j (k : v.adicCompletion ℚ) + x) ⁻¹' (Q ∩ {x | Valued.v (rowAt₂ v x j) < 1})
  have hTm : ∀ k, MeasurableSet (T k) := fun k => measurable_const_add _ hDm
  have hTμ : ∀ k, rowHaar₂ (T k) = rowHaar₂ (Q ∩ {x | Valued.v (rowAt₂ v x j) < 1}) :=
    fun k => measure_preimage_add _ _ _
  have hTQ : ∀ k, T k ⊆ Q := fun k x hx => by
    have hx' : shiftRow₂ v j (k : v.adicCompletion ℚ) + x ∈ Q := hx.1
    rw [add_comm] at hx'
    exact (hstab _ (valued_natCast_le_one v k) x).mp hx'
  have hdisj : ∀ k l : ℕ, k < l → l < residueChar v → Disjoint (T k) (T l) := fun k l hkl hl => by
    refine Set.disjoint_left.mpr fun x hk hl' => ?_
    have h1 : Valued.v ((k : v.adicCompletion ℚ) + rowAt₂ v x j) < 1 := by
      have h := hk.2
      rwa [Set.mem_setOf_eq, rowAt_shiftRow_add₂] at h
    have h2 : Valued.v ((l : v.adicCompletion ℚ) + rowAt₂ v x j) < 1 := by
      have h := hl'.2
      rwa [Set.mem_setOf_eq, rowAt_shiftRow_add₂] at h
    have h3 : Valued.v ((l - k : ℕ) : v.adicCompletion ℚ) = 1 :=
      valued_natCast_eq_one (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hkl) (by omega))
    have h4 : ((l - k : ℕ) : v.adicCompletion ℚ) =
        ((l : v.adicCompletion ℚ) + rowAt₂ v x j) - ((k : v.adicCompletion ℚ) + rowAt₂ v x j) := by
      rw [Nat.cast_sub hkl.le]
      ring
    rw [h4] at h3
    have h5 := Valuation.map_sub_lt _ h2 h1
    rw [h3] at h5
    exact lt_irrefl _ h5
  have hunion : rowHaar₂ (⋃ k ∈ Finset.range (residueChar v), T k) =
      (residueChar v : ℝ≥0∞) * rowHaar₂ (Q ∩ {x | Valued.v (rowAt₂ v x j) < 1}) := by
    rw [measure_biUnion_finset ?_ fun k _ => hTm k]
    · simp only [hTμ, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · intro k hk l hl hkl
      rcases hkl.lt_or_gt with h | h
      · exact hdisj k l h (Finset.mem_range.mp hl)
      · exact (hdisj l k h (Finset.mem_range.mp hk)).symm
  rw [← hunion]
  exact measure_mono (Set.iUnion₂_subset fun k _ => hTQ k)

private def tailTerm (i : ℕ) : ℝ≥0∞ := if 3 ≤ i then ((i : ℝ≥0∞) ^ 2)⁻¹ else 0

private theorem sum_range_tailTerm_le (n : ℕ) : ∑ i ∈ Finset.range n, tailTerm i ≤ ENNReal.ofReal (2 / 3) := by
  calc ∑ i ∈ Finset.range n, tailTerm i = ∑ i ∈ Finset.Ioo 2 n, ((i : ℝ≥0∞) ^ 2)⁻¹ := by
        simp only [tailTerm]
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
        constructor <;> intro h <;> omega
    _ = ∑ i ∈ Finset.Ioo 2 n, ENNReal.ofReal (((i : ℝ) ^ 2)⁻¹) := Finset.sum_congr rfl fun i hi => by
        have hi0 : (0 : ℝ) < i := Nat.cast_pos.mpr (by have := (Finset.mem_Ioo.mp hi).1; omega)
        rw [ENNReal.ofReal_inv_of_pos (pow_pos hi0 2), ENNReal.ofReal_pow hi0.le, ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (∑ i ∈ Finset.Ioo 2 n, ((i : ℝ) ^ 2)⁻¹) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity).symm
    _ ≤ ENNReal.ofReal (2 / 3) :=
        ENNReal.ofReal_le_ofReal ((sum_Ioo_inv_sq_le (α := ℝ) 2 n).trans (by norm_num))

private theorem tsum_tailTerm_le : ∑' i, tailTerm i ≤ ENNReal.ofReal (2 / 3) :=
  ENNReal.tsum_le_of_sum_range_le sum_range_tailTerm_le

private theorem tailTerm_residueChar {v : HeightOneSpectrum (𝓞 ℚ)} {N : ℕ} (h2 : 2 ∣ N) (hv : ¬ residueChar v ∣ N) :
    tailTerm (residueChar v) = ((residueChar v : ℝ≥0∞) * residueChar v)⁻¹ := by
  have hne : residueChar v ≠ 2 := fun h => hv (h ▸ h2)
  have h3 : 3 ≤ residueChar v := by
    have := (residueChar_prime v).two_le
    omega
  rw [tailTerm, if_pos h3, pow_two]

private theorem measure_badRows_le₂ {W : Fin 2 → Set (InfiniteAdeleRing ℚ)} (hW : ∀ j, IsOpen (W j)) {N : ℕ}
    (h2 : 2 ∣ N) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ residueChar v ∣ N) :
    rowHaar₂ ((goodRows₂ W N ∩ {x | Valued.v (rowAt₂ v x 1) < 1}) ∩ {x | Valued.v (rowAt₂ v x 0) < 1}) ≤
      rowHaar₂ (goodRows₂ W N) * tailTerm (residueChar v) := by
  have hrad : levelRadius N v = 1 := levelRadius_eq_one hv
  have hq0 : (residueChar v : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (residueChar_prime v).ne_zero
  have hqq0 : (residueChar v : ℝ≥0∞) * residueChar v ≠ 0 := mul_ne_zero hq0 hq0
  have hqqt : (residueChar v : ℝ≥0∞) * residueChar v ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)
  have hstep1 := residueChar_mul_measure_le₂ (measurableSet_goodRows₂ hW N) v 1 fun r hr x =>
    add_shiftRow_mem_goodRows_iff₂ hrad 1 hr x
  have hstep0 := residueChar_mul_measure_le₂
    ((measurableSet_goodRows₂ hW N).inter (measurableSet_valued_rowAt_lt_one₂ v 1)) v 0 fun r hr x => by
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, add_shiftRow_mem_goodRows_iff₂ hrad 0 hr x,
        rowAt_add_shiftRow_of_ne₂ v 0 1 (by decide) r x]
  have hboth : (residueChar v : ℝ≥0∞) * residueChar v *
      rowHaar₂ ((goodRows₂ W N ∩ {x | Valued.v (rowAt₂ v x 1) < 1}) ∩ {x | Valued.v (rowAt₂ v x 0) < 1}) ≤
        rowHaar₂ (goodRows₂ W N) := by
    rw [mul_assoc]
    exact (mul_le_mul' le_rfl hstep0).trans hstep1
  rw [tailTerm_residueChar h2 hv, ← div_eq_mul_inv]
  rw [mul_comm] at hboth
  exact (ENNReal.le_div_iff_mul_le (Or.inl hqq0) (Or.inl hqqt)).mpr hboth

private theorem pos_rowHaar_inter_explicitRows₂ (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {O : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)} (hO : O ∈ nhds e₂) : 0 < rowHaar₂ (O ∩ explicitRows₂ S) := by
  rw [nhds_pi, Filter.mem_pi] at hO
  obtain ⟨I, -, t, ht, hIt⟩ := hO
  choose W K N hWo hW₃ hK hWK hN hsub using fun j => exists_open_finBox_subset (ht j)
  obtain ⟨M, hM0, hNM, h2M, hSM⟩ : ∃ M : ℕ, M ≠ 0 ∧ (∀ j, N j ∣ M) ∧ 2 ∣ M ∧ ∀ v ∈ S, residueChar v ∣ M :=
    ⟨(∏ j, N j) * 2 * ∏ v ∈ S, residueChar v,
      mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hN j) two_ne_zero)
        (Finset.prod_ne_zero_iff.mpr fun v _ => (residueChar_prime v).ne_zero),
      fun j => ((Finset.dvd_prod_of_mem N (Finset.mem_univ j)).mul_right _).mul_right _,
      (dvd_mul_left 2 _).mul_right _,
      fun v hv => dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hv) _⟩
  have hQO : goodRows₂ W M ⊆ O := fun x hx => hIt fun j _ =>
    hsub j (x j) ((mem_goodRows₂.mp hx).1 j).1 (finBox_antitone (hNM j) _ ((mem_goodRows₂.mp hx).1 j).2)
  refine lt_of_lt_of_le ?_ (measure_mono (Set.inter_subset_inter_left _ hQO))
  have hQpos : 0 < rowHaar₂ (goodRows₂ W M) := Measure.measure_pos_of_nonempty_interior (μ := rowHaar₂)
    ⟨e₂, mem_interior_iff_mem_nhds.mpr (goodRows_mem_nhds₂ hWo hW₃ hM0)⟩
  have hQtop : rowHaar₂ (goodRows₂ W M) ≠ ⊤ := measure_goodRows_ne_top₂ hK hWK M
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  let E : {v : HeightOneSpectrum (𝓞 ℚ) // ¬ residueChar v ∣ M} → Set (Fin 2 → 𝔸) := fun v =>
    (goodRows₂ W M ∩ {x | Valued.v (rowAt₂ v.1 x 1) < 1}) ∩ {x | Valued.v (rowAt₂ v.1 x 0) < 1}
  have hcover : goodRows₂ W M ⊆ (goodRows₂ W M ∩ explicitRows₂ S) ∪ ⋃ v, E v := by
    intro x hx
    by_cases hxS : x ∈ explicitRows₂ S
    · exact Or.inl ⟨hx, hxS⟩
    · have hprim : ¬ ∀ v, v ∉ S → PrimitiveAt₂ v x := fun h =>
        hxS (mem_explicitRows₂.mpr ⟨h, fun v hv => nonzeroAt_of_mem_goodRows₂ hx (hSM v hv),
          nonzeroArch_of_rowArch₂ ⟨1, (mem_goodRows₂.mp hx).2⟩⟩)
      simp only [not_forall] at hprim
      obtain ⟨v, -, hvbad⟩ := hprim
      have hvM : ¬ residueChar v ∣ M := fun hdvd => hvbad (primitiveAt_of_mem_goodRows₂ hx hdvd)
      have hle := valued_rowAt_le_one_of_mem_goodRows₂ hx v
      refine Or.inr (Set.mem_iUnion.mpr ⟨⟨v, hvM⟩, ⟨hx, ?_⟩, ?_⟩)
      · exact lt_of_le_of_ne (hle 1) fun h1 => hvbad ((primitiveAt_iff₂ v x).mpr ⟨hle, 1, h1⟩)
      · exact lt_of_le_of_ne (hle 0) fun h1 => hvbad ((primitiveAt_iff₂ v x).mpr ⟨hle, 0, h1⟩)
  have hE : ∀ v, rowHaar₂ (E v) ≤ rowHaar₂ (goodRows₂ W M) * tailTerm (residueChar v.1) := fun v =>
    measure_badRows_le₂ hWo h2M v.2
  have hinj : Function.Injective fun v : {v : HeightOneSpectrum (𝓞 ℚ) // ¬ residueChar v ∣ M} => residueChar v.1 :=
    residueChar_injective.comp Subtype.val_injective
  have hsum : ∑' v, rowHaar₂ (E v) ≤ rowHaar₂ (goodRows₂ W M) * ENNReal.ofReal (2 / 3) :=
    calc ∑' v, rowHaar₂ (E v)
      _ ≤ ∑' v : {v : HeightOneSpectrum (𝓞 ℚ) // ¬ residueChar v ∣ M},
            rowHaar₂ (goodRows₂ W M) * tailTerm (residueChar v.1) :=
          ENNReal.tsum_le_tsum hE
      _ = rowHaar₂ (goodRows₂ W M) *
            ∑' v : {v : HeightOneSpectrum (𝓞 ℚ) // ¬ residueChar v ∣ M}, tailTerm (residueChar v.1) :=
          ENNReal.tsum_mul_left
      _ ≤ rowHaar₂ (goodRows₂ W M) * ∑' i, tailTerm i :=
          mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hinj tailTerm)
      _ ≤ rowHaar₂ (goodRows₂ W M) * ENNReal.ofReal (2 / 3) := mul_le_mul' le_rfl tsum_tailTerm_le
  have hlt : rowHaar₂ (goodRows₂ W M) * ENNReal.ofReal (2 / 3) < rowHaar₂ (goodRows₂ W M) := by
    calc rowHaar₂ (goodRows₂ W M) * ENNReal.ofReal (2 / 3)
      _ = ENNReal.ofReal (2 / 3) * rowHaar₂ (goodRows₂ W M) := mul_comm _ _
      _ < 1 * rowHaar₂ (goodRows₂ W M) :=
          ENNReal.mul_lt_mul_left hQpos.ne' hQtop (ENNReal.ofReal_lt_one.mpr (by norm_num))
      _ = rowHaar₂ (goodRows₂ W M) := one_mul _
  refine lt_irrefl _ (hlt.trans_le ?_)
  calc rowHaar₂ (goodRows₂ W M) ≤ rowHaar₂ ((goodRows₂ W M ∩ explicitRows₂ S) ∪ ⋃ v, E v) := measure_mono hcover
    _ ≤ rowHaar₂ (goodRows₂ W M ∩ explicitRows₂ S) + rowHaar₂ (⋃ v, E v) := measure_union_le _ _
    _ = rowHaar₂ (⋃ v, E v) := by rw [h0, zero_add]
    _ ≤ ∑' v, rowHaar₂ (E v) := measure_iUnion_le _
    _ ≤ rowHaar₂ (goodRows₂ W M) * ENNReal.ofReal (2 / 3) := hsum

private theorem explicitRows₂_eq_goodLeviRows (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    explicitRows₂ S = goodLeviRows S :=
  rfl

private theorem leviHaar_goodLeviRows_pos (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : 0 < leviHaar (goodLeviRows S) := by
  have h := pos_rowHaar_inter_explicitRows₂ S (O := Set.univ) Filter.univ_mem
  rwa [Set.univ_inter, explicitRows₂_eq_goodLeviRows] at h

end SectionHeads
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end SectionAndRowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end MirabolicLeviFibration
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end RowMass
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section FibrationIdentity

noncomputable section

namespace MirabolicLeviFibration

section Furniture

end Furniture
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end RowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Modulus

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end Modulus
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section GenericDevice

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] {Y : Type} [MeasurableSpace Y]

end GenericDevice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private abbrev rowHaar : Measure (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

end RowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section DeviceIdentities

section DeviceAlgebra

private theorem bottomRow_mul_eq_vecMul (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    bottomRow (g * h) = bottomRow g ᵥ* (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := by
  rw [bottomRow_mul]
  funext j
  simp [Matrix.vecMul, dotProduct]

private theorem e₃_vecMul (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    e₃ ᵥ* (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = bottomRow h := by
  funext j
  simp [e₃, Matrix.vecMul, dotProduct, bottomRow]

private theorem bottomRow_mul_of_mem {p : AdelicGL 3 (𝓞 ℚ) ℚ} (hp : p ∈ mirabolic)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : bottomRow (p * g) = bottomRow g := by
  rw [bottomRow_mul_eq_vecMul, show bottomRow p = e₃ from hp, e₃_vecMul]

private theorem mul_inv_mem_mirabolic_iff (a b : AdelicGL 3 (𝓞 ℚ) ℚ) :
    a * b⁻¹ ∈ mirabolic ↔ bottomRow a = bottomRow b := by
  constructor
  · intro h
    have := bottomRow_mul_of_mem h b
    rwa [inv_mul_cancel_right] at this
  · intro h
    show bottomRow (a * b⁻¹) = e₃
    rw [bottomRow_mul_eq_vecMul, h, ← e₃_vecMul b, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.vecMul_one]

end DeviceAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end DeviceIdentities
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section JacobianAndModulus

section JacobianUnimodular

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

open scoped NNReal Pointwise

open NumberField.AdelicHaar

section Generation

variable {R : Type*} [CommRing R] {M : Type*} [CommGroup M]

private def HasIdempotentPivots (R : Type*) [CommRing R] : Prop :=
  ∀ b c : Fin 3 → R, b ⬝ᵥ c = 1 → ∃ e : Fin 3 → R,
    (∀ i, e i * e i = e i) ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ e 0 + e 1 + e 2 = 1 ∧
      IsUnit (e 0 * c 0 + e 1 * c 1 + e 2 * c 2)

private def glOf (A B : Matrix (Fin 3) (Fin 3) R) (h : A * B = 1) : GL (Fin 3) R :=
  ⟨A, B, h, mul_eq_one_comm.mp h⟩

@[scoped simp] private theorem coe_glOf (A B : Matrix (Fin 3) (Fin 3) R) (h : A * B = 1) :
    ((glOf A B h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = A := rfl

private def tGL (i j : Fin 3) (hij : i ≠ j) (c : R) : GL (Fin 3) R :=
  glOf (transvection i j c) (transvection i j (-c))
    (by rw [transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero])

@[scoped simp] private theorem coe_tGL (i j : Fin 3) (hij : i ≠ j) (c : R) :
    ((tGL i j hij c : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = transvection i j c := rfl

private def dGL (d : Fin 3 → Rˣ) : GL (Fin 3) R :=
  glOf (diagonal fun i => (d i : R)) (diagonal fun i => ((d i)⁻¹ : Rˣ))
    (by rw [diagonal_mul_diagonal]; simp)

@[scoped simp] private theorem coe_dGL (d : Fin 3 → Rˣ) :
    ((dGL d : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = diagonal fun i => (d i : R) := rfl

private theorem coe_dGL_inv (d : Fin 3 → Rˣ) :
    (((dGL d)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = diagonal fun i => (((d i)⁻¹ : Rˣ) : R) := rfl

private theorem dGL_mul (d d' : Fin 3 → Rˣ) : dGL d * dGL d' = dGL (d * d') := by
  refine Units.ext ?_
  simp [diagonal_mul_diagonal]

private theorem apply_congr (ρ : GL (Fin 3) R →* M) {g h : GL (Fin 3) R}
    (hgh : (g : Matrix (Fin 3) (Fin 3) R) = h) : ρ g = ρ h := by
  rw [Units.ext hgh]

private theorem apply_tGL (h2 : IsUnit (2 : R)) (ρ : GL (Fin 3) R →* M) (i j : Fin 3) (hij : i ≠ j) (c : R) :
    ρ (tGL i j hij c) = 1 := by
  obtain ⟨w, hw⟩ := h2
  let d : Fin 3 → Rˣ := Function.update 1 i w
  have hdi : (d i : R) = 2 := by simp [d, hw]
  have hdj : ((d j)⁻¹ : Rˣ) = 1 := by simp [d, Function.update_of_ne (Ne.symm hij)]
  have hconj : ((dGL d * tGL i j hij c * (dGL d)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (tGL i j hij c * tGL i j hij c : GL (Fin 3) R) := by
    have hinv : (((dGL d)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = diagonal fun k => (((d k)⁻¹ : Rˣ) : R) :=
      rfl
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_dGL, coe_tGL, hinv,
      transvection_mul_transvection_same (h := hij)]
    ext a b
    rw [mul_diagonal, diagonal_mul]
    simp only [transvection, Matrix.add_apply, Matrix.single_apply]
    by_cases hab : a = b
    · subst hab
      have hne : ¬(i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
      simp [hne]
    · by_cases h' : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h'
        simp [Matrix.one_apply_ne hab, hdi, hdj, two_mul]
      · simp [Matrix.one_apply_ne hab, h']
  have key := apply_congr ρ hconj
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm, map_mul] at key
  exact (mul_eq_left.mp key.symm)

private def swap01 : Matrix (Fin 3) (Fin 3) R := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

private def swap02 : Matrix (Fin 3) (Fin 3) R := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

private theorem swap01_mul_self : (swap01 : Matrix (Fin 3) (Fin 3) R) * swap01 = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [swap01, Matrix.mul_apply, Fin.sum_univ_three]

private theorem swap02_mul_self : (swap02 : Matrix (Fin 3) (Fin 3) R) * swap02 = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [swap02, Matrix.mul_apply, Fin.sum_univ_three]

private theorem swap01_conj (a : Rˣ) :
    (swap01 : Matrix (Fin 3) (Fin 3) R) * (diagonal fun k => ((Function.update (1 : Fin 3 → Rˣ) 0 a k : Rˣ) : R)) *
      swap01 = diagonal fun k => ((Function.update (1 : Fin 3 → Rˣ) 1 a k : Rˣ) : R) := by
  ext x y; fin_cases x <;> fin_cases y <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [swap01, Function.update_apply]

private theorem swap02_conj (a : Rˣ) :
    (swap02 : Matrix (Fin 3) (Fin 3) R) * (diagonal fun k => ((Function.update (1 : Fin 3 → Rˣ) 0 a k : Rˣ) : R)) *
      swap02 = diagonal fun k => ((Function.update (1 : Fin 3 → Rˣ) 2 a k : Rˣ) : R) := by
  ext x y; fin_cases x <;> fin_cases y <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [swap02, Function.update_apply]

private theorem apply_conj_invol (ρ : GL (Fin 3) R →* M) (P : Matrix (Fin 3) (Fin 3) R) (hP : P * P = 1)
    (g h : GL (Fin 3) R) (hc : P * (g : Matrix (Fin 3) (Fin 3) R) * P = h) : ρ g = ρ h := by
  have hmat : ((glOf P P hP * g * glOf P P hP : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = h := by
    rw [Units.val_mul, Units.val_mul, coe_glOf, hc]
  rw [← apply_congr ρ hmat, map_mul, map_mul, mul_right_comm, ← map_mul]
  have h1 : glOf P P hP * glOf P P hP = (1 : GL (Fin 3) R) := Units.ext (by rw [Units.val_mul, coe_glOf, hP]; rfl)
  rw [h1, map_one, one_mul]

private theorem apply_dGL (hM3 : ∀ x : M, x ^ 3 = 1 → x = 1) (ρ : GL (Fin 3) R →* M)
    (hscalar : ∀ a : Rˣ, ρ (dGL fun _ => a) = 1) (d : Fin 3 → Rˣ) : ρ (dGL d) = 1 := by
  have h1 : ∀ a : Rˣ, ρ (dGL (Function.update 1 1 a)) = ρ (dGL (Function.update 1 0 a)) := fun a =>
    (apply_conj_invol ρ swap01 swap01_mul_self (dGL (Function.update 1 0 a)) (dGL (Function.update 1 1 a))
      (swap01_conj a)).symm
  have h2 : ∀ a : Rˣ, ρ (dGL (Function.update 1 2 a)) = ρ (dGL (Function.update 1 0 a)) := fun a =>
    (apply_conj_invol ρ swap02 swap02_mul_self (dGL (Function.update 1 0 a)) (dGL (Function.update 1 2 a))
      (swap02_conj a)).symm
  have hsplit : ∀ d : Fin 3 → Rˣ,
      dGL d = dGL (Function.update 1 0 (d 0)) * dGL (Function.update 1 1 (d 1)) * dGL (Function.update 1 2 (d 2)) := by
    intro d
    rw [dGL_mul, dGL_mul]
    congr 1
    ext k
    fin_cases k <;> simp
  have hθ : ∀ a : Rˣ, ρ (dGL (Function.update 1 0 a)) = 1 := by
    intro a
    refine hM3 _ ?_
    have := hscalar a
    rw [hsplit (fun _ => a), map_mul, map_mul, h1, h2] at this
    simpa [pow_succ] using this
  rw [hsplit d, map_mul, map_mul, hθ, h1, hθ, h2, hθ, one_mul, one_mul]

private theorem apply_invol (hM2 : ∀ x : M, x ^ 2 = 1 → x = 1) (ρ : GL (Fin 3) R →* M)
    (W : Matrix (Fin 3) (Fin 3) R) (hW : W * W = 1) : ρ (glOf W W hW) = 1 := by
  refine hM2 _ ?_
  have h1 : glOf W W hW * glOf W W hW = (1 : GL (Fin 3) R) := Units.ext (by rw [Units.val_mul, coe_glOf, hW]; rfl)
  rw [sq, ← map_mul, h1, map_one]

private def pivot₁ (e : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![e 0, e 1, e 2; e 1, e 0 + e 2, 0; e 2, 0, e 0 + e 1]

private def pivot₂ (f : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0; 0, f 0, f 1 + f 2; 0, f 1 + f 2, f 0]

section Pivots

variable {e : Fin 3 → R} (hii : ∀ i, e i * e i = e i) (hij : ∀ i j, i ≠ j → e i * e j = 0)
  (hsum : e 0 + e 1 + e 2 = 1)

include hii hij hsum

private theorem pivot₁_mul_self : pivot₁ e * pivot₁ e = 1 := by
  have h00 := hii 0; have h11 := hii 1; have h22 := hii 2
  have h01 := hij 0 1 (by decide); have h02 := hij 0 2 (by decide); have h12 := hij 1 2 (by decide)
  have h10 := hij 1 0 (by decide); have h20 := hij 2 0 (by decide); have h21 := hij 2 1 (by decide)
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pivot₁, Matrix.mul_apply, Fin.sum_univ_three, mul_add, add_mul, h00, h11, h22, h01, h02, h12, h10, h20,
      h21] <;>
    linear_combination hsum

private theorem pivot₂_mul_self : pivot₂ e * pivot₂ e = 1 := by
  have h00 := hii 0; have h11 := hii 1; have h22 := hii 2
  have h01 := hij 0 1 (by decide); have h02 := hij 0 2 (by decide); have h12 := hij 1 2 (by decide)
  have h10 := hij 1 0 (by decide); have h20 := hij 2 0 (by decide); have h21 := hij 2 1 (by decide)
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pivot₂, Matrix.mul_apply, Fin.sum_univ_three, mul_add, add_mul, h00, h11, h22, h01, h02, h12, h10, h20,
      h21] <;>
    linear_combination hsum

end Pivots
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem pivot₁_mul_apply (e : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (b : Fin 3) :
    (pivot₁ e * A) 0 b = e 0 * A 0 b + e 1 * A 1 b + e 2 * A 2 b := by
  simp [pivot₁, Matrix.mul_apply, Fin.sum_univ_three]

private theorem pivot₂_mul_apply₀ (f : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (b : Fin 3) :
    (pivot₂ f * A) 0 b = A 0 b := by
  simp [pivot₂, Matrix.mul_apply, Fin.sum_univ_three]

private theorem pivot₂_mul_apply₁ (f : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (b : Fin 3) :
    (pivot₂ f * A) 1 b = f 0 * A 1 b + (f 1 + f 2) * A 2 b := by
  simp [pivot₂, Matrix.mul_apply, Fin.sum_univ_three]

private theorem pivot₂_mul_apply₂ (f : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (b : Fin 3) :
    (pivot₂ f * A) 2 b = (f 1 + f 2) * A 1 b + f 0 * A 2 b := by
  simp [pivot₂, Matrix.mul_apply, Fin.sum_univ_three]

private theorem apply_of_offDiag_eq_zero (hM3 : ∀ x : M, x ^ 3 = 1 → x = 1) (ρ : GL (Fin 3) R →* M)
    (hscalar : ∀ a : Rˣ, ρ (dGL fun _ => a) = 1) (g : GL (Fin 3) R) (h01 : (g : Matrix (Fin 3) (Fin 3) R) 0 1 = 0)
    (h02 : (g : Matrix (Fin 3) (Fin 3) R) 0 2 = 0) (h10 : (g : Matrix (Fin 3) (Fin 3) R) 1 0 = 0)
    (h12 : (g : Matrix (Fin 3) (Fin 3) R) 1 2 = 0) (h20 : (g : Matrix (Fin 3) (Fin 3) R) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) R) 2 1 = 0) : ρ g = 1 := by
  have hdiag : (g : Matrix (Fin 3) (Fin 3) R) = diagonal fun k => (g : Matrix (Fin 3) (Fin 3) R) k k := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21]
  have hdet : IsUnit (∏ k, (g : Matrix (Fin 3) (Fin 3) R) k k) := by
    have := isUnits_det_units g
    rwa [hdiag, det_diagonal] at this
  rw [Fin.prod_univ_three, IsUnit.mul_iff, IsUnit.mul_iff] at hdet
  obtain ⟨⟨h0, h1⟩, h2⟩ := hdet
  let d : Fin 3 → Rˣ := ![h0.unit, h1.unit, h2.unit]
  have hd : (g : Matrix (Fin 3) (Fin 3) R) = (dGL d : GL (Fin 3) R) := by
    rw [hdiag, coe_dGL]
    congr 1
    ext k
    fin_cases k <;> simp [d]
  rw [apply_congr ρ hd]
  exact apply_dGL hM3 ρ hscalar d

private theorem eq_one_of_apply_scalar (hP : HasIdempotentPivots R) (h2 : IsUnit (2 : R))
    (hM2 : ∀ x : M, x ^ 2 = 1 → x = 1) (hM3 : ∀ x : M, x ^ 3 = 1 → x = 1) (ρ : GL (Fin 3) R →* M)
    (hscalar : ∀ a : Rˣ, ρ (dGL fun _ => a) = 1) (g : GL (Fin 3) R) : ρ g = 1 := by
  have hT : ∀ (i j : Fin 3) (hij : i ≠ j) (c : R), tGL i j hij c ∈ ρ.ker := fun i j hij c =>
    (MonoidHom.mem_ker).mpr (apply_tGL h2 ρ i j hij c)
  have hW : ∀ (W : Matrix (Fin 3) (Fin 3) R) (hW : W * W = 1), glOf W W hW ∈ ρ.ker := fun W hW =>
    (MonoidHom.mem_ker).mpr (apply_invol hM2 ρ W hW)
  rw [← MonoidHom.mem_ker]

  obtain ⟨e, hii, hij, hsum, hu⟩ := hP (fun j => ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 j)
    (fun i => (g : Matrix (Fin 3) (Fin 3) R) i 0) (by
      have := congrFun (congrFun (g.inv_mul) 0) 0
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
      exact this)
  refine (Subgroup.mul_mem_cancel_left (h := hW (pivot₁ e) (pivot₁_mul_self hii hij hsum))).mp ?_
  set g₁ : GL (Fin 3) R := glOf (pivot₁ e) (pivot₁ e) (pivot₁_mul_self hii hij hsum) * g with hg₁
  have h00 : IsUnit ((g₁ : Matrix (Fin 3) (Fin 3) R) 0 0) := by
    rw [hg₁, Units.val_mul, coe_glOf, pivot₁_mul_apply]; exact hu
  clear_value g₁
  obtain ⟨u, hu⟩ := h00

  set t₁ : R := -((g₁ : Matrix (Fin 3) (Fin 3) R) 1 0 * ((u⁻¹ : Rˣ) : R)) with ht₁
  set t₂ : R := -((g₁ : Matrix (Fin 3) (Fin 3) R) 2 0 * ((u⁻¹ : Rˣ) : R)) with ht₂
  refine (Subgroup.mul_mem_cancel_left (h := hT 2 0 (by decide) t₂)).mp
    ((Subgroup.mul_mem_cancel_left (h := hT 1 0 (by decide) t₁)).mp ?_)
  set g₂ : GL (Fin 3) R := tGL 1 0 (by decide) t₁ * (tGL 2 0 (by decide) t₂ * g₁) with hg₂
  have h₂00 : (g₂ : Matrix (Fin 3) (Fin 3) R) 0 0 = u := by
    simp [hg₂, transvection_mul_apply_of_ne, hu]
  have h₂10 : (g₂ : Matrix (Fin 3) (Fin 3) R) 1 0 = 0 := by
    simp only [hg₂, Units.val_mul, coe_tGL, transvection_mul_apply_same, ne_eq, Fin.reduceEq, not_false_eq_true,
      transvection_mul_apply_of_ne, ht₁, ← hu]
    linear_combination (-(g₁ : Matrix (Fin 3) (Fin 3) R) 1 0) * u.inv_mul
  have h₂20 : (g₂ : Matrix (Fin 3) (Fin 3) R) 2 0 = 0 := by
    simp only [hg₂, Units.val_mul, coe_tGL, transvection_mul_apply_same, ne_eq, Fin.reduceEq, not_false_eq_true,
      transvection_mul_apply_of_ne, ht₂, ← hu]
    linear_combination (-(g₁ : Matrix (Fin 3) (Fin 3) R) 2 0) * u.inv_mul
  clear_value g₂
  set s₁ : R := -(((u⁻¹ : Rˣ) : R) * (g₂ : Matrix (Fin 3) (Fin 3) R) 0 1) with hs₁
  set s₂ : R := -(((u⁻¹ : Rˣ) : R) * (g₂ : Matrix (Fin 3) (Fin 3) R) 0 2) with hs₂
  refine (Subgroup.mul_mem_cancel_right (h := hT 0 1 (by decide) s₁)).mp
    ((Subgroup.mul_mem_cancel_right (h := hT 0 2 (by decide) s₂)).mp ?_)
  set g₃ : GL (Fin 3) R := g₂ * tGL 0 1 (by decide) s₁ * tGL 0 2 (by decide) s₂ with hg₃
  have h₃c0 : ∀ i, (g₃ : Matrix (Fin 3) (Fin 3) R) i 0 = (g₂ : Matrix (Fin 3) (Fin 3) R) i 0 := by
    intro i; simp [hg₃, mul_transvection_apply_of_ne]
  have h₃00 : (g₃ : Matrix (Fin 3) (Fin 3) R) 0 0 = u := by rw [h₃c0, h₂00]
  have h₃10 : (g₃ : Matrix (Fin 3) (Fin 3) R) 1 0 = 0 := by rw [h₃c0, h₂10]
  have h₃20 : (g₃ : Matrix (Fin 3) (Fin 3) R) 2 0 = 0 := by rw [h₃c0, h₂20]
  have h₃01 : (g₃ : Matrix (Fin 3) (Fin 3) R) 0 1 = 0 := by
    simp only [hg₃, Units.val_mul, coe_tGL, ne_eq, Fin.reduceEq, not_false_eq_true, mul_transvection_apply_of_ne,
      mul_transvection_apply_same, hs₁, h₂00]
    linear_combination (-(g₂ : Matrix (Fin 3) (Fin 3) R) 0 1) * u.inv_mul
  have h₃02 : (g₃ : Matrix (Fin 3) (Fin 3) R) 0 2 = 0 := by
    simp only [hg₃, Units.val_mul, coe_tGL, ne_eq, Fin.reduceEq, not_false_eq_true, mul_transvection_apply_of_ne,
      mul_transvection_apply_same, hs₂, h₂00]
    linear_combination (-(g₂ : Matrix (Fin 3) (Fin 3) R) 0 2) * u.inv_mul
  clear_value g₃

  obtain ⟨f, fii, fij, fsum, fu⟩ := hP ![((g₃⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 1 1,
      ((g₃⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 1 2, 0]
    ![(g₃ : Matrix (Fin 3) (Fin 3) R) 1 1, (g₃ : Matrix (Fin 3) (Fin 3) R) 2 1,
      (g₃ : Matrix (Fin 3) (Fin 3) R) 2 1] (by
      have := congrFun (congrFun (g₃.inv_mul) 1) 1
      rw [Matrix.mul_apply, Matrix.one_apply_eq, Fin.sum_univ_three, h₃01, mul_zero, zero_add] at this
      simpa [dotProduct, Fin.sum_univ_three] using this)
  refine (Subgroup.mul_mem_cancel_left (h := hW (pivot₂ f) (pivot₂_mul_self fii fij fsum))).mp ?_
  set g₄ : GL (Fin 3) R := glOf (pivot₂ f) (pivot₂ f) (pivot₂_mul_self fii fij fsum) * g₃ with hg₄
  have h₄11 : IsUnit ((g₄ : Matrix (Fin 3) (Fin 3) R) 1 1) := by
    rw [hg₄, Units.val_mul, coe_glOf, pivot₂_mul_apply₁]
    convert fu using 1
    simp; ring
  have h₄00 : (g₄ : Matrix (Fin 3) (Fin 3) R) 0 0 = u := by rw [hg₄, Units.val_mul, coe_glOf, pivot₂_mul_apply₀, h₃00]
  have h₄01 : (g₄ : Matrix (Fin 3) (Fin 3) R) 0 1 = 0 := by rw [hg₄, Units.val_mul, coe_glOf, pivot₂_mul_apply₀, h₃01]
  have h₄02 : (g₄ : Matrix (Fin 3) (Fin 3) R) 0 2 = 0 := by rw [hg₄, Units.val_mul, coe_glOf, pivot₂_mul_apply₀, h₃02]
  have h₄10 : (g₄ : Matrix (Fin 3) (Fin 3) R) 1 0 = 0 := by
    rw [hg₄, Units.val_mul, coe_glOf, pivot₂_mul_apply₁, h₃10, h₃20]; ring
  have h₄20 : (g₄ : Matrix (Fin 3) (Fin 3) R) 2 0 = 0 := by
    rw [hg₄, Units.val_mul, coe_glOf, pivot₂_mul_apply₂, h₃10, h₃20]; ring
  clear_value g₄
  obtain ⟨v, hv⟩ := h₄11

  set t₃ : R := -((g₄ : Matrix (Fin 3) (Fin 3) R) 2 1 * ((v⁻¹ : Rˣ) : R)) with ht₃
  refine (Subgroup.mul_mem_cancel_left (h := hT 2 1 (by decide) t₃)).mp ?_
  set g₅ : GL (Fin 3) R := tGL 2 1 (by decide) t₃ * g₄ with hg₅
  have h₅r0 : ∀ b, (g₅ : Matrix (Fin 3) (Fin 3) R) 0 b = (g₄ : Matrix (Fin 3) (Fin 3) R) 0 b := by
    intro b; simp [hg₅, transvection_mul_apply_of_ne]
  have h₅r1 : ∀ b, (g₅ : Matrix (Fin 3) (Fin 3) R) 1 b = (g₄ : Matrix (Fin 3) (Fin 3) R) 1 b := by
    intro b; simp [hg₅, transvection_mul_apply_of_ne]
  have h₅20 : (g₅ : Matrix (Fin 3) (Fin 3) R) 2 0 = 0 := by
    simp only [hg₅, Units.val_mul, coe_tGL, transvection_mul_apply_same, h₄20, h₄10, mul_zero, add_zero]
  have h₅21 : (g₅ : Matrix (Fin 3) (Fin 3) R) 2 1 = 0 := by
    simp only [hg₅, Units.val_mul, coe_tGL, transvection_mul_apply_same, ht₃, ← hv]
    linear_combination (-(g₄ : Matrix (Fin 3) (Fin 3) R) 2 1) * v.inv_mul
  clear_value g₅
  set s₃ : R := -(((v⁻¹ : Rˣ) : R) * (g₅ : Matrix (Fin 3) (Fin 3) R) 1 2) with hs₃
  refine (Subgroup.mul_mem_cancel_right (h := hT 1 2 (by decide) s₃)).mp ?_
  set g₆ : GL (Fin 3) R := g₅ * tGL 1 2 (by decide) s₃ with hg₆
  have h₆c0 : ∀ a, (g₆ : Matrix (Fin 3) (Fin 3) R) a 0 = (g₅ : Matrix (Fin 3) (Fin 3) R) a 0 := by
    intro a; simp [hg₆, mul_transvection_apply_of_ne]
  have h₆c1 : ∀ a, (g₆ : Matrix (Fin 3) (Fin 3) R) a 1 = (g₅ : Matrix (Fin 3) (Fin 3) R) a 1 := by
    intro a; simp [hg₆, mul_transvection_apply_of_ne]
  have h₆02 : (g₆ : Matrix (Fin 3) (Fin 3) R) 0 2 = 0 := by
    simp only [hg₆, Units.val_mul, coe_tGL, mul_transvection_apply_same, h₅r0, h₄02, h₄01, mul_zero, add_zero]
  have h₆12 : (g₆ : Matrix (Fin 3) (Fin 3) R) 1 2 = 0 := by
    simp only [hg₆, Units.val_mul, coe_tGL, mul_transvection_apply_same, hs₃, h₅r1, ← hv]
    linear_combination (-(g₄ : Matrix (Fin 3) (Fin 3) R) 1 2) * v.inv_mul

  exact (MonoidHom.mem_ker).mpr (apply_of_offDiag_eq_zero hM3 ρ hscalar g₆ (by rw [h₆c1, h₅r0, h₄01]) h₆02
    (by rw [h₆c0, h₅r1, h₄10]) h₆12 (by rw [h₆c0, h₅20]) (by rw [h₆c1, h₅21]))

end Generation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Adele

variable (K : Type*) [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K

private theorem snd_mul_apply (x y : 𝔸) (v : HeightOneSpectrum (𝓞 K)) : (x * y).2 v = x.2 v * y.2 v := rfl

private theorem snd_add_apply (x y : 𝔸) (v : HeightOneSpectrum (𝓞 K)) : (x + y).2 v = x.2 v + y.2 v := rfl

private theorem snd_one_apply (v : HeightOneSpectrum (𝓞 K)) : (1 : 𝔸).2 v = 1 := rfl

private theorem snd_zero_apply (v : HeightOneSpectrum (𝓞 K)) : (0 : 𝔸).2 v = 0 := rfl

private theorem tab_mul_self {A : Type*} [MulZeroOneClass A] (k i : Fin 3) :
    (if k = i then (1 : A) else 0) * (if k = i then 1 else 0) = if k = i then 1 else 0 := by
  split <;> simp

private theorem tab_mul_of_ne {A : Type*} [MulZeroOneClass A] (k i j : Fin 3) (hij : i ≠ j) :
    (if k = i then (1 : A) else 0) * (if k = j then 1 else 0) = 0 := by
  by_cases h : k = i
  · subst h; simp [hij]
  · simp [h]

private theorem tab_sum {A : Type*} [AddMonoidWithOne A] (k : Fin 3) :
    (if k = 0 then (1 : A) else 0) + (if k = 1 then 1 else 0) + (if k = 2 then 1 else 0) = 1 := by
  fin_cases k <;> simp

private theorem tab_select {A : Type*} [NonAssocSemiring A] (k : Fin 3) (x : Fin 3 → A) :
    (if k = 0 then (1 : A) else 0) * x 0 + (if k = 1 then 1 else 0) * x 1 + (if k = 2 then 1 else 0) * x 2 = x k := by
  fin_cases k <;> simp

private theorem tab_zero {A : Type*} [NonAssocSemiring A] (y x : Fin 3 → A) (h : ∀ j, x j = 0) :
    y 0 * x 0 + y 1 * x 1 + y 2 * x 2 = 0 := by
  simp [h]

private theorem adele_ext {x y : 𝔸} (h₁ : ∀ w, x.1 w = y.1 w) (h₂ : ∀ v, x.2 v = y.2 v) : x = y :=
  Prod.ext (funext h₁) (FiniteAdeleRing.ext K h₂)

private theorem hasIdempotentPivots_adeleRing : HasIdempotentPivots 𝔸 := by
  intro b c hbc

  have hmax₁ : ∀ w : InfinitePlace K, ∃ i : Fin 3, ∀ j, ‖(c j).1 w‖ ≤ ‖(c i).1 w‖ := fun w => by
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_max_image Finset.univ (fun j : Fin 3 => ‖(c j).1 w‖) Finset.univ_nonempty
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  have hmax₂ : ∀ v : HeightOneSpectrum (𝓞 K), ∃ i : Fin 3, ∀ j, Valued.v ((c j).2 v) ≤ Valued.v ((c i).2 v) :=
    fun v => by
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_max_image Finset.univ (fun j : Fin 3 => Valued.v ((c j).2 v)) Finset.univ_nonempty
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  choose ι₁ hι₁ using hmax₁
  choose ι₂ hι₂ using hmax₂
  let e : Fin 3 → 𝔸 := fun i =>
    (fun w => if ι₁ w = i then 1 else 0, ⟨fun v => if ι₂ v = i then 1 else 0, Filter.Eventually.of_forall fun v => by
      by_cases h : ι₂ v = i
      · simp only [h, if_true, SetLike.mem_coe]; exact one_mem _
      · simp only [h, if_false, SetLike.mem_coe]; exact zero_mem _⟩)
  have he₁ : ∀ i w, (e i).1 w = if ι₁ w = i then 1 else 0 := fun i w => rfl
  have he₂ : ∀ i v, (e i).2 v = if ι₂ v = i then 1 else 0 := fun i v => rfl

  have hbc' : b 0 * c 0 + b 1 * c 1 + b 2 * c 2 = 1 := by simpa [dotProduct, Fin.sum_univ_three] using hbc
  have hbc₁ : ∀ w, (b 0 * c 0 + b 1 * c 1 + b 2 * c 2).1 w = (1 : 𝔸).1 w := fun w => by rw [hbc']
  have hbc₂ : ∀ v, (b 0).2 v * (c 0).2 v + (b 1).2 v * (c 1).2 v + (b 2).2 v * (c 2).2 v = 1 := fun v => by
    have := congrArg (fun x : 𝔸 => x.2 v) hbc'
    simpa only [snd_add_apply, snd_mul_apply, snd_one_apply] using this
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro i
    exact adele_ext K (fun w => tab_mul_self (ι₁ w) i) (fun v => by rw [snd_mul_apply, he₂, tab_mul_self])
  · intro i j hij
    exact adele_ext K (fun w => tab_mul_of_ne (ι₁ w) i j hij)
      (fun v => by rw [snd_mul_apply, he₂, he₂, tab_mul_of_ne _ _ _ hij, snd_zero_apply])
  · exact adele_ext K (fun w => tab_sum (ι₁ w))
      (fun v => by rw [snd_add_apply, snd_add_apply, he₂, he₂, he₂, tab_sum, snd_one_apply])
  ·
    have hu₁ : ∀ w, (e 0 * c 0 + e 1 * c 1 + e 2 * c 2).1 w = (c (ι₁ w)).1 w := fun w =>
      tab_select (ι₁ w) fun j => (c j).1 w
    have hu₂ : ∀ v, (e 0 * c 0 + e 1 * c 1 + e 2 * c 2).2 v = (c (ι₂ v)).2 v := fun v => by
      rw [snd_add_apply, snd_add_apply, snd_mul_apply, snd_mul_apply, snd_mul_apply, he₂, he₂, he₂]
      exact tab_select (ι₂ v) fun j => (c j).2 v

    have hne₁ : ∀ w, (e 0 * c 0 + e 1 * c 1 + e 2 * c 2).1 w ≠ 0 := fun w h0 => by
      have hall : ∀ j, (c j).1 w = 0 := fun j => by
        have := hι₁ w j
        rw [← hu₁ w, h0, norm_zero] at this
        exact norm_le_zero_iff.mp this
      have hzero : (b 0 * c 0 + b 1 * c 1 + b 2 * c 2).1 w = 0 :=
        tab_zero (fun j => (b j).1 w) (fun j => (c j).1 w) hall
      exact (isUnit_one (M := w.Completion)).ne_zero ((hbc₁ w).symm.trans hzero)

    have hne₂ : ∀ v, (e 0 * c 0 + e 1 * c 1 + e 2 * c 2).2 v ≠ 0 := fun v h0 => by
      rw [hu₂] at h0
      have hall : ∀ j, (c j).2 v = 0 := fun j => by
        have := hι₂ v j
        rw [h0, Valuation.map_zero, le_zero_iff] at this
        exact (Valuation.zero_iff _).mp this
      have := hbc₂ v
      rw [hall 0, hall 1, hall 2, mul_zero, mul_zero, mul_zero, add_zero, add_zero] at this
      exact zero_ne_one this

    have hint : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        ∀ j, (b j).2 v ∈ v.adicCompletionIntegers K ∧ (c j).2 v ∈ v.adicCompletionIntegers K := by
      simp only [Filter.eventually_all, Filter.eventually_and]
      exact fun j => ⟨(b j).2.2, (c j).2.2⟩
    refine Prod.isUnit_iff.mpr ⟨Pi.isUnit_iff.mpr fun w => (hne₁ w).isUnit, ?_⟩
    refine RestrictedProduct.isUnit_of_eventually_isUnit (fun v => (hne₂ v).isUnit) ?_
    filter_upwards [hint] with v hv

    have hle : Valued.v ((e 0 * c 0 + e 1 * c 1 + e 2 * c 2).2 v) ≤ 1 := by
      rw [hu₂]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (hv _).2
    have hbj : ∀ j, Valued.v ((b j).2 v * (c j).2 v) ≤ Valued.v ((c (ι₂ v)).2 v) := fun j => by
      rw [Valuation.map_mul]
      calc Valued.v ((b j).2 v) * Valued.v ((c j).2 v) ≤ 1 * Valued.v ((c (ι₂ v)).2 v) :=
            mul_le_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (hv j).1) (hι₂ v j)
        _ = _ := one_mul _
    have hge : 1 ≤ Valued.v ((e 0 * c 0 + e 1 * c 1 + e 2 * c 2).2 v) := by
      rw [hu₂, ← (Valued.v : Valuation (v.adicCompletion K) _).map_one, ← hbc₂ v]
      exact Valuation.map_add_le _ (Valuation.map_add_le _ (hbj 0) (hbj 1)) (hbj 2)
    have hone : Valued.v ((e 0 * c 0 + e 1 * c 1 + e 2 * c 2).2 v) = 1 := le_antisymm hle hge
    refine ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mpr hle,
      isUnit_iff_exists_inv.mpr ⟨⟨((e 0 * c 0 + e 1 * c 1 + e 2 * c 2).2 v)⁻¹, ?_⟩, ?_⟩⟩
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mpr ?_
      rw [map_inv₀, hone, inv_one]
    · exact Subtype.ext (mul_inv_cancel₀ (hne₂ v))

private theorem isUnit_two_adeleRing : IsUnit (2 : 𝔸) := by
  have h : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr two_ne_zero
  have := h.map (algebraMap K 𝔸)
  rwa [map_ofNat] at this

end Adele
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

section Torsion

private theorem units_pow_eq_one {n : ℕ} (hn : n ≠ 0) (x : ℝ≥0ˣ) (hx : x ^ n = 1) : x = 1 := by
  have h1 : ((x : ℝ≥0) : ℝ) ^ n = 1 := by
    have := congrArg (fun u : ℝ≥0ˣ => ((u : ℝ≥0) : ℝ)) hx
    simpa using this
  have h2 : ((x : ℝ≥0) : ℝ) = 1 := by
    rcases (pow_eq_one_iff_of_ne_zero hn).mp h1 with h | ⟨h, -⟩
    · exact h
    · have : (0 : ℝ) ≤ ((x : ℝ≥0) : ℝ) := (x : ℝ≥0).coe_nonneg
      linarith
  exact Units.ext (NNReal.coe_injective (by simpa using h2))

end Torsion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowAction

private scoped instance : ContinuousConstSMul (Matrix (Fin 3) (Fin 3) 𝔸) (Fin 3 → 𝔸) :=
  ⟨fun A => continuous_pi fun i => by
    simp only [Matrix.smul_eq_mulVec, Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)⟩

private theorem secondCountableTopology_adelicGL3 : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem domSMul_rowHaar (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    DomMulAct.mk h • (rowHaar : Measure (Fin 3 → 𝔸)) = distribHaarChar (Fin 3 → 𝔸) h • rowHaar := by
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk h • (rowHaar : Measure (Fin 3 → 𝔸))) rowHaar]
  rw [addHaarScalarFactor_smul_eq_distribHaarChar]

private theorem domSMul_adelicAddHaar (a : 𝔸ˣ) :
    DomMulAct.mk a • (adelicAddHaar (𝓞 ℚ) ℚ : Measure 𝔸) = distribHaarChar 𝔸 a • adelicAddHaar (𝓞 ℚ) ℚ := by
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk a • (adelicAddHaar (𝓞 ℚ) ℚ : Measure 𝔸))
    (adelicAddHaar (𝓞 ℚ) ℚ)]
  rw [addHaarScalarFactor_smul_eq_distribHaarChar]

private theorem addHaarScalarFactor_congr {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] {μ₁ μ₂ μ : Measure A} [μ.IsAddHaarMeasure] [IsFiniteMeasureOnCompacts μ₁]
    [μ₁.IsAddLeftInvariant] [IsFiniteMeasureOnCompacts μ₂] [μ₂.IsAddLeftInvariant] (h : μ₁ = μ₂) :
    μ₁.addHaarScalarFactor μ = μ₂.addHaarScalarFactor μ := by
  subst h
  rfl

private theorem haarScalarFactor_congr {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ₁ μ₂ μ : Measure G} [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts μ₁]
    [μ₁.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ₂] [μ₂.IsMulLeftInvariant] (h : μ₁ = μ₂) :
    μ₁.haarScalarFactor μ = μ₂.haarScalarFactor μ := by
  subst h
  rfl

private theorem distribHaarChar_rows_scalar (a : 𝔸ˣ) :
    distribHaarChar (Fin 3 → 𝔸) (dGL fun _ : Fin 3 => a) = distribHaarChar 𝔸 a ^ 3 := by

  have hset : ∀ s : Fin 3 → Set 𝔸,
      ((dGL fun _ : Fin 3 => a) • Set.univ.pi s : Set (Fin 3 → 𝔸)) = Set.univ.pi fun i => a • s i := by
    intro s
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_univ_pi]
    refine forall_congr' fun i => ?_
    rw [Units.smul_def, coe_dGL_inv, Matrix.smul_eq_mulVec, Matrix.mulVec_diagonal, Units.smul_def, smul_eq_mul]

  have h1 : Measure.pi (fun _ : Fin 3 => distribHaarChar 𝔸 a • adelicAddHaar (𝓞 ℚ) ℚ) =
      DomMulAct.mk (dGL fun _ : Fin 3 => a) • (rowHaar : Measure (Fin 3 → 𝔸)) := by
    refine Measure.pi_eq fun s _ => ?_
    rw [Measure.domSMul_apply, Equiv.symm_apply_apply, hset,
      show (rowHaar : Measure (Fin 3 → 𝔸)) = Measure.pi fun _ : Fin 3 => adelicAddHaar (𝓞 ℚ) ℚ from rfl,
      Measure.pi_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← domSMul_adelicAddHaar a, Measure.domSMul_apply, Equiv.symm_apply_apply]
  have h2 : Measure.pi (fun _ : Fin 3 => distribHaarChar 𝔸 a • adelicAddHaar (𝓞 ℚ) ℚ) =
      (distribHaarChar 𝔸 a ^ 3) • (rowHaar : Measure (Fin 3 → 𝔸)) := by
    refine Measure.pi_eq fun s _ => ?_
    rw [Measure.coe_nnreal_smul_apply,
      show (rowHaar : Measure (Fin 3 → 𝔸)) = Measure.pi fun _ : Fin 3 => adelicAddHaar (𝓞 ℚ) ℚ from rfl,
      Measure.pi_pi]
    simp only [Measure.coe_nnreal_smul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.coe_pow]
  rw [← addHaarScalarFactor_smul_eq_distribHaarChar rowHaar, addHaarScalarFactor_congr (h1.symm.trans h2),
    Measure.addHaarScalarFactor_smul, Measure.addHaarScalarFactor_self, smul_eq_mul, mul_one]

private def transposeGL (g : AdelicGL 3 (𝓞 ℚ) ℚ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  ⟨(g : Matrix (Fin 3) (Fin 3) 𝔸)ᵀ, ((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸)ᵀ,
    by rw [← Matrix.transpose_mul, g.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, g.mul_inv, Matrix.transpose_one]⟩

private theorem det_transposeGL (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Matrix.GeneralLinearGroup.det (transposeGL g) = Matrix.GeneralLinearGroup.det g :=
  Units.ext (Matrix.det_transpose _)

private theorem distribHaarChar_rows (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    distribHaarChar (Fin 3 → 𝔸) g = distribHaarChar 𝔸 (Matrix.GeneralLinearGroup.det g) := by
  let χ : AdelicGL 3 (𝓞 ℚ) ℚ →* ℝ≥0 := distribHaarChar (Fin 3 → 𝔸)
  let ψ : AdelicGL 3 (𝓞 ℚ) ℚ →* ℝ≥0 := (distribHaarChar 𝔸).comp Matrix.GeneralLinearGroup.det
  let ρ : AdelicGL 3 (𝓞 ℚ) ℚ →* ℝ≥0ˣ := χ.toHomUnits / ψ.toHomUnits
  have hρ : ∀ h, ρ h = 1 ↔ χ h = ψ h := fun h => by
    simp only [ρ, MonoidHom.div_apply, div_eq_one, Units.ext_iff, MonoidHom.coe_toHomUnits]
  suffices ρ g = 1 from (hρ g).mp this
  refine eq_one_of_apply_scalar (hasIdempotentPivots_adeleRing ℚ) (isUnit_two_adeleRing ℚ)
    (units_pow_eq_one two_ne_zero) (units_pow_eq_one three_ne_zero) ρ (fun a => (hρ _).mpr ?_) g
  have hdet : Matrix.GeneralLinearGroup.det (dGL fun _ : Fin 3 => a) = a ^ 3 := by
    refine Units.ext ?_
    simp [Matrix.GeneralLinearGroup.val_det_apply, det_diagonal, Finset.prod_const]
  simp only [χ, ψ, MonoidHom.comp_apply, hdet, map_pow]
  exact distribHaarChar_rows_scalar a

end RowAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem scalar_comm (a : 𝔸ˣ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    x * dGL (fun _ : Fin 3 => a) = dGL (fun _ : Fin 3 => a) * x := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_dGL, ← Matrix.scalar_apply]
  exact (Matrix.scalar_commute (a : 𝔸) (fun r' => Commute.all _ _) _).eq.symm

private theorem map_vecMul_rowHaar (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Measure.map (fun x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ => x ᵥ* (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) rowHaar =
      (ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)))⁻¹ • rowHaar := by
  have hfun : (fun x : Fin 3 → 𝔸 => x ᵥ* (g : Matrix (Fin 3) (Fin 3) 𝔸)) = fun x => transposeGL g • x := by
    funext x
    rw [Units.smul_def, Matrix.smul_eq_mulVec]
    exact (Matrix.mulVec_transpose _ _).symm
  have hmap : Measure.map (fun x : Fin 3 → 𝔸 => transposeGL g • x) rowHaar =
      DomMulAct.mk (transposeGL g)⁻¹ • (rowHaar : Measure (Fin 3 → 𝔸)) := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply (measurable_const_smul _) hs, Set.preimage_smul, Measure.domSMul_apply,
      Equiv.symm_apply_apply]
  have hinv : distribHaarChar (Fin 3 → 𝔸) (transposeGL g)⁻¹ = (distribHaarChar (Fin 3 → 𝔸) (transposeGL g))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])
  have hne : distribHaarChar 𝔸 (Matrix.GeneralLinearGroup.det g) ≠ 0 := (distribHaarChar_pos).ne'
  rw [hfun, hmap, domSMul_rowHaar, hinv, distribHaarChar_rows, det_transposeGL, NumberField.TateGlobal.ideleNorm,
    ENNReal.ofReal_coe_nnreal]
  refine Measure.ext fun s _ => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul, ENNReal.coe_inv hne]

private theorem lintegral_vecMul_rowHaar (g : AdelicGL 3 (𝓞 ℚ) ℚ) (φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞)
    (hφ : Measurable φ) :
    ∫⁻ x, φ (x ᵥ* (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) ∂rowHaar =
      (ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)))⁻¹ *
        ∫⁻ x, φ x ∂rowHaar := by
  have hmeas : Measurable fun x : Fin 3 → 𝔸 => x ᵥ* (g : Matrix (Fin 3) (Fin 3) 𝔸) := by
    have : (fun x : Fin 3 → 𝔸 => x ᵥ* (g : Matrix (Fin 3) (Fin 3) 𝔸)) = fun x => transposeGL g • x := by
      funext x
      rw [Units.smul_def, Matrix.smul_eq_mulVec]
      exact (Matrix.mulVec_transpose _ _).symm
    rw [this]
    exact measurable_const_smul _
  rw [← lintegral_map hφ hmeas, map_vecMul_rowHaar, lintegral_smul_measure, smul_eq_mul]

private theorem isMulRightInvariant_adelicGLHaar :
    (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).IsMulRightInvariant := by
  haveI := secondCountableTopology_adelicGL3
  set μ : Measure (AdelicGL 3 (𝓞 ℚ) ℚ) := adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ with hμ

  have hΔ : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Measure.modularCharacter g = 1 := by
    intro g
    let ρ : AdelicGL 3 (𝓞 ℚ) ℚ →* ℝ≥0ˣ := (Measure.modularCharacter).toHomUnits
    suffices ρ g = 1 by
      have := congrArg (fun u : ℝ≥0ˣ => (u : ℝ≥0)) this
      simpa [ρ, MonoidHom.coe_toHomUnits] using this
    refine eq_one_of_apply_scalar (hasIdempotentPivots_adeleRing ℚ) (isUnit_two_adeleRing ℚ)
      (units_pow_eq_one two_ne_zero) (units_pow_eq_one three_ne_zero) ρ (fun a => Units.ext ?_) g
    show Measure.modularCharacterFun (dGL fun _ : Fin 3 => a) = ((1 : ℝ≥0ˣ) : ℝ≥0)
    rw [Units.val_one, Measure.modularCharacterFun_eq_haarScalarFactor μ]
    have hz : Measure.map (fun x => x * dGL fun _ : Fin 3 => a) μ = μ := by
      rw [show (fun x => x * dGL fun _ : Fin 3 => a) = fun x => dGL (fun _ : Fin 3 => a) * x from
        funext (scalar_comm a)]
      exact map_mul_left_eq_self μ _
    rw [haarScalarFactor_congr hz, Measure.haarScalarFactor_self]
  refine ⟨fun g => ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ,
    ← Measure.modularCharacterFun_eq_haarScalarFactor μ g]
  change Measure.modularCharacter g • μ = μ
  rw [hΔ g]
  exact one_smul ℝ≥0 μ

end JacobianUnimodular
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end JacobianAndModulus
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section SectionAndRowSets

section SectionHeads

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

open scoped RestrictedProduct

open Topology

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

end SectionHeads
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end SectionAndRowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section DeviceFiniteness

section GenericDevice

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] {Y : Type} [MeasurableSpace Y]

private theorem measurable_fibMap (P : Subgroup G) {sec : Y → G} (hsec : Measurable sec) :
    Measurable fun z : Y × ↥P => (z.2 : G) * sec z.1 :=
  (measurable_subtype_coe.comp measurable_snd).mul (hsec.comp measurable_fst)

private theorem measurable_fibreIntegral (P : Subgroup G) {sec : Y → G} (hsec : Measurable sec) (μP : Measure ↥P)
    [SFinite μP] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x : Y => ∫⁻ p : ↥P, f ((p : G) * sec x) ∂μP := by
  have hfφ : Measurable fun z : Y × ↥P => f ((z.2 : G) * sec z.1) := hf.comp (measurable_fibMap P hsec)
  exact hfφ.lintegral_prod_right'

private theorem lintegral_fibMeasure (P : Subgroup G) {sec : Y → G} (hsec : Measurable sec) {δ : G → ℝ≥0∞}
    (hδ : Measurable δ) (μP : Measure ↥P) [SFinite μP] (lam : Measure Y) (R : Set Y) {f : G → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ g, f g ∂fibMeasure P sec δ μP lam R =
      ∫⁻ x in R, (δ (sec x))⁻¹ * ∫⁻ p : ↥P, f ((p : G) * sec x) ∂μP ∂lam := by
  have hfφ : Measurable fun z : Y × ↥P => f ((z.2 : G) * sec z.1) := hf.comp (measurable_fibMap P hsec)
  have hw : Measurable fun x : Y => (δ (sec x))⁻¹ := (hδ.comp hsec).inv
  rw [fibMeasure, lintegral_map hf (measurable_fibMap P hsec), lintegral_prod _ hfφ.aemeasurable]
  dsimp only
  rw [lintegral_withDensity_eq_lintegral_mul _ hw (measurable_fibreIntegral P hsec μP hf)]
  simp only [Pi.mul_apply]

private theorem lintegral_mul_right_fibMeasure (P : Subgroup G) (π : G → Y) (act : Y → G → Y) {sec : Y → G}
    (hsec : Measurable sec) {δ : G → ℝ≥0∞} (hδ : Measurable δ) (μP : Measure ↥P) [SFinite μP] (lam : Measure Y)
    {R : Set Y} (hR : MeasurableSet R)
    (hπmul : ∀ g h : G, π (g * h) = act (π g) h)
    (hπP : ∀ a b : G, π a = π b → a * b⁻¹ ∈ P)
    (hπsec : ∀ x ∈ R, π (sec x) = x)
    (hRact : ∀ (x : Y) (h : G), act x h ∈ R ↔ x ∈ R)
    (hδmul : ∀ g h : G, δ (g * h) = δ g * δ h) (hδinv : ∀ g : G, δ g⁻¹ = (δ g)⁻¹)
    (hδ0 : ∀ g : G, δ g ≠ 0) (hδtop : ∀ g : G, δ g ≠ ⊤)
    (hμP : ∀ (p₁ : ↥P) (F : ↥P → ℝ≥0∞), Measurable F →
      ∫⁻ p, F (p * p₁) ∂μP = δ (p₁ : G) * ∫⁻ p, F p ∂μP)
    (hlam : ∀ (h : G) (Ψ : Y → ℝ≥0∞), Measurable Ψ → ∫⁻ x, Ψ (act x h) ∂lam = (δ h)⁻¹ * ∫⁻ x, Ψ x ∂lam)
    (h : G) {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f (g * h) ∂fibMeasure P sec δ μP lam R = ∫⁻ g, f g ∂fibMeasure P sec δ μP lam R := by
  have hfh : Measurable fun g => f (g * h) := hf.comp (measurable_mul_const h)
  rw [lintegral_fibMeasure P hsec hδ μP lam R hfh, lintegral_fibMeasure P hsec hδ μP lam R hf]

  set Ψ : Y → ℝ≥0∞ := fun x => (δ (sec x))⁻¹ * ∫⁻ p : ↥P, f ((p : G) * sec x) ∂μP with hΨ
  have hΨm : Measurable Ψ := (hδ.comp hsec).inv.mul (measurable_fibreIntegral P hsec μP hf)

  have hpt : ∀ x ∈ R, (δ (sec x))⁻¹ * ∫⁻ p : ↥P, f ((p : G) * sec x * h) ∂μP = δ h * Ψ (act x h) := by
    intro x hx
    have hx' : act x h ∈ R := (hRact x h).2 hx
    have hmem : sec x * h * (sec (act x h))⁻¹ ∈ P := by
      refine hπP _ _ ?_
      rw [hπmul, hπsec x hx, hπsec _ hx']
    set p₁ : ↥P := ⟨sec x * h * (sec (act x h))⁻¹, hmem⟩ with hp₁
    have hfactor : ∀ p : ↥P, (p : G) * sec x * h = ((p * p₁ : ↥P) : G) * sec (act x h) := by
      intro p
      simp only [hp₁, Subgroup.coe_mul, mul_assoc, inv_mul_cancel, mul_one]
    have hδp₁ : δ (p₁ : G) = δ (sec x) * δ h * (δ (sec (act x h)))⁻¹ := by
      simp only [hp₁, hδmul, hδinv]
    simp_rw [hfactor]
    rw [hμP p₁ (fun p => f ((p : G) * sec (act x h))) (hf.comp (measurable_subtype_coe.mul_const _)), hδp₁]
    simp only [hΨ]

    set I : ℝ≥0∞ := ∫⁻ p : ↥P, f ((p : G) * sec (act x h)) ∂μP
    calc (δ (sec x))⁻¹ * (δ (sec x) * δ h * (δ (sec (act x h)))⁻¹ * I)
        = ((δ (sec x))⁻¹ * δ (sec x)) * (δ h * ((δ (sec (act x h)))⁻¹ * I)) := by simp only [mul_assoc]
      _ = δ h * ((δ (sec (act x h)))⁻¹ * I) := by rw [ENNReal.inv_mul_cancel (hδ0 _) (hδtop _), one_mul]

  have hind : ∀ x : Y, R.indicator (fun x => Ψ (act x h)) x = R.indicator Ψ (act x h) := by
    intro x
    by_cases hx : x ∈ R
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hRact x h).2 hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx ((hRact x h).1 h'))]
  calc ∫⁻ x in R, (δ (sec x))⁻¹ * ∫⁻ p : ↥P, f ((p : G) * sec x * h) ∂μP ∂lam
      = ∫⁻ x in R, δ h * Ψ (act x h) ∂lam := setLIntegral_congr_fun hR hpt
    _ = δ h * ∫⁻ x in R, Ψ (act x h) ∂lam := lintegral_const_mul' _ _ (hδtop h)
    _ = δ h * ∫⁻ x, R.indicator Ψ (act x h) ∂lam := by
        rw [← lintegral_indicator hR]
        simp_rw [hind]
    _ = δ h * ((δ h)⁻¹ * ∫⁻ x, R.indicator Ψ x ∂lam) := by rw [hlam h _ (hΨm.indicator hR)]
    _ = ∫⁻ x, R.indicator Ψ x ∂lam := by rw [← mul_assoc, ENNReal.mul_inv_cancel (hδ0 h) (hδtop h), one_mul]
    _ = ∫⁻ x in R, Ψ x ∂lam := lintegral_indicator hR _

private theorem isMulRightInvariant_fibMeasure (P : Subgroup G) (π : G → Y) (act : Y → G → Y) {sec : Y → G}
    (hsec : Measurable sec) {δ : G → ℝ≥0∞} (hδ : Measurable δ) (μP : Measure ↥P) [SFinite μP] (lam : Measure Y)
    {R : Set Y} (hR : MeasurableSet R)
    (hπmul : ∀ g h : G, π (g * h) = act (π g) h)
    (hπP : ∀ a b : G, π a = π b → a * b⁻¹ ∈ P)
    (hπsec : ∀ x ∈ R, π (sec x) = x)
    (hRact : ∀ (x : Y) (h : G), act x h ∈ R ↔ x ∈ R)
    (hδmul : ∀ g h : G, δ (g * h) = δ g * δ h) (hδinv : ∀ g : G, δ g⁻¹ = (δ g)⁻¹)
    (hδ0 : ∀ g : G, δ g ≠ 0) (hδtop : ∀ g : G, δ g ≠ ⊤)
    (hμP : ∀ (p₁ : ↥P) (F : ↥P → ℝ≥0∞), Measurable F →
      ∫⁻ p, F (p * p₁) ∂μP = δ (p₁ : G) * ∫⁻ p, F p ∂μP)
    (hlam : ∀ (h : G) (Ψ : Y → ℝ≥0∞), Measurable Ψ → ∫⁻ x, Ψ (act x h) ∂lam = (δ h)⁻¹ * ∫⁻ x, Ψ x ∂lam) :
    (fibMeasure P sec δ μP lam R).IsMulRightInvariant := by
  refine (forall_measure_preimage_mul_right_iff _).1 fun h A hA => ?_
  have key := lintegral_mul_right_fibMeasure P π act hsec hδ μP lam hR hπmul hπP hπsec hRact hδmul hδinv hδ0 hδtop
    hμP hlam h (f := A.indicator fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator hA)
  have hpre : (fun g => A.indicator (fun _ => (1 : ℝ≥0∞)) (g * h)) =
      ((fun g => g * h) ⁻¹' A).indicator fun _ => (1 : ℝ≥0∞) := by
    funext g
    by_cases hg : g * h ∈ A
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (show g ∈ (fun g => g * h) ⁻¹' A from hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (show g ∉ (fun g => g * h) ⁻¹' A from hg)]
  rw [hpre, lintegral_indicator_const (hA.preimage (measurable_mul_const h)), lintegral_indicator_const hA, one_mul,
    one_mul] at key
  exact key

end GenericDevice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Finiteness

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] {Y : Type} [MeasurableSpace Y]

private theorem fibMeasure_apply (P : Subgroup G) {sec : Y → G} (hsec : Measurable sec) {δ : G → ℝ≥0∞}
    (hδ : Measurable δ) (μP : Measure ↥P) [SFinite μP] (lam : Measure Y) (R : Set Y) {K : Set G}
    (hK : MeasurableSet K) :
    fibMeasure P sec δ μP lam R K =
      ∫⁻ x in R, (δ (sec x))⁻¹ * ∫⁻ p : ↥P, K.indicator (fun _ => (1 : ℝ≥0∞)) ((p : G) * sec x) ∂μP ∂lam := by
  rw [← one_mul (fibMeasure P sec δ μP lam R K), ← lintegral_indicator_const hK,
    lintegral_fibMeasure P hsec hδ μP lam R (measurable_const.indicator hK)]

private theorem fibMeasure_ne_top (P : Subgroup G) (π : G → Y) {sec : Y → G} (hsec : Measurable sec)
    {δ : G → ℝ≥0∞} (hδ : Measurable δ) (μP : Measure ↥P) [SFinite μP] (lam : Measure Y) {R : Set Y}
    (hR : MeasurableSet R)
    (hπleft : ∀ (p : ↥P) (g : G), π ((p : G) * g) = π g)
    (hπP : ∀ a b : G, π a = π b → a * b⁻¹ ∈ P)
    (hπsec : ∀ x ∈ R, π (sec x) = x)
    (hδmul : ∀ g h : G, δ (g * h) = δ g * δ h) (hδinv : ∀ g : G, δ g⁻¹ = (δ g)⁻¹)
    (hδ0 : ∀ g : G, δ g ≠ 0) (hδtop : ∀ g : G, δ g ≠ ⊤)
    (hμP : ∀ (p₁ : ↥P) (F : ↥P → ℝ≥0∞), Measurable F →
      ∫⁻ p, F (p * p₁) ∂μP = δ (p₁ : G) * ∫⁻ p, F p ∂μP)
    {K : Set G} (hK : MeasurableSet K)
    {T : Set Y} (hTmeas : MeasurableSet T) (hTtop : lam T ≠ ⊤) (hKT : ∀ k ∈ K, π k ∈ T)
    {C : Set ↥P} (hCmeas : MeasurableSet C) (hCtop : μP C ≠ ⊤)
    (hKC : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ q : ↥P, (q : G) = k₁ * k₂⁻¹ → q ∈ C)
    {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmK : ∀ k ∈ K, m ≤ δ k) :
    fibMeasure P sec δ μP lam R K ≠ ⊤ := by
  rw [fibMeasure_apply P hsec hδ μP lam R hK]

  have hrow : ∀ x ∈ R, (δ (sec x))⁻¹ * ∫⁻ p : ↥P, K.indicator (fun _ => (1 : ℝ≥0∞)) ((p : G) * sec x) ∂μP ≤
      T.indicator (fun _ => m⁻¹ * μP C) x := by
    intro x hx
    by_cases hxK : ∃ k ∈ K, π k = x
    · obtain ⟨k₀, hk₀, hπk₀⟩ := hxK
      have hxT : x ∈ T := hπk₀ ▸ hKT k₀ hk₀
      have hmem : sec x * k₀⁻¹ ∈ P := hπP _ _ (by rw [hπsec x hx, hπk₀])
      set p₀ : ↥P := ⟨sec x * k₀⁻¹, hmem⟩ with hp₀

      have hfib : ∀ p : ↥P, K.indicator (fun _ => (1 : ℝ≥0∞)) ((p : G) * sec x) ≤
          C.indicator (fun _ => (1 : ℝ≥0∞)) (p * p₀) := by
        intro p
        by_cases hpK : (p : G) * sec x ∈ K
        · have hpC : p * p₀ ∈ C := by
            refine hKC _ hpK k₀ hk₀ (p * p₀) ?_
            simp only [hp₀, Subgroup.coe_mul, mul_assoc]
          rw [Set.indicator_of_mem hpK, Set.indicator_of_mem hpC]
        · rw [Set.indicator_of_notMem hpK]
          exact zero_le
      have hδp₀ : δ (p₀ : G) = δ (sec x) * (δ k₀)⁻¹ := by
        simp only [hp₀, hδmul, hδinv]
      calc (δ (sec x))⁻¹ * ∫⁻ p : ↥P, K.indicator (fun _ => (1 : ℝ≥0∞)) ((p : G) * sec x) ∂μP
          ≤ (δ (sec x))⁻¹ * ∫⁻ p : ↥P, C.indicator (fun _ => (1 : ℝ≥0∞)) (p * p₀) ∂μP :=
            mul_le_mul' le_rfl (lintegral_mono fun p => hfib p)
        _ = (δ (sec x))⁻¹ * (δ (sec x) * (δ k₀)⁻¹ * μP C) := by
            rw [hμP p₀ _ (measurable_const.indicator hCmeas), lintegral_indicator_const hCmeas, one_mul, hδp₀]
        _ = (δ k₀)⁻¹ * μP C := by
            rw [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel (hδ0 _) (hδtop _), one_mul]
        _ ≤ m⁻¹ * μP C := mul_le_mul' (ENNReal.inv_le_inv' (hmK k₀ hk₀)) le_rfl
        _ = T.indicator (fun _ => m⁻¹ * μP C) x := by rw [Set.indicator_of_mem hxT]
    ·
      have hzero : ∀ p : ↥P, K.indicator (fun _ => (1 : ℝ≥0∞)) ((p : G) * sec x) = 0 := by
        intro p
        refine Set.indicator_of_notMem (fun hpK => hxK ⟨_, hpK, ?_⟩) _
        rw [hπleft, hπsec x hx]
      simp only [hzero, lintegral_zero, mul_zero]
      exact zero_le
  refine ne_top_of_le_ne_top ?_ ((setLIntegral_mono' hR hrow).trans (setLIntegral_le_lintegral _ _))
  rw [lintegral_indicator_const hTmeas]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hm0) hCtop) hTtop

end Finiteness
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end DeviceFiniteness
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section CompactSupports

section CompactInputs

open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

private theorem exists_ne_zero_le_on_of_isCompact {X : Type} [TopologicalSpace X] {f : X → ℝ≥0∞} (hf : Continuous f)
    (hf0 : ∀ x, f x ≠ 0) {K : Set X} (hK : IsCompact K) : ∃ m : ℝ≥0∞, m ≠ 0 ∧ ∀ k ∈ K, m ≤ f k := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_ne_zero, by simp [hKe]⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne hf.continuousOn
    exact ⟨f x₀, hf0 x₀, fun k hk => hmin hk⟩

private theorem continuous_ofReal_ideleNorm_det :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)) :=
  ENNReal.continuous_ofReal.comp
    ((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp Matrix.GeneralLinearGroup.continuous_det)

private theorem isFiniteMeasureOnCompacts_rowHaar :
    IsFiniteMeasureOnCompacts (rowHaar : Measure (Fin 3 → AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstance

private theorem isCompact_mul_inv {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hK : IsCompact K) : IsCompact (K * K⁻¹) :=
  hK.mul hK.inv

private theorem isCompact_preimage_mirabolic {L : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hL : IsCompact L) :
    IsCompact ((fun q : ↥mirabolic => (q : AdelicGL 3 (𝓞 ℚ) ℚ)) ⁻¹' L) :=
  isClosed_mirabolic.isClosedEmbedding_subtypeVal.isCompact_preimage hL

private theorem measurableSet_of_isCompact_mirabolic {C : Set ↥mirabolic} (hC : IsCompact C) : MeasurableSet C :=
  hC.isClosed.measurableSet

private theorem mem_preimage_mul_inv_of_mem {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} {k₁ : AdelicGL 3 (𝓞 ℚ) ℚ} (hk₁ : k₁ ∈ K)
    {k₂ : AdelicGL 3 (𝓞 ℚ) ℚ} (hk₂ : k₂ ∈ K) (q : ↥mirabolic) (hq : (q : AdelicGL 3 (𝓞 ℚ) ℚ) = k₁ * k₂⁻¹) :
    q ∈ (fun q : ↥mirabolic => (q : AdelicGL 3 (𝓞 ℚ) ℚ)) ⁻¹' (K * K⁻¹) := by
  show (q : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ K * K⁻¹
  rw [hq]
  exact Set.mul_mem_mul hk₁ (Set.inv_mem_inv.2 hk₂)

end CompactInputs
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end CompactSupports
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section BlockIntegrand

private theorem continuous_coe_matrix :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  Units.continuous_val

end BlockIntegrand
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UniquenessPrinciple

section UniquenessHead

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open Filter Topology Set

open scoped NNReal Classical

private abbrev archBorel : MeasurableSpace (InfiniteAdeleRing ℚ) := borel _

attribute [local instance] archBorel

private theorem archBorelSpace : BorelSpace (InfiniteAdeleRing ℚ) := ⟨rfl⟩

attribute [local instance] archBorelSpace

private theorem archSecondCountable [∀ w : InfinitePlace ℚ, ProperSpace w.Completion] :
    SecondCountableTopology (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace ℚ) → w.Completion))

private abbrev localBorel (p : HeightOneSpectrum (𝓞 ℚ)) : MeasurableSpace (p.adicCompletion ℚ) := borel _

attribute [local instance] localBorel

private theorem localBorelSpace (p : HeightOneSpectrum (𝓞 ℚ)) : BorelSpace (p.adicCompletion ℚ) := ⟨rfl⟩

attribute [local instance] localBorelSpace

private abbrev Coords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Type :=
  (Fin 3 → InfiniteAdeleRing ℚ) × ∀ k : Fin 3 × {p // p ∈ S}, k.2.1.adicCompletion ℚ

private theorem countable_primes : Countable (HeightOneSpectrum (𝓞 ℚ)) :=
  Countable.of_equiv _ Rat.HeightOneSpectrum.primesEquiv.symm

attribute [local instance] countable_primes

private theorem properCompletion (w : InfinitePlace ℚ) : ProperSpace w.Completion :=
  AdelicBox.properSpace_completion (K := ℚ) w

attribute [local instance] properCompletion archSecondCountable

private theorem secondCountableAdeles : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

attribute [local instance] secondCountableAdeles NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem borelRows : BorelSpace (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) := inferInstance

attribute [local instance] borelRows

private theorem haarRows : rowHaar.IsAddHaarMeasure := inferInstance

attribute [local instance] haarRows

private theorem localSecondCountable (p : HeightOneSpectrum (𝓞 ℚ)) : SecondCountableTopology (p.adicCompletion ℚ) :=
  secondCountable_of_proper

attribute [local instance] localSecondCountable

private theorem archRowsSecondCountable : SecondCountableTopology (Fin 3 → InfiniteAdeleRing ℚ) :=
  inferInstance

private theorem localRowsSecondCountable (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    SecondCountableTopology (∀ k : Fin 3 × {p // p ∈ S}, k.2.1.adicCompletion ℚ) :=
  inferInstance

attribute [local instance] archRowsSecondCountable localRowsSecondCountable

private theorem secondCountableCoords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : SecondCountableTopology (Coords S) :=
  inferInstance

attribute [local instance] secondCountableCoords

private theorem archRowsBorel : BorelSpace (Fin 3 → InfiniteAdeleRing ℚ) := Pi.borelSpace

private theorem localRowsBorel (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    BorelSpace (∀ k : Fin 3 × {p // p ∈ S}, k.2.1.adicCompletion ℚ) :=
  Pi.borelSpace

attribute [local instance] archRowsBorel localRowsBorel

private theorem borelCoords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : BorelSpace (Coords S) := Prod.borelSpace

attribute [local instance] borelCoords

private theorem locallyCompactCoords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : LocallyCompactSpace (Coords S) :=
  inferInstance

attribute [local instance] locallyCompactCoords

private theorem sigmaCompactCoords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : SigmaCompactSpace (Coords S) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

attribute [local instance] sigmaCompactCoords

private def coordsHaar (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Measure (Coords S) :=
  Measure.addHaarMeasure (Classical.arbitrary _)

private theorem coordsHaar_isAddHaarMeasure (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    (coordsHaar S).IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_addHaarMeasure _

attribute [local instance] coordsHaar_isAddHaarMeasure

private theorem sigmaFinite_coordsHaar (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : SigmaFinite (coordsHaar S) :=
  inferInstance

attribute [local instance] sigmaFinite_coordsHaar

end UniquenessHead
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end UniquenessPrinciple
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Assembly

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

attribute [local instance] secondCountableTopology_adelicGL3 isMulRightInvariant_adelicGLHaar

attribute [local instance] WhittakerBlock.isHaarMeasure_unipotentHaar3

attribute [local instance] WhittakerBlock.isMulRightInvariant_unipotentHaar3

private scoped instance locallyCompactSpace_mirabolic : LocallyCompactSpace ↥mirabolic :=
  isClosed_mirabolic.locallyCompactSpace

private scoped instance sigmaCompactSpace_mirabolic : SigmaCompactSpace ↥mirabolic :=
  isClosed_mirabolic.sigmaCompactSpace

private abbrev fibreModulus (p : ↥mirabolic) : ℝ≥0∞ := modulus (p : AdelicGL 3 (𝓞 ℚ) ℚ)

private theorem measurable_fibreModulus : Measurable fibreModulus :=
  measurable_modulus.comp measurable_subtype_coe

private theorem fibreModulus_mul (p q : ↥mirabolic) : fibreModulus (p * q) = fibreModulus p * fibreModulus q :=
  modulus_mul _ _

private theorem continuous_fibreModulus : Continuous fibreModulus :=
  continuous_ofReal_ideleNorm_det.comp continuous_subtype_val

private scoped instance locallyCompactSpace_unipotent : LocallyCompactSpace ↥WhittakerBlock.unipotentSubgroup3 :=
  WhittakerBlock.isClosed_unipotentSubgroup3.locallyCompactSpace

private scoped instance sigmaCompactSpace_unipotent : SigmaCompactSpace ↥WhittakerBlock.unipotentSubgroup3 :=
  WhittakerBlock.isClosed_unipotentSubgroup3.sigmaCompactSpace

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

open Topology Set

section RightInvariantComparison

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private theorem exists_eq_smul_of_isMulRightInvariant_of_isOpenPosMeasure (m μ : Measure G) [μ.IsMulRightInvariant]
    [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts m] [m.IsMulRightInvariant] :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ m = c • μ := by
  haveI : Measure.IsHaarMeasure μ.inv :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  obtain ⟨c, hc⟩ : ∃ c : NNReal, m.inv = c • μ.inv := ⟨_, Measure.isMulLeftInvariant_eq_smul m.inv μ.inv⟩
  refine ⟨c, ENNReal.coe_ne_top, ?_⟩
  ext s hs
  calc m s = m.inv.inv s := by rw [Measure.inv_inv]
    _ = m.inv s⁻¹ := Measure.inv_apply _ _
    _ = (c • μ.inv) s⁻¹ := by rw [hc]
    _ = c * μ.inv s⁻¹ := Measure.coe_nnreal_smul_apply _ _ _
    _ = c * μ s := by rw [Measure.inv_apply, inv_inv]
    _ = ((c : ℝ≥0∞) • μ) s := by rw [Measure.smul_apply, smul_eq_mul]

private theorem exists_ne_zero_and_eq_smul_of_isMulRightInvariant_of_ne_zero (m μ : Measure G) [μ.IsMulRightInvariant]
    [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts m] [m.IsMulRightInvariant]
    (hm : m ≠ 0) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • m := by
  obtain ⟨c, hctop, hmc⟩ := exists_eq_smul_of_isMulRightInvariant_of_isOpenPosMeasure m μ
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hm (by rw [hmc, zero_smul])
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.2 hctop, ENNReal.inv_ne_top.2 hc0, ?_⟩
  rw [hmc, smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]

end RightInvariantComparison
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section WeightedFiniteness

variable {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]

private theorem isFiniteMeasureOnCompacts_withDensity_inv (ρ : Measure X) [IsFiniteMeasureOnCompacts ρ] {f : X → ℝ≥0∞}
    (hf : Continuous f) (hf0 : ∀ x, f x ≠ 0) : IsFiniteMeasureOnCompacts (ρ.withDensity fun x => (f x)⁻¹) := by
  refine ⟨fun {C} hC => ?_⟩
  obtain ⟨m, hm0, hmC⟩ := exists_ne_zero_le_on_of_isCompact hf hf0 hC
  rw [withDensity_apply _ hC.isClosed.measurableSet]
  calc ∫⁻ x in C, (f x)⁻¹ ∂ρ ≤ ∫⁻ _ in C, m⁻¹ ∂ρ :=
        setLIntegral_mono' hC.isClosed.measurableSet fun x hx => ENNReal.inv_le_inv.2 (hmC x hx)
    _ = m⁻¹ * ρ C := setLIntegral_const C m⁻¹
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hm0)) hC.measure_lt_top

end WeightedFiniteness
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section TorusMeasure

variable {T : Type} [Group T] [MeasurableSpace T] {A : Type} [CommGroup A] [MeasurableSpace A]

private theorem lintegral_mul_right_map_eq [MeasurableMul A] (h : Measure T) [h.IsMulLeftInvariant] [MeasurableMul T]
    {d : T → A} (hd : Measurable d) (hdmul : ∀ t t', d (t * t') = d t * d t') {τ : A → T} (hdτ : ∀ y, d (τ y) = y)
    (y : A)
    {F : A → ℝ≥0∞} (hF : Measurable F) : ∫⁻ x, F (x * y) ∂(Measure.map d h) = ∫⁻ x, F x ∂(Measure.map d h) := by
  have hFy : Measurable fun x => F (x * y) := hF.comp (measurable_mul_const y)
  rw [lintegral_map hFy hd, lintegral_map hF hd]
  calc ∫⁻ t, F (d t * y) ∂h = ∫⁻ t, F (d (τ y * t)) ∂h := by
        refine lintegral_congr fun t => ?_
        rw [hdmul, hdτ, mul_comm]
    _ = ∫⁻ t, F (d t) ∂h := lintegral_mul_left_eq_self (fun t => F (d t)) (τ y)

private theorem lintegral_mul_right_withDensity (ρ₀ : Measure A) [MeasurableMul A]
    (hρ₀ : ∀ (y : A) {F : A → ℝ≥0∞}, Measurable F → ∫⁻ x, F (x * y) ∂ρ₀ = ∫⁻ x, F x ∂ρ₀) {w : A → ℝ≥0∞}
    (hw : Measurable w) (hwmul : ∀ x y, w (x * y) = w x * w y) (hw0 : ∀ x, w x ≠ 0) (hwtop : ∀ x, w x ≠ ⊤) (y : A)
    {F : A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (x * y) ∂(ρ₀.withDensity w) = (w y)⁻¹ * ∫⁻ x, F x ∂(ρ₀.withDensity w) := by
  have hFy : Measurable fun x => F (x * y) := hF.comp (measurable_mul_const y)
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hFy, lintegral_withDensity_eq_lintegral_mul _ hw hF]

  have hG : Measurable fun x => w (x * y⁻¹) * F x := (hw.comp (measurable_mul_const y⁻¹)).mul hF
  have h1 : (fun x => (w * fun x => F (x * y)) x) = fun x => (fun x => w (x * y⁻¹) * F x) (x * y) := by
    funext x
    simp only [Pi.mul_apply, mul_inv_cancel_right]
  rw [h1, hρ₀ y hG]
  have h2 : ∀ x, w (x * y⁻¹) * F x = (w y)⁻¹ * (w x * F x) := by
    intro x
    have hx : w x = w (x * y⁻¹) * w y := by rw [← hwmul, inv_mul_cancel_right]
    rw [hx, mul_assoc, mul_left_comm (w (x * y⁻¹)), ← mul_assoc, ENNReal.inv_mul_cancel (hw0 y) (hwtop y), one_mul]
  simp only [h2, Pi.mul_apply]
  exact lintegral_const_mul _ (hw.mul hF)

end TorusMeasure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section TriangularShift

variable {A : Type} [MeasurableSpace A] {M : Type} [AddCommGroup M] [MeasurableSpace M] [MeasurableAdd₂ M]

private theorem lintegral_triangular_shift (ρ : Measure A) [SFinite ρ] (H : Measure M) [SFinite H]
    [H.IsAddRightInvariant] {σ : A → A} (hσ : Measurable σ) {κ : ℝ≥0∞}
    (hρ : ∀ {F : A → ℝ≥0∞}, Measurable F → ∫⁻ a, F (σ a) ∂ρ = κ * ∫⁻ a, F a ∂ρ) {f₁ : A → M} (hf₁ : Measurable f₁)
    {f₂ : A × M → M} (hf₂ : Measurable f₂) (c : M) {Φ : A × (M × (M × M)) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ q, Φ (σ q.1, (q.2.1 + f₁ q.1, (q.2.2.1 + f₂ (q.1, q.2.1), q.2.2.2 + c))) ∂(ρ.prod (H.prod (H.prod H))) =
      κ * ∫⁻ q, Φ q ∂(ρ.prod (H.prod (H.prod H))) := by

  have hΦ' : ∀ a, Measurable fun v : M × (M × M) => Φ (a, v) := fun a =>
    hΦ.comp (measurable_const.prodMk measurable_id)
  have hinner : ∀ a x, Measurable fun yz : M × M => Φ (a, (x, yz)) := fun a x =>
    hΦ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hlast : ∀ a x y', Measurable fun z : M => Φ (a, (x, (y', z))) := fun a x y' =>
    hΦ.comp (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_id)))

  have hslice : ∀ a : A,
      ∫⁻ v : M × (M × M), Φ (σ a, (v.1 + f₁ a, (v.2.1 + f₂ (a, v.1), v.2.2 + c))) ∂(H.prod (H.prod H)) =
        ∫⁻ v : M × (M × M), Φ (σ a, v) ∂(H.prod (H.prod H)) := by
    intro a
    have hm1 : Measurable fun v : M × (M × M) => Φ (σ a, (v.1 + f₁ a, (v.2.1 + f₂ (a, v.1), v.2.2 + c))) := by
      refine hΦ.comp (measurable_const.prodMk ((measurable_fst.add_const _).prodMk (Measurable.prodMk ?_ ?_)))
      · exact (measurable_snd.comp measurable_id |>.fst).add (hf₂.comp (measurable_const.prodMk measurable_fst))
      · exact (measurable_snd.snd).add_const _
    rw [lintegral_prod _ hm1.aemeasurable, lintegral_prod _ (hΦ' (σ a)).aemeasurable]

    have hx : ∀ x : M,
        ∫⁻ yz : M × M, Φ (σ a, (x + f₁ a, (yz.1 + f₂ (a, x), yz.2 + c))) ∂(H.prod H) =
          ∫⁻ yz : M × M, Φ (σ a, (x + f₁ a, yz)) ∂(H.prod H) := by
      intro x
      have hm2 : Measurable fun yz : M × M => Φ (σ a, (x + f₁ a, (yz.1 + f₂ (a, x), yz.2 + c))) :=
        hΦ.comp (measurable_const.prodMk (measurable_const.prodMk
          ((measurable_fst.add_const _).prodMk (measurable_snd.add_const _))))
      rw [lintegral_prod _ hm2.aemeasurable, lintegral_prod _ (hinner (σ a) (x + f₁ a)).aemeasurable]
      have hy : ∀ y' : M, ∫⁻ z, Φ (σ a, (x + f₁ a, (y' + f₂ (a, x), z + c))) ∂H =
          ∫⁻ z, Φ (σ a, (x + f₁ a, (y' + f₂ (a, x), z))) ∂H :=
        fun y' => lintegral_add_right_eq_self (fun z => Φ (σ a, (x + f₁ a, (y' + f₂ (a, x), z)))) c
      simp only [hy]
      exact lintegral_add_right_eq_self (fun y' => ∫⁻ z, Φ (σ a, (x + f₁ a, (y', z))) ∂H) (f₂ (a, x))
    simp only [hx]
    exact lintegral_add_right_eq_self (fun x => ∫⁻ yz : M × M, Φ (σ a, (x, yz)) ∂(H.prod H)) (f₁ a)
  have hmΦ : Measurable fun q : A × (M × (M × M)) =>
      Φ (σ q.1, (q.2.1 + f₁ q.1, (q.2.2.1 + f₂ (q.1, q.2.1), q.2.2.2 + c))) := by
    refine hΦ.comp ((hσ.comp measurable_fst).prodMk (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)))
    · exact measurable_snd.fst.add (hf₁.comp measurable_fst)
    · exact measurable_snd.snd.fst.add (hf₂.comp (measurable_fst.prodMk measurable_snd.fst))
    · exact measurable_snd.snd.snd.add_const _
  rw [lintegral_prod _ hmΦ.aemeasurable, lintegral_prod _ hΦ.aemeasurable]
  simp only [hslice]
  exact hρ (Measurable.lintegral_prod_right' (ν := H.prod (H.prod H)) hΦ)

end TriangularShift
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section LastCoordinate

variable {M : Type} [AddCommGroup M] [MeasurableSpace M] [MeasurableAdd₂ M]

private theorem lintegral_pi_three_split (μ : Measure M) [SigmaFinite μ] [μ.IsAddRightInvariant]
    {Ψ : (Fin 2 → M) → ℝ≥0∞} (hΨ : Measurable Ψ) {s : (Fin 2 → M) → M} (hs : Measurable s) {B : Set M}
    (hB : MeasurableSet B) :
    ∫⁻ x : Fin 3 → M, Ψ (fun i => x i.castSucc) * B.indicator 1 (x (Fin.last 2) + s fun i => x i.castSucc)
        ∂(Measure.pi fun _ : Fin 3 => μ) =
      (∫⁻ r : Fin 2 → M, Ψ r ∂(Measure.pi fun _ : Fin 2 => μ)) * μ B := by

  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => M) (Fin.last 2) with he
  have hpres := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) (Fin.last 2)
  have hG : Measurable fun p : M × (Fin 2 → M) => Ψ p.2 * B.indicator 1 (p.1 + s p.2) :=
    (hΨ.comp measurable_snd).mul
      ((measurable_one.indicator hB).comp (measurable_fst.add (hs.comp measurable_snd)))
  have hcomp : ∀ x : Fin 3 → M,
      Ψ (fun i => x i.castSucc) * B.indicator 1 (x (Fin.last 2) + s fun i => x i.castSucc) =
        (fun p : M × (Fin 2 → M) => Ψ p.2 * B.indicator 1 (p.1 + s p.2)) (e x) := by
    intro x
    show _ = Ψ (fun j => x ((Fin.last 2).succAbove j)) *
      B.indicator 1 (x (Fin.last 2) + s fun j => x ((Fin.last 2).succAbove j))
    simp only [Fin.succAbove_last]
  simp only [hcomp]
  rw [hpres.lintegral_comp hG]

  rw [lintegral_prod_symm' _ hG]
  simp only
  have hinner : ∀ r : Fin 2 → M, ∫⁻ t, Ψ r * B.indicator 1 (t + s r) ∂μ = Ψ r * μ B := by
    intro r
    have hind : Measurable fun t => B.indicator (1 : M → ℝ≥0∞) (t + s r) :=
      (measurable_one.indicator hB).comp (measurable_add_const (s r))
    rw [lintegral_const_mul _ hind, lintegral_add_right_eq_self (B.indicator (1 : M → ℝ≥0∞)) (s r),
      lintegral_indicator_one hB]
  simp only [hinner]
  exact lintegral_mul_const _ hΨ

end LastCoordinate
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section KernelMatrix

variable {A : Type} [CommRing A]

private def kernelMatrix (a x y z : A) : Matrix (Fin 3) (Fin 3) A :=
  !![a, x, y; 0, 1, z; 0, 0, 1]

private theorem kernelMatrix_mul (a x y z a' x' y' z' : A) :
    kernelMatrix a x y z * kernelMatrix a' x' y' z' =
      kernelMatrix (a * a') (x + a * x') (y + (a * y' + x * z')) (z' + z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kernelMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem kernelMatrix_det (a x y z : A) : (kernelMatrix a x y z).det = a := by
  simp [kernelMatrix, Matrix.det_fin_three]

private def kernelMatrixInv (u : Aˣ) (x y z : A) : Matrix (Fin 3) (Fin 3) A :=
  kernelMatrix (↑u⁻¹ : A) (-(↑u⁻¹ * x)) (↑u⁻¹ * (x * z - y)) (-z)

private theorem kernelMatrix_mul_kernelMatrixInv (u : Aˣ) (x y z : A) :
    kernelMatrix (u : A) x y z * kernelMatrixInv u x y z = 1 := by
  unfold kernelMatrixInv
  rw [kernelMatrix_mul]
  have hu : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  have h1 : x + (u : A) * -((↑u⁻¹ : A) * x) = 0 := by linear_combination (-x) * hu
  have h2 : y + ((u : A) * ((↑u⁻¹ : A) * (x * z - y)) + x * -z) = 0 := by linear_combination (x * z - y) * hu
  rw [hu, h1, h2, neg_add_cancel]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem kernelMatrixInv_mul_kernelMatrix (u : Aˣ) (x y z : A) :
    kernelMatrixInv u x y z * kernelMatrix (u : A) x y z = 1 := by
  unfold kernelMatrixInv
  rw [kernelMatrix_mul]
  have hu : (↑u⁻¹ : A) * (u : A) = 1 := Units.inv_mul u
  have h1 : -((↑u⁻¹ : A) * x) + (↑u⁻¹ : A) * x = 0 := neg_add_cancel _
  have h2 : (↑u⁻¹ : A) * (x * z - y) + ((↑u⁻¹ : A) * y + -((↑u⁻¹ : A) * x) * z) = 0 := by ring
  rw [hu, h1, h2, add_neg_cancel]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem kernelMatrix_apply_zero_one (a x y z : A) : kernelMatrix a x y z 0 1 = x := rfl
private theorem kernelMatrix_apply_zero_two (a x y z : A) : kernelMatrix a x y z 0 2 = y := rfl
private theorem kernelMatrix_apply_one_two (a x y z : A) : kernelMatrix a x y z 1 2 = z := rfl
private theorem kernelMatrix_apply_one_zero (a x y z : A) : kernelMatrix a x y z 1 0 = 0 := rfl
private theorem kernelMatrix_apply_one_one (a x y z : A) : kernelMatrix a x y z 1 1 = 1 := rfl
private theorem kernelMatrix_apply_two (a x y z : A) (j : Fin 3) :
    kernelMatrix a x y z 2 j = if j = 2 then 1 else 0 := by
  fin_cases j <;> rfl

private theorem eq_kernelMatrix_of_rows (N : Matrix (Fin 3) (Fin 3) A) (h10 : N 1 0 = 0) (h11 : N 1 1 = 1)
    (h20 : N 2 0 = 0) (h21 : N 2 1 = 0) (h22 : N 2 2 = 1) : N = kernelMatrix (N 0 0) (N 0 1) (N 0 2) (N 1 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kernelMatrix, h10, h11, h20, h21, h22]

end KernelMatrix
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section KernelMatrixContinuity

variable {A : Type} [CommRing A] [TopologicalSpace A] {X : Type} [TopologicalSpace X]

private theorem continuous_kernelMatrix {a x y z : X → A} (ha : Continuous a) (hx : Continuous x) (hy : Continuous y)
    (hz : Continuous z) : Continuous fun q => kernelMatrix (a q) (x q) (y q) (z q) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [kernelMatrix] <;>
    first | exact ha | exact hx | exact hy | exact hz | exact continuous_const

end KernelMatrixContinuity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UnitsMeasurability

variable {R : Type} [Monoid R] [MeasurableSpace R]

private theorem measurable_units_of_val {X : Type} [MeasurableSpace X] {f : X → Rˣ}
    (hf : Measurable fun q => (f q : R)) : Measurable f := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap f (MeasurableSpace.comap Units.val ‹MeasurableSpace R›) ≤ _
  rw [MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 hf

private theorem measurable_units_val : Measurable fun u : Rˣ => (u : R) := comap_measurable _

private theorem measurableMul_units [MeasurableMul R] : MeasurableMul Rˣ where
  measurable_const_mul c := measurable_units_of_val (by
    simp only [Units.val_mul]
    exact (measurable_const_mul (c : R)).comp measurable_units_val)
  measurable_mul_const c := measurable_units_of_val (by
    simp only [Units.val_mul]
    exact (measurable_mul_const (c : R)).comp measurable_units_val)

end UnitsMeasurability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section CoarseStructure

variable {U : Type} [TopologicalSpace U] {m : MeasurableSpace U}

private theorem measurableSet_comap_of_isCompact {A : Type} [TopologicalSpace A] [T2Space A] [mA : MeasurableSpace A]
    [OpensMeasurableSpace A] {val : U → A} (hinj : Function.Injective val) (hcont : Continuous val) {K : Set U}
    (hK : IsCompact K) : MeasurableSet[mA.comap val] K := by
  rw [← hinj.preimage_image K]
  exact MeasurableSpace.measurableSet_comap.2 ⟨val '' K, (hK.image hcont).isClosed.measurableSet, rfl⟩

private theorem isFiniteMeasureOnCompacts_trim (ν : Measure[borel U] U) (hm : m ≤ borel U)
    (hν : @IsFiniteMeasureOnCompacts U (borel U) _ ν) (hK : ∀ K : Set U, IsCompact K → MeasurableSet[m] K) :
    @IsFiniteMeasureOnCompacts U m _ (ν.trim hm) :=
  @IsFiniteMeasureOnCompacts.mk U m _ (ν.trim hm) fun K hKc => by
    rw [trim_measurableSet_eq hm (hK K hKc)]
    exact hν.lt_top_of_isCompact hKc

private theorem sigmaFinite_trim_of_isCompact [SigmaCompactSpace U] (ν : Measure[borel U] U) (hm : m ≤ borel U)
    (hν : @IsFiniteMeasureOnCompacts U (borel U) _ ν) (hK : ∀ K : Set U, IsCompact K → MeasurableSet[m] K) :
    @SigmaFinite U m (ν.trim hm) :=
  @SigmaFinite.mk U m (ν.trim hm) ⟨{
    set := compactCovering U,
    set_mem := fun _ => mem_univ _,
    finite := fun n => by
      rw [trim_measurableSet_eq hm (hK _ (isCompact_compactCovering U n))]
      exact hν.lt_top_of_isCompact (isCompact_compactCovering U n),
    spanning := iUnion_compactCovering U }⟩

private theorem trim_univ_ne_zero (ν : Measure[borel U] U) (hm : m ≤ borel U) (hν : ν univ ≠ 0) :
    ν.trim hm univ ≠ 0 := by
  rw [trim_measurableSet_eq hm MeasurableSet.univ]
  exact hν

private theorem lintegral_trim_transform (ν : Measure[borel U] U) (hm : m ≤ borel U) {σ : U → U} {c : ℝ≥0∞}
    (hlaw : ∀ {F : U → ℝ≥0∞}, Measurable[borel U] F → ∫⁻ x, F (σ x) ∂ν = c * ∫⁻ x, F x ∂ν) {F : U → ℝ≥0∞}
    (hF : Measurable[m] F) (hFσ : Measurable[m] fun x => F (σ x)) :
    ∫⁻ x, F (σ x) ∂(ν.trim hm) = c * ∫⁻ x, F x ∂(ν.trim hm) := by
  rw [lintegral_trim hm hFσ, lintegral_trim hm hF]
  exact hlaw (hF.mono hm le_rfl)

end CoarseStructure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UnitsBorelTopology

variable {R : Type} [Monoid R] [TopologicalSpace R]

private theorem isInducing_unitsPair : IsInducing fun u : Rˣ => ((u : R), ((u⁻¹ : Rˣ) : R)) := by
  have h : (fun u : Rˣ => ((u : R), ((u⁻¹ : Rˣ) : R))) =
      ((Homeomorph.refl R).prodCongr MulOpposite.opHomeomorph.symm) ∘ Units.embedProduct R := by
    funext u
    rfl
  rw [h]
  exact ((Homeomorph.refl R).prodCongr MulOpposite.opHomeomorph.symm).isInducing.comp Units.isInducing_embedProduct

end UnitsBorelTopology
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UnitsBorel

variable {R : Type} [Monoid R] [TopologicalSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]

private theorem borel_units_eq_comap :
    borel Rˣ = MeasurableSpace.comap (fun u : Rˣ => ((u : R), ((u⁻¹ : Rˣ) : R))) Prod.instMeasurableSpace := by
  rw [isInducing_unitsPair.eq_induced, borel_comap, Prod.borelSpace.measurable_eq]

private theorem measurable_units_borel_of_val_of_inv {X : Type} [MeasurableSpace X] {f : X → Rˣ}
    (h₁ : Measurable fun x => (f x : R)) (h₂ : Measurable fun x => (((f x)⁻¹ : Rˣ) : R)) :
    Measurable[_, borel Rˣ] f := by
  rw [borel_units_eq_comap, measurable_iff_comap_le, MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 (h₁.prodMk h₂)

private theorem measurable_units_borel_val : Measurable[borel Rˣ, _] fun u : Rˣ => (u : R) := by
  rw [borel_units_eq_comap]
  exact measurable_fst.comp (comap_measurable _)

private theorem measurable_units_borel_inv_val : Measurable[borel Rˣ, _] fun u : Rˣ => ((u⁻¹ : Rˣ) : R) := by
  rw [borel_units_eq_comap]
  exact measurable_snd.comp (comap_measurable _)

end UnitsBorel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section MatrixBorel

variable {A : Type} [TopologicalSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

private theorem borel_matrix_eq :
    borel (Matrix (Fin 3) (Fin 3) A) = (MeasurableSpace.pi : MeasurableSpace (Fin 3 → Fin 3 → A)) :=
  (inferInstance : BorelSpace (Fin 3 → Fin 3 → A)).measurable_eq.symm

private theorem measurable_matrix_borel_of_entries {X : Type} [MeasurableSpace X] {M : X → Matrix (Fin 3) (Fin 3) A}
    (h : ∀ i j, Measurable fun x => M x i j) : Measurable[_, borel (Matrix (Fin 3) (Fin 3) A)] M := by
  rw [borel_matrix_eq]
  exact measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => h i j

end MatrixBorel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section MatrixUnitsBorel

variable {A : Type} [CommRing A] [TopologicalSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

private theorem measurable_matrixUnits_borel_of_entries {X : Type} [MeasurableSpace X]
    {f : X → (Matrix (Fin 3) (Fin 3) A)ˣ} (h₁ : ∀ i j, Measurable fun x => (f x : Matrix (Fin 3) (Fin 3) A) i j)
    (h₂ : ∀ i j, Measurable fun x => (((f x)⁻¹ : (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A) i j) :
    Measurable[_, borel (Matrix (Fin 3) (Fin 3) A)ˣ] f := by
  letI : MeasurableSpace (Matrix (Fin 3) (Fin 3) A) := borel _
  haveI : BorelSpace (Matrix (Fin 3) (Fin 3) A) := ⟨rfl⟩
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → A))
  exact measurable_units_borel_of_val_of_inv (measurable_matrix_borel_of_entries h₁)
    (measurable_matrix_borel_of_entries h₂)

end MatrixUnitsBorel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section IdeleInversion

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

open Filter Topology Set
open scoped RestrictedProduct NNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] archBorel archBorelSpace localBorel localBorelSpace countable_primes
attribute [local instance] properCompletion archSecondCountable localSecondCountable secondCountableAdeles

open scoped Classical in

private def unitPiece (T : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set 𝔸 :=
  {u | (∀ w, u.1 w ≠ 0) ∧ (∀ p, u.2 p ≠ 0) ∧ ∀ p, p ∉ T → Valued.v (u.2 p) = 1}

private theorem continuous_archCoordinate (w : InfinitePlace ℚ) : Continuous fun u : 𝔸 => u.1 w :=
  (continuous_apply w).comp continuous_fst

private theorem continuous_finCoordinate (p : HeightOneSpectrum (𝓞 ℚ)) : Continuous fun u : 𝔸 => u.2 p :=
  (AdelicLevel.continuous_finAdeleEval (R := 𝓞 ℚ) (K := ℚ) p).comp
    (AdelicLevel.continuous_adeleFin (R := 𝓞 ℚ) (K := ℚ))

private theorem measurableSet_unitPiece (T : Finset (HeightOneSpectrum (𝓞 ℚ))) : MeasurableSet (unitPiece T) := by
  have h₁ : MeasurableSet {u : 𝔸 | ∀ w, u.1 w ≠ 0} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun w => (isOpen_ne.preimage (continuous_archCoordinate w)).measurableSet
  have h₂ : MeasurableSet {u : 𝔸 | ∀ p, u.2 p ≠ 0} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun p => (isOpen_ne.preimage (continuous_finCoordinate p)).measurableSet
  have h₃ : MeasurableSet {u : 𝔸 | ∀ p, p ∉ T → Valued.v (u.2 p) = 1} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun p => ?_
    by_cases hp : p ∈ T
    · simp only [hp, not_true_eq_false, false_implies, Set.setOf_true, MeasurableSet.univ]
    · simp only [hp, not_false_eq_true, true_implies]
      exact ((isClopen_setOf_valued_eq_one p).preimage (continuous_finCoordinate p)).isClosed.measurableSet
  exact h₁.inter (h₂.inter h₃)

private theorem arch_inv_val (y : 𝔸ˣ) (w : InfinitePlace ℚ) : ((y⁻¹ : 𝔸ˣ) : 𝔸).1 w = ((y : 𝔸).1 w)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← arch_mul_apply, Units.mul_inv, arch_one_apply])

private theorem fin_inv_val (y : 𝔸ˣ) (p : HeightOneSpectrum (𝓞 ℚ)) : ((y⁻¹ : 𝔸ˣ) : 𝔸).2 p = ((y : 𝔸).2 p)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← fin_mul_apply, Units.mul_inv, fin_one_apply])

private theorem arch_val_ne_zero (y : 𝔸ˣ) (w : InfinitePlace ℚ) : (y : 𝔸).1 w ≠ 0 := fun h => by
  have := congrArg (fun a : 𝔸 => a.1 w) (Units.mul_inv y)
  simp only [arch_mul_apply, arch_one_apply, h, zero_mul] at this
  exact zero_ne_one this

private theorem fin_val_ne_zero (y : 𝔸ˣ) (p : HeightOneSpectrum (𝓞 ℚ)) : (y : 𝔸).2 p ≠ 0 := fun h => by
  have := congrArg (fun a : 𝔸 => a.2 p) (Units.mul_inv y)
  simp only [fin_mul_apply, fin_one_apply, h, zero_mul] at this
  exact zero_ne_one this

private theorem eventually_valued_val_eq_one (y : 𝔸ˣ) :
    ∀ᶠ p in Filter.cofinite, Valued.v ((y : 𝔸).2 p) = 1 := by
  filter_upwards [(y : 𝔸).2.2, ((y⁻¹ : 𝔸ˣ) : 𝔸).2.2] with p h₁ h₂
  have h₁' : Valued.v ((y : 𝔸).2 p) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mp h₁
  have h₂' : Valued.v (((y : 𝔸).2 p)⁻¹) ≤ 1 := by
    rw [← fin_inv_val]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mp h₂
  rw [map_inv₀] at h₂'
  have hpos : 0 < Valued.v ((y : 𝔸).2 p) := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff _).2 (fin_val_ne_zero y p))
  exact le_antisymm h₁' ((inv_le_one₀ hpos).mp h₂')

private theorem exists_val_mem_unitPiece (y : 𝔸ˣ) : ∃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), (y : 𝔸) ∈ unitPiece T := by
  have hfin : {p : HeightOneSpectrum (𝓞 ℚ) | ¬ Valued.v ((y : 𝔸).2 p) = 1}.Finite :=
    Filter.eventually_cofinite.mp (eventually_valued_val_eq_one y)
  refine ⟨hfin.toFinset, arch_val_ne_zero y, fin_val_ne_zero y, fun p hp => ?_⟩
  by_contra h
  exact hp (hfin.mem_toFinset.mpr h)

private theorem isUnit_of_mem_unitPiece {T : Finset (HeightOneSpectrum (𝓞 ℚ))} {u : 𝔸} (hu : u ∈ unitPiece T) :
    IsUnit u := by
  obtain ⟨harch, hfin, hval⟩ := hu
  refine Prod.isUnit_iff.mpr ⟨Pi.isUnit_iff.mpr fun w => (harch w).isUnit, ?_⟩
  refine RestrictedProduct.isUnit_of_eventually_isUnit (fun p => (hfin p).isUnit) ?_
  have hT : ∀ᶠ p in Filter.cofinite, p ∉ T := T.finite_toSet.compl_mem_cofinite
  filter_upwards [hT] with p hp
  have hone : Valued.v (u.2 p) = 1 := hval p hp
  refine ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mpr hone.le,
    isUnit_iff_exists_inv.mpr ⟨⟨(u.2 p)⁻¹, ?_⟩, ?_⟩⟩
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mpr ?_
    rw [map_inv₀, hone, inv_one]
  · exact Subtype.ext (mul_inv_cancel₀ (hfin p))

private theorem arch_ringInverse_of_mem {T : Finset (HeightOneSpectrum (𝓞 ℚ))} {u : 𝔸} (hu : u ∈ unitPiece T)
    (w : InfinitePlace ℚ) : (Ring.inverse u : 𝔸).1 w = (u.1 w)⁻¹ := by
  obtain ⟨y, rfl⟩ := isUnit_of_mem_unitPiece hu
  rw [Ring.inverse_unit, arch_inv_val]

private theorem fin_ringInverse_of_mem {T : Finset (HeightOneSpectrum (𝓞 ℚ))} {u : 𝔸} (hu : u ∈ unitPiece T)
    (p : HeightOneSpectrum (𝓞 ℚ)) : (Ring.inverse u : 𝔸).2 p = (u.2 p)⁻¹ := by
  obtain ⟨y, rfl⟩ := isUnit_of_mem_unitPiece hu
  rw [Ring.inverse_unit, fin_inv_val]

private theorem continuousOn_ringInverse_unitPiece (T : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ContinuousOn (Ring.inverse : 𝔸 → 𝔸) (unitPiece T) := by
  refine continuousOn_adele (fun w => ?_) ?_
  · refine ((continuous_archCoordinate w).continuousOn.inv₀ fun u hu => hu.1 w).congr fun u hu => ?_
    exact arch_ringInverse_of_mem hu w
  · refine continuousOn_finiteAdele T.finite_toSet (fun u => (Ring.inverse u : 𝔸).2) (fun u hu p hp => ?_) fun p => ?_
    · rw [fin_ringInverse_of_mem hu p]
      refine (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mpr ?_
      rw [map_inv₀, hu.2.2 p hp, inv_one]
    · refine ((continuous_finCoordinate p).continuousOn.inv₀ fun u hu => hu.2.1 p).congr fun u hu => ?_
      exact fin_ringInverse_of_mem hu p

private theorem measurable_ringInverse : Measurable (Ring.inverse : 𝔸 → 𝔸) := by
  refine measurable_of_pieces (s := ⋃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), unitPiece T)
    (MeasurableSet.iUnion fun T => measurableSet_unitPiece T) unitPiece measurableSet_unitPiece
    (fun T => Set.subset_iUnion unitPiece T) (fun u hu => Set.mem_iUnion.mp hu) continuousOn_ringInverse_unitPiece
    (c := 0) fun u hu => ?_
  refine Ring.inverse_non_unit u fun h => hu ?_
  obtain ⟨y, rfl⟩ := h
  obtain ⟨T, hT⟩ := exists_val_mem_unitPiece y
  exact Set.mem_iUnion.mpr ⟨T, hT⟩

private theorem measurable_inv_val : Measurable fun y : 𝔸ˣ => ((y⁻¹ : 𝔸ˣ) : 𝔸) := by
  have h : (fun y : 𝔸ˣ => ((y⁻¹ : 𝔸ˣ) : 𝔸)) = fun y : 𝔸ˣ => Ring.inverse (y : 𝔸) := by
    funext y
    rw [Ring.inverse_unit]
  rw [h]
  exact measurable_ringInverse.comp measurable_units_val

private theorem measurable_units_inv : Measurable fun y : 𝔸ˣ => y⁻¹ :=
  measurable_units_of_val measurable_inv_val

private def torusElement (y : 𝔸ˣ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  ⟨kernelMatrix (y : 𝔸) 0 0 0, kernelMatrixInv y 0 0 0, kernelMatrix_mul_kernelMatrixInv y 0 0 0,
    kernelMatrixInv_mul_kernelMatrix y 0 0 0⟩

private theorem coe_torusElement (y : 𝔸ˣ) :
    ((torusElement y : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) = kernelMatrix (y : 𝔸) 0 0 0 := rfl

private theorem coe_torusElement_inv (y : 𝔸ˣ) :
    (((torusElement y)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) = kernelMatrixInv y 0 0 0 := rfl

private theorem torusElement_mul (y z : 𝔸ˣ) : torusElement (y * z) = torusElement y * torusElement z := by
  apply Units.ext
  rw [Units.val_mul, coe_torusElement, coe_torusElement, coe_torusElement, kernelMatrix_mul, Units.val_mul]
  simp only [mul_zero, add_zero]

private theorem det_torusElement (y : 𝔸ˣ) : Matrix.GeneralLinearGroup.det (torusElement y) = y := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_torusElement, kernelMatrix_det]

private theorem measurable_torusElement : Measurable torusElement := by
  refine measurable_matrixUnits_borel_of_entries (fun i j => ?_) fun i j => ?_
  · simp only [coe_torusElement]
    fin_cases i <;> fin_cases j <;> simp only [kernelMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] <;> first | exact measurable_units_val | exact measurable_const
  · simp only [coe_torusElement_inv, kernelMatrixInv, mul_zero, neg_zero, sub_zero]
    fin_cases i <;> fin_cases j <;> simp only [kernelMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] <;> first | exact measurable_inv_val | exact measurable_const

end IdeleInversion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section KernelChart

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel secondCountableTopology_adelicGL3
attribute [local instance] secondCountableAdeles

private theorem matrix_two_of_mem (p : ↥mirabolic) (j : Fin 3) :
    ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 2 j = if j = 2 then 1 else 0 := by
  have h : bottomRow (p : AdelicGL 3 (𝓞 ℚ) ℚ) = e₃ := p.2
  have := congrFun h j
  simpa [bottomRow, e₃] using this

private theorem matrix_one_of_leviRow_eq {p : ↥mirabolic} (hp : leviRow p = e₂) :
    ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 1 0 = 0 ∧
      ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 1 1 = 1 := by
  have h0 := congrFun hp 0
  have h1 := congrFun hp 1
  simp only [leviRow, e₂] at h0 h1
  exact ⟨by simpa using h0, by simpa using h1⟩

private theorem coe_eq_kernelMatrix_of_leviRow_eq {p : ↥mirabolic} (hp : leviRow p = e₂) :
    ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) =
      kernelMatrix (((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 0 0)
        (((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 0 1)
        (((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 0 2)
        (((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 1 2) := by
  obtain ⟨h10, h11⟩ := matrix_one_of_leviRow_eq hp
  exact eq_kernelMatrix_of_rows _ h10 h11 (by simpa using matrix_two_of_mem p 0)
    (by simpa using matrix_two_of_mem p 1) (by simpa using matrix_two_of_mem p 2)

private theorem val_det_eq_of_leviRow_eq {p : ↥mirabolic} (hp : leviRow p = e₂) :
    ((Matrix.GeneralLinearGroup.det (p : AdelicGL 3 (𝓞 ℚ) ℚ) : 𝔸ˣ) : 𝔸) =
      ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 0 0 := by
  change ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸).det = _
  conv_lhs => rw [coe_eq_kernelMatrix_of_leviRow_eq hp]
  exact kernelMatrix_det _ _ _ _

private abbrev ChartCoords : Type := 𝔸ˣ × (𝔸 × (𝔸 × 𝔸))

private def kernelUnit (q : ChartCoords) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  glOf (kernelMatrix (q.1 : 𝔸) q.2.1 q.2.2.1 q.2.2.2) (kernelMatrixInv q.1 q.2.1 q.2.2.1 q.2.2.2)
    (kernelMatrix_mul_kernelMatrixInv q.1 q.2.1 q.2.2.1 q.2.2.2)

private theorem coe_kernelUnit (q : ChartCoords) :
    ((kernelUnit q : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) =
      kernelMatrix (q.1 : 𝔸) q.2.1 q.2.2.1 q.2.2.2 := rfl

private theorem coe_kernelUnit_inv (q : ChartCoords) :
    (((kernelUnit q)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) =
      kernelMatrixInv q.1 q.2.1 q.2.2.1 q.2.2.2 := rfl

private theorem kernelUnit_mem_mirabolic (q : ChartCoords) : kernelUnit q ∈ mirabolic := by
  show bottomRow (kernelUnit q) = e₃
  funext j
  simp only [bottomRow, coe_kernelUnit, e₃]
  fin_cases j <;> simp [kernelMatrix]

private def kernelElt (q : ChartCoords) : ↥mirabolic := ⟨kernelUnit q, kernelUnit_mem_mirabolic q⟩

private theorem leviRow_kernelElt (q : ChartCoords) : leviRow (kernelElt q) = e₂ := by
  funext i
  simp only [leviRow, kernelElt, coe_kernelUnit, e₂]
  fin_cases i <;> simp [kernelMatrix]

private theorem mirabolicChart_kernelElt (q : ChartCoords) : mirabolicChart (kernelElt q) = q := by
  obtain ⟨u, x, y, z⟩ := q
  simp only [mirabolicChart, kernelElt, coe_kernelUnit, kernelMatrix_apply_zero_one, kernelMatrix_apply_zero_two,
    kernelMatrix_apply_one_two]
  refine Prod.ext ?_ rfl
  apply Units.ext
  exact kernelMatrix_det (u : 𝔸) x y z

private theorem kernelElt_mirabolicChart {p : ↥mirabolic} (hp : leviRow p = e₂) :
    kernelElt (mirabolicChart p) = p := by
  apply Subtype.ext
  apply Units.ext
  change kernelMatrix _ _ _ _ = ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸)
  conv_rhs => rw [coe_eq_kernelMatrix_of_leviRow_eq hp]
  simp only [mirabolicChart, val_det_eq_of_leviRow_eq hp]

private theorem kernelElt_mul (q q' : ChartCoords) :
    kernelElt q * kernelElt q' =
      kernelElt (q.1 * q'.1, (q.2.1 + (q.1 : 𝔸) * q'.2.1,
        (q.2.2.1 + ((q.1 : 𝔸) * q'.2.2.1 + q.2.1 * q'.2.2.2), q.2.2.2 + q'.2.2.2))) := by
  apply Subtype.ext
  apply Units.ext
  change kernelMatrix (q.1 : 𝔸) q.2.1 q.2.2.1 q.2.2.2 * kernelMatrix (q'.1 : 𝔸) q'.2.1 q'.2.2.1 q'.2.2.2 =
    kernelMatrix ((q.1 * q'.1 : 𝔸ˣ) : 𝔸) (q.2.1 + (q.1 : 𝔸) * q'.2.1)
      (q.2.2.1 + ((q.1 : 𝔸) * q'.2.2.1 + q.2.1 * q'.2.2.2)) (q.2.2.2 + q'.2.2.2)
  rw [kernelMatrix_mul, Units.val_mul, add_comm q'.2.2.2 q.2.2.2]

private theorem continuous_kernelUnit : Continuous kernelUnit := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun q : ChartCoords => kernelMatrix (q.1 : 𝔸) q.2.1 q.2.2.1 q.2.2.2
    exact continuous_kernelMatrix (Units.continuous_val.comp continuous_fst) (continuous_fst.comp continuous_snd)
      (continuous_fst.comp (continuous_snd.comp continuous_snd))
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
  · show Continuous fun q : ChartCoords => kernelMatrixInv q.1 q.2.1 q.2.2.1 q.2.2.2
    unfold kernelMatrixInv
    have hu : Continuous fun q : ChartCoords => ((q.1⁻¹ : 𝔸ˣ) : 𝔸) :=
      Units.continuous_coe_inv.comp continuous_fst
    have hx : Continuous fun q : ChartCoords => q.2.1 := continuous_fst.comp continuous_snd
    have hy : Continuous fun q : ChartCoords => q.2.2.1 := continuous_fst.comp (continuous_snd.comp continuous_snd)
    have hz : Continuous fun q : ChartCoords => q.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
    exact continuous_kernelMatrix hu (hu.mul hx).neg (hu.mul (hx.mul hz |>.sub hy)) hz.neg

private theorem continuous_kernelElt : Continuous kernelElt :=
  continuous_kernelUnit.subtype_mk _

private theorem measurable_kernelUnit : Measurable kernelUnit := by
  have hu : Measurable fun q : ChartCoords => (q.1 : 𝔸) := measurable_units_val.comp measurable_fst
  have hui : Measurable fun q : ChartCoords => ((q.1⁻¹ : 𝔸ˣ) : 𝔸) := measurable_inv_val.comp measurable_fst
  have hx : Measurable fun q : ChartCoords => q.2.1 := measurable_fst.comp measurable_snd
  have hy : Measurable fun q : ChartCoords => q.2.2.1 := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hz : Measurable fun q : ChartCoords => q.2.2.2 := measurable_snd.comp (measurable_snd.comp measurable_snd)
  refine measurable_matrixUnits_borel_of_entries (f := kernelUnit) ?_ ?_
  · intro i j
    simp only [coe_kernelUnit]
    fin_cases i <;> fin_cases j <;> simp [kernelMatrix] <;> first | exact hu | exact hx | exact hy | exact hz
  · intro i j
    simp only [coe_kernelUnit_inv, kernelMatrixInv]
    fin_cases i <;> fin_cases j <;> simp [kernelMatrix] <;>
      first | exact hui | exact hui.mul hx | exact hui.mul ((hx.mul hz).sub hy) | exact hz

private theorem measurable_kernelElt : Measurable kernelElt :=
  measurable_kernelUnit.subtype_mk

private theorem measurable_coe_matrix_entry (i j : Fin 3) :
    Measurable fun p : ↥mirabolic => ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) i j := by
  have h : Continuous fun p : ↥mirabolic => ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) i j :=
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_coe_matrix)).comp continuous_subtype_val
  exact h.measurable

private theorem measurable_mirabolicChart : Measurable mirabolicChart := by
  refine Measurable.prodMk ?_ (Measurable.prodMk (measurable_coe_matrix_entry 0 1)
    (Measurable.prodMk (measurable_coe_matrix_entry 0 2) (measurable_coe_matrix_entry 1 2)))
  refine measurable_units_of_val ?_
  have h : Continuous fun p : ↥mirabolic =>
      ((Matrix.GeneralLinearGroup.det (p : AdelicGL 3 (𝓞 ℚ) ℚ) : 𝔸ˣ) : 𝔸) :=
    Units.continuous_val.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  exact h.measurable

end KernelChart
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section TorusMeasureFine

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] NumberField.Idele.isHaarMeasure_idelicHaar

private def ideleWeight (y : 𝔸ˣ) : ℝ≥0∞ := ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ y)

private theorem ideleWeight_ne_zero (y : 𝔸ˣ) : ideleWeight y ≠ 0 :=
  (ENNReal.ofReal_pos.2 (NumberField.TateGlobal.ideleNorm_pos _)).ne'

private theorem ideleWeight_ne_top (y : 𝔸ˣ) : ideleWeight y ≠ ⊤ := ENNReal.ofReal_ne_top

private theorem ideleWeight_mul (x y : 𝔸ˣ) : ideleWeight (x * y) = ideleWeight x * ideleWeight y := by
  unfold ideleWeight
  rw [NumberField.TateGlobal.ideleNorm_mul, ENNReal.ofReal_mul (NumberField.TateGlobal.ideleNorm_pos _).le]

private theorem continuous_ideleWeight : Continuous ideleWeight :=
  ENNReal.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm ℚ)

private theorem modulus_eq_ideleWeight (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    modulus g = ideleWeight (Matrix.GeneralLinearGroup.det g) := rfl

private def torusFine : Measure 𝔸ˣ :=
  (NumberField.Idele.idelicHaar ℚ).withDensity fun y => (ideleWeight y)⁻¹

private theorem isFiniteMeasureOnCompacts_torusFine : IsFiniteMeasureOnCompacts torusFine :=
  isFiniteMeasureOnCompacts_withDensity_inv (NumberField.Idele.idelicHaar ℚ) continuous_ideleWeight ideleWeight_ne_zero

private theorem torusFine_univ_ne_zero : torusFine Set.univ ≠ 0 := by
  unfold torusFine
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  intro h
  rw [lintegral_eq_zero_iff (continuous_ideleWeight.measurable.fun_inv)] at h
  have h2 : ∀ᵐ y ∂(NumberField.Idele.idelicHaar ℚ), False :=
    h.mono fun y hy => ENNReal.inv_ne_zero.2 (ideleWeight_ne_top y) (by simpa using hy)
  exact (NeZero.ne (NumberField.Idele.idelicHaar ℚ)) (by simpa using ae_iff.1 h2)

private theorem lintegral_mul_right_torusFine (y : 𝔸ˣ) {F : 𝔸ˣ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (x * y) ∂torusFine = ideleWeight y * ∫⁻ x, F x ∂torusFine := by
  have hinv : ∀ x, (ideleWeight x)⁻¹ ≠ 0 := fun x => ENNReal.inv_ne_zero.2 (ideleWeight_ne_top x)
  have hinvtop : ∀ x, (ideleWeight x)⁻¹ ≠ ⊤ := fun x => ENNReal.inv_ne_top.2 (ideleWeight_ne_zero x)
  have hmul : ∀ x x', (ideleWeight (x * x'))⁻¹ = (ideleWeight x)⁻¹ * (ideleWeight x')⁻¹ := fun x x' => by
    rw [ideleWeight_mul, ENNReal.mul_inv (Or.inl (ideleWeight_ne_zero x)) (Or.inl (ideleWeight_ne_top x))]
  have h := lintegral_mul_right_withDensity (NumberField.Idele.idelicHaar ℚ)
    (fun y' {F'} hF' => lintegral_mul_right_eq_self (μ := NumberField.Idele.idelicHaar ℚ) F' y')
    continuous_ideleWeight.measurable.inv hmul hinv hinvtop y hF
  simp only [Pi.inv_apply, inv_inv] at h
  exact h

end TorusMeasureFine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section TorusMeasure

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] secondCountableAdeles

private theorem comap_le_ideleBorel : (inferInstance : MeasurableSpace 𝔸ˣ) ≤ borel 𝔸ˣ := by
  letI : MeasurableSpace 𝔸ˣ := borel 𝔸ˣ
  haveI : BorelSpace 𝔸ˣ := ⟨rfl⟩
  exact (Units.continuous_val.measurable : Measurable (Units.val : 𝔸ˣ → 𝔸)).comap_le

private theorem measurableSet_of_isCompact_ideles {K : Set 𝔸ˣ} (hK : IsCompact K) : MeasurableSet K :=
  measurableSet_comap_of_isCompact Units.val_injective Units.continuous_val hK

private scoped instance secondCountable_ideles : SecondCountableTopology 𝔸ˣ :=
  haveI : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

private def torusMeasure : Measure 𝔸ˣ := torusFine.trim comap_le_ideleBorel

private theorem isFiniteMeasureOnCompacts_torusMeasure : IsFiniteMeasureOnCompacts torusMeasure :=
  isFiniteMeasureOnCompacts_trim torusFine comap_le_ideleBorel isFiniteMeasureOnCompacts_torusFine
    fun _ hK => measurableSet_of_isCompact_ideles hK

private theorem sigmaFinite_torusMeasure : SigmaFinite torusMeasure :=
  sigmaFinite_trim_of_isCompact torusFine comap_le_ideleBorel isFiniteMeasureOnCompacts_torusFine
    fun _ hK => measurableSet_of_isCompact_ideles hK

private theorem sFinite_torusMeasure : SFinite torusMeasure :=
  haveI := sigmaFinite_torusMeasure
  inferInstance

private theorem torusMeasure_univ_ne_zero : torusMeasure Set.univ ≠ 0 :=
  trim_univ_ne_zero torusFine comap_le_ideleBorel torusFine_univ_ne_zero

private theorem lintegral_mul_right_torusMeasure (y : 𝔸ˣ) {F : 𝔸ˣ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (x * y) ∂torusMeasure = ideleWeight y * ∫⁻ x, F x ∂torusMeasure := by
  haveI : MeasurableMul 𝔸ˣ := measurableMul_units
  exact lintegral_trim_transform torusFine comap_le_ideleBorel (σ := fun x => x * y)
    (fun {F'} hF' => lintegral_mul_right_torusFine y hF') hF (hF.comp (measurable_mul_const y))

end TorusMeasure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section FibreMeasure

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar secondCountableAdeles
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel secondCountableTopology_adelicGL3
attribute [local instance] sFinite_torusMeasure

private abbrev chartMeasure : Measure ChartCoords :=
  torusMeasure.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
    ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))

variable (P₂ : Subgroup ↥mirabolic) (hP₂ : ∀ p : ↥mirabolic, p ∈ P₂ ↔ leviRow p = e₂)

private def kernelEltIn (q : ChartCoords) : ↥P₂ := ⟨kernelElt q, (hP₂ _).2 (leviRow_kernelElt q)⟩

private theorem measurable_kernelEltIn : Measurable (kernelEltIn P₂ hP₂) :=
  measurable_kernelElt.subtype_mk

private theorem chart_kernelEltIn (q : ChartCoords) : mirabolicChart ((kernelEltIn P₂ hP₂ q : ↥P₂) : ↥mirabolic) = q :=
  mirabolicChart_kernelElt q

private theorem kernelEltIn_chart (p : ↥P₂) : kernelEltIn P₂ hP₂ (mirabolicChart (p : ↥mirabolic)) = p :=
  Subtype.ext (kernelElt_mirabolicChart ((hP₂ _).1 p.2))

private theorem kernelEltIn_mul (q q' : ChartCoords) :
    kernelEltIn P₂ hP₂ q * kernelEltIn P₂ hP₂ q' =
      kernelEltIn P₂ hP₂ (q.1 * q'.1, (q.2.1 + (q.1 : 𝔸) * q'.2.1,
        (q.2.2.1 + ((q.1 : 𝔸) * q'.2.2.1 + q.2.1 * q'.2.2.2), q.2.2.2 + q'.2.2.2))) :=
  Subtype.ext (kernelElt_mul q q')

private theorem measurable_chart_of_kernel : Measurable fun p : ↥P₂ => mirabolicChart (p : ↥mirabolic) :=
  measurable_mirabolicChart.comp measurable_subtype_coe

private def kernelMeasure : Measure ↥P₂ := Measure.map (kernelEltIn P₂ hP₂) chartMeasure

private theorem sFinite_kernelMeasure : SFinite (kernelMeasure P₂ hP₂) := by
  unfold kernelMeasure
  infer_instance

private theorem map_chart_kernelMeasure :
    Measure.map (fun p : ↥P₂ => mirabolicChart (p : ↥mirabolic)) (kernelMeasure P₂ hP₂) = chartMeasure := by
  unfold kernelMeasure
  rw [Measure.map_map (measurable_chart_of_kernel P₂) (measurable_kernelEltIn P₂ hP₂)]
  have h : (fun p : ↥P₂ => mirabolicChart (p : ↥mirabolic)) ∘ kernelEltIn P₂ hP₂ = id := by
    funext q
    exact chart_kernelEltIn P₂ hP₂ q
  rw [h, Measure.map_id]

private theorem lintegral_kernelMeasure {F : ↥P₂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂(kernelMeasure P₂ hP₂) = ∫⁻ q, F (kernelEltIn P₂ hP₂ q) ∂chartMeasure := by
  unfold kernelMeasure
  exact lintegral_map hF (measurable_kernelEltIn P₂ hP₂)

private theorem val_det_coe_kernelEltIn (q : ChartCoords) :
    Matrix.GeneralLinearGroup.det ((kernelEltIn P₂ hP₂ q : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) = q.1 :=
  congrArg Prod.fst (chart_kernelEltIn P₂ hP₂ q)

private theorem lintegral_mul_right_kernelMeasure (p₁ : ↥P₂) {F : ↥P₂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (p * p₁) ∂(kernelMeasure P₂ hP₂) =
      modulus ((p₁ : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * ∫⁻ p, F p ∂(kernelMeasure P₂ hP₂) := by
  haveI : MeasurableMul 𝔸ˣ := measurableMul_units
  set q₁ : ChartCoords := mirabolicChart (p₁ : ↥mirabolic) with hq₁
  have hp₁ : p₁ = kernelEltIn P₂ hP₂ q₁ := (kernelEltIn_chart P₂ hP₂ p₁).symm
  have hFmul : Measurable fun p => F (p * p₁) := hF.comp (measurable_mul_const p₁)
  rw [lintegral_kernelMeasure P₂ hP₂ hFmul, lintegral_kernelMeasure P₂ hP₂ hF]
  have hΦ : Measurable fun q : ChartCoords => F (kernelEltIn P₂ hP₂ q) := hF.comp (measurable_kernelEltIn P₂ hP₂)
  have hshift : ∀ q : ChartCoords, F (kernelEltIn P₂ hP₂ q * p₁) =
      (fun q : ChartCoords => F (kernelEltIn P₂ hP₂ q))
        (q.1 * q₁.1, (q.2.1 + (q.1 : 𝔸) * q₁.2.1,
          (q.2.2.1 + ((q.1 : 𝔸) * q₁.2.2.1 + q.2.1 * q₁.2.2.2), q.2.2.2 + q₁.2.2.2))) := by
    intro q
    simp only
    rw [hp₁, kernelEltIn_mul]
  simp_rw [hshift]
  have hmod : modulus ((p₁ : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) = ideleWeight q₁.1 := by
    rw [modulus_eq_ideleWeight, hq₁]
    rfl
  rw [hmod]
  have hf₁ : Measurable fun u : 𝔸ˣ => (u : 𝔸) * q₁.2.1 := measurable_units_val.mul_const _
  have hf₂ : Measurable fun v : 𝔸ˣ × 𝔸 => (v.1 : 𝔸) * q₁.2.2.1 + v.2 * q₁.2.2.2 :=
    ((measurable_units_val.comp measurable_fst).mul_const _).add (measurable_snd.mul_const _)
  exact lintegral_triangular_shift torusMeasure (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
    (measurable_mul_const q₁.1) (fun {G} hG => lintegral_mul_right_torusMeasure q₁.1 hG) hf₁ hf₂ q₁.2.2.2 hΦ

private theorem kernelMeasure_univ_ne_zero : kernelMeasure P₂ hP₂ Set.univ ≠ 0 := by
  unfold kernelMeasure
  rw [Measure.map_apply (measurable_kernelEltIn P₂ hP₂) MeasurableSet.univ, Set.preimage_univ]
  have hH : NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ Set.univ ≠ 0 := NeZero.ne _
  unfold chartMeasure
  rw [← Set.univ_prod_univ (α := 𝔸ˣ) (β := 𝔸 × (𝔸 × 𝔸)), Measure.prod_prod,
    ← Set.univ_prod_univ (α := 𝔸) (β := 𝔸 × 𝔸), Measure.prod_prod, ← Set.univ_prod_univ (α := 𝔸) (β := 𝔸),
    Measure.prod_prod]
  exact mul_ne_zero torusMeasure_univ_ne_zero (mul_ne_zero hH (mul_ne_zero hH hH))

private theorem kernelMeasure_ne_top_of_isCompact {C : Set ↥P₂} (hC : IsCompact C) :
    kernelMeasure P₂ hP₂ C ≠ ⊤ := by
  haveI := isFiniteMeasureOnCompacts_torusMeasure
  have hchart : Continuous fun p : ↥P₂ => mirabolicChart (p : ↥mirabolic) := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_))
    · exact Matrix.GeneralLinearGroup.continuous_det.comp (continuous_subtype_val.comp continuous_subtype_val)
    all_goals
      exact ((continuous_apply _).comp ((continuous_apply _).comp continuous_coe_matrix)).comp
        (continuous_subtype_val.comp continuous_subtype_val)
  have himage : IsCompact ((fun p : ↥P₂ => mirabolicChart (p : ↥mirabolic)) '' C) := hC.image hchart
  have hsub : kernelEltIn P₂ hP₂ ⁻¹' C ⊆ (fun p : ↥P₂ => mirabolicChart (p : ↥mirabolic)) '' C := by
    intro q hq
    exact ⟨kernelEltIn P₂ hP₂ q, hq, chart_kernelEltIn P₂ hP₂ q⟩
  have hmeasC : MeasurableSet C := by
    have : IsClosed C := hC.isClosed
    exact this.measurableSet
  unfold kernelMeasure
  rw [Measure.map_apply (measurable_kernelEltIn P₂ hP₂) hmeasC]
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  exact himage.measure_lt_top.ne

end FibreMeasure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section LeviRowShift

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar secondCountableAdeles

private theorem vecMul_castSucc (x : Fin 3 → 𝔸) (h : ↥mirabolic) (j : Fin 2) :
    (x ᵥ* ((h : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸)) (Fin.castSucc j) =
      leviAct (fun i => x (Fin.castSucc i)) h j := by
  simp only [Matrix.vecMul, dotProduct, leviAct, Fin.sum_univ_three, Fin.sum_univ_two]
  have h2 := matrix_two_of_mem h (Fin.castSucc j)
  have hj : (Fin.castSucc j : Fin 3) ≠ 2 := by
    fin_cases j <;> decide
  rw [if_neg hj] at h2
  simp only [h2, mul_zero, add_zero]
  rfl

private theorem vecMul_last (x : Fin 3 → 𝔸) (h : ↥mirabolic) :
    (x ᵥ* ((h : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸)) (Fin.last 2) =
      x (Fin.last 2) + (x 0 * ((h : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 0 2 +
        x 1 * ((h : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) 1 2) := by
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  have h2 := matrix_two_of_mem h 2
  rw [if_pos rfl] at h2
  have hlast : (Fin.last 2 : Fin 3) = 2 := rfl
  rw [hlast, h2, mul_one]
  ring

private theorem measurable_leviAct (h : ↥mirabolic) : Measurable fun r : Fin 2 → 𝔸 => leviAct r h := by
  refine measurable_pi_lambda _ fun j => ?_
  simp only [leviAct]
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul_const _

private theorem lintegral_leviAct_leviHaar (h : ↥mirabolic) {Ψ : (Fin 2 → 𝔸) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ r, Ψ (leviAct r h) ∂leviHaar = (modulus (h : AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ * ∫⁻ r, Ψ r ∂leviHaar := by

  obtain ⟨B, hBc, hB0⟩ := exists_compact_mem_nhds (0 : 𝔸)
  have hBmeas : MeasurableSet B := hBc.isClosed.measurableSet
  have hBpos : NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ B ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) hB0).ne'
  have hBtop : NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ B ≠ ⊤ := hBc.measure_lt_top.ne
  set H := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ with hH
  set M : Matrix (Fin 3) (Fin 3) 𝔸 := ((h : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) with hM

  set φ : (Fin 3 → 𝔸) → ℝ≥0∞ := fun x => Ψ (fun i => x (Fin.castSucc i)) * B.indicator 1 (x (Fin.last 2) + 0)
    with hφ
  have hφm : Measurable φ := by
    refine Measurable.mul (hΨ.comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)) ?_
    exact (measurable_indicator_const_iff (1 : ℝ≥0∞)).2 hBmeas |>.comp ((measurable_pi_apply _).add_const 0)
  have hsplit₀ : ∫⁻ x, φ x ∂rowHaar = (∫⁻ r, Ψ r ∂leviHaar) * H B := by
    simpa [φ] using lintegral_pi_three_split H hΨ (s := fun _ => 0) measurable_const hBmeas

  set s : (Fin 2 → 𝔸) → 𝔸 := fun r => r 0 * M 0 2 + r 1 * M 1 2 with hs
  have hsm : Measurable s := ((measurable_pi_apply 0).mul_const _).add ((measurable_pi_apply 1).mul_const _)
  have hshift : ∀ x : Fin 3 → 𝔸, φ (x ᵥ* M) =
      Ψ (leviAct (fun i => x (Fin.castSucc i)) h) *
        B.indicator 1 (x (Fin.last 2) + s (fun i => x (Fin.castSucc i))) := by
    intro x
    simp only [φ]
    rw [vecMul_last, add_zero]
    congr 1
    congr 1
    funext j
    exact vecMul_castSucc x h j
  have hsplit₁ : ∫⁻ x, φ (x ᵥ* M) ∂rowHaar = (∫⁻ r, Ψ (leviAct r h) ∂leviHaar) * H B := by
    simp_rw [hshift]
    exact lintegral_pi_three_split H (hΨ.comp (measurable_leviAct h)) hsm hBmeas
  have hrow := lintegral_vecMul_rowHaar (h : AdelicGL 3 (𝓞 ℚ) ℚ) φ hφm
  rw [← hM, hsplit₁, hsplit₀] at hrow
  change (∫⁻ r, Ψ (leviAct r h) ∂leviHaar) * H B = (modulus (h : AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ *
    ((∫⁻ r, Ψ r ∂leviHaar) * H B) at hrow
  rw [← mul_assoc] at hrow
  exact (ENNReal.mul_left_inj hBpos hBtop).1 hrow

end LeviRowShift
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section IdentityAssembly

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar secondCountableAdeles
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel secondCountableTopology_adelicGL3

private scoped instance secondCountableTopology_mirabolic : SecondCountableTopology ↥mirabolic :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

private scoped instance borelSpace_mirabolic : BorelSpace ↥mirabolic := inferInstance

private scoped instance measurableMul₂_mirabolic : MeasurableMul₂ ↥mirabolic := inferInstance

variable (P₂ : Subgroup ↥mirabolic) (hP₂ : ∀ p : ↥mirabolic, p ∈ P₂ ↔ leviRow p = e₂)

include hP₂ in
private theorem mul_inv_mem_of_leviRow_eq
    (hact : ∀ q p : ↥mirabolic, leviRow (q * p) = leviAct (leviRow q) p) (a b : ↥mirabolic)
    (hab : leviRow a = leviRow b) : a * b⁻¹ ∈ P₂ := by
  rw [hP₂, hact, hab, ← hact, mul_inv_cancel, leviRow_one]

include hP₂ in
private theorem leviRow_mul_left_of_mem (hact : ∀ q p : ↥mirabolic, leviRow (q * p) = leviAct (leviRow q) p)
    (p : ↥P₂) (g : ↥mirabolic) : leviRow ((p : ↥mirabolic) * g) = leviRow g := by
  have hp : leviRow (p : ↥mirabolic) = e₂ := (hP₂ _).1 p.2
  have hg : g = (1 : ↥mirabolic) * g := (one_mul g).symm
  rw [hact, hp]
  conv_rhs => rw [hg, hact, leviRow_one]

private theorem continuous_leviRow : Continuous leviRow := by
  refine continuous_pi fun i => ?_
  exact ((continuous_apply _).comp ((continuous_apply _).comp continuous_coe_matrix)).comp continuous_subtype_val

include hP₂ in
private theorem isClosed_kernel : IsClosed ((P₂ : Set ↥mirabolic)) := by
  have h : (P₂ : Set ↥mirabolic) = leviRow ⁻¹' {e₂} := by
    ext p
    simpa using hP₂ p
  rw [h]
  exact isClosed_singleton.preimage continuous_leviRow

include hP₂ in
private theorem isCompact_preimage_kernel {L : Set ↥mirabolic} (hL : IsCompact L) :
    IsCompact ((fun p : ↥P₂ => (p : ↥mirabolic)) ⁻¹' L) :=
  (isClosed_kernel P₂ hP₂).isClosedEmbedding_subtypeVal.isCompact_preimage hL

private theorem isCompact_mul_inv_mirabolic {K : Set ↥mirabolic} (hK : IsCompact K) :
    IsCompact ((fun z : ↥mirabolic × ↥mirabolic => z.1 * z.2⁻¹) '' (K ×ˢ K)) :=
  (hK.prod hK).image (continuous_fst.mul continuous_snd.inv)

private abbrev leviFibration (sec : (Fin 2 → 𝔸) → ↥mirabolic) (R : Set (Fin 2 → 𝔸)) : Measure ↥mirabolic :=
  fibMeasure P₂ sec (fun p => modulus (p : AdelicGL 3 (𝓞 ℚ) ℚ)) (kernelMeasure P₂ hP₂) leviHaar R

private theorem measurable_fibreModulus' : Measurable fun p : ↥mirabolic => modulus (p : AdelicGL 3 (𝓞 ℚ) ℚ) :=
  measurable_modulus.comp measurable_subtype_coe

private theorem modulus_coe_mul (g h : ↥mirabolic) :
    modulus ((g * h : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) =
      modulus (g : AdelicGL 3 (𝓞 ℚ) ℚ) * modulus (h : AdelicGL 3 (𝓞 ℚ) ℚ) :=
  modulus_mul _ _

private theorem modulus_coe_inv (g : ↥mirabolic) :
    modulus ((g⁻¹ : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) = (modulus (g : AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ :=
  modulus_inv _

private theorem isMulRightInvariant_leviFibration {sec : (Fin 2 → 𝔸) → ↥mirabolic} (hsec : Measurable sec)
    {R : Set (Fin 2 → 𝔸)} (hR : MeasurableSet R)
    (hact : ∀ q p : ↥mirabolic, leviRow (q * p) = leviAct (leviRow q) p)
    (hsecR : ∀ r ∈ R, leviRow (sec r) = r) (hRact : ∀ r, ∀ p : ↥mirabolic, leviAct r p ∈ R ↔ r ∈ R) :
    (leviFibration P₂ hP₂ sec R).IsMulRightInvariant :=
  haveI := sFinite_kernelMeasure P₂ hP₂
  isMulRightInvariant_fibMeasure P₂ leviRow leviAct hsec measurable_fibreModulus' (kernelMeasure P₂ hP₂) leviHaar hR
    hact (mul_inv_mem_of_leviRow_eq P₂ hP₂ hact) hsecR hRact modulus_coe_mul modulus_coe_inv
    (fun _ => modulus_ne_zero _) (fun _ => modulus_ne_top _)
    (fun p₁ _ hF => lintegral_mul_right_kernelMeasure P₂ hP₂ p₁ hF)
    (fun h _ hΨ => lintegral_leviAct_leviHaar h hΨ)

private theorem isFiniteMeasureOnCompacts_leviFibration {sec : (Fin 2 → 𝔸) → ↥mirabolic} (hsec : Measurable sec)
    {R : Set (Fin 2 → 𝔸)} (hR : MeasurableSet R)
    (hact : ∀ q p : ↥mirabolic, leviRow (q * p) = leviAct (leviRow q) p)
    (hsecR : ∀ r ∈ R, leviRow (sec r) = r) :
    IsFiniteMeasureOnCompacts (leviFibration P₂ hP₂ sec R) := by
  haveI := sFinite_kernelMeasure P₂ hP₂
  haveI : IsFiniteMeasureOnCompacts (leviHaar : Measure (Fin 2 → 𝔸)) := inferInstance
  refine ⟨fun {K} hK => lt_top_iff_ne_top.2 ?_⟩
  obtain ⟨m, hm0, hmK⟩ := exists_ne_zero_le_on_of_isCompact continuous_fibreModulus
    (fun p => modulus_ne_zero ((p : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)) hK
  have hT : IsCompact (leviRow '' K) := hK.image continuous_leviRow
  have hC : IsCompact ((fun p : ↥P₂ => (p : ↥mirabolic)) ⁻¹'
      ((fun z : ↥mirabolic × ↥mirabolic => z.1 * z.2⁻¹) '' (K ×ˢ K))) :=
    isCompact_preimage_kernel P₂ hP₂ (isCompact_mul_inv_mirabolic hK)
  refine fibMeasure_ne_top P₂ leviRow hsec measurable_fibreModulus' (kernelMeasure P₂ hP₂) leviHaar hR
    (leviRow_mul_left_of_mem P₂ hP₂ hact) (mul_inv_mem_of_leviRow_eq P₂ hP₂ hact) hsecR modulus_coe_mul modulus_coe_inv
    (fun g => modulus_ne_zero _) (fun g => modulus_ne_top _)
    (fun p₁ F hF => lintegral_mul_right_kernelMeasure P₂ hP₂ p₁ hF) hK.isClosed.measurableSet
    hT.isClosed.measurableSet hT.measure_lt_top.ne (fun k hk => Set.mem_image_of_mem _ hk)
    hC.isClosed.measurableSet (kernelMeasure_ne_top_of_isCompact P₂ hP₂ hC) ?_ hm0 hmK
  intro k₁ hk₁ k₂ hk₂ q hq
  exact ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, hq.symm⟩

private theorem leviFibration_ne_zero {sec : (Fin 2 → 𝔸) → ↥mirabolic} (hsec : Measurable sec)
    {R : Set (Fin 2 → 𝔸)} (hR : MeasurableSet R) (hRpos : leviHaar R ≠ 0) :
    leviFibration P₂ hP₂ sec R ≠ 0 := by
  haveI := sFinite_kernelMeasure P₂ hP₂
  intro h0
  have h1 : ∫⁻ _ : ↥mirabolic, (1 : ℝ≥0∞) ∂(leviFibration P₂ hP₂ sec R) = 0 := by
    rw [h0, lintegral_zero_measure]
  rw [lintegral_fibMeasure P₂ hsec measurable_fibreModulus' _ leviHaar R measurable_const] at h1
  simp only [lintegral_const, one_mul] at h1
  have hm : Measurable fun r : Fin 2 → 𝔸 =>
      (modulus ((sec r : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ * kernelMeasure P₂ hP₂ Set.univ :=
    (measurable_fibreModulus'.comp hsec).inv.mul_const _
  have h2 := (ae_restrict_iff' hR).1 ((lintegral_eq_zero_iff hm).1 h1)
  have hall : ∀ r, (modulus ((sec r : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ * kernelMeasure P₂ hP₂ Set.univ ≠ 0 :=
    fun r => mul_ne_zero (ENNReal.inv_ne_zero.2 (modulus_ne_top _)) (kernelMeasure_univ_ne_zero P₂ hP₂)
  have h3 := ae_iff.1 h2
  have hnull : leviHaar R = 0 := by
    refine measure_mono_null (fun r hrR => ?_) h3
    intro himp
    exact hall r (by simpa using himp hrR)
  exact hRpos hnull

end IdentityAssembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section LeviFibration

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private theorem exists_levi_fibration (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (μP : Measure ↥mirabolic)
    [μP.IsMulRightInvariant] [μP.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μP] :
    ∃ (P₂ : Subgroup ↥mirabolic) (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic)
      (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) (μ₂ : Measure ↥P₂) (c : ℝ≥0∞),
      (c ≠ 0 ∧ c ≠ ⊤ ∧
        μP = c • fibMeasure P₂ sec (fun p => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))
          μ₂ leviHaar R) ∧
      (∀ p : ↥mirabolic, p ∈ P₂ ↔ leviRow p = e₂) ∧
      Measurable sec ∧
      (∀ r ∈ R, leviRow (sec r) = r) ∧
      (∀ p : ↥mirabolic, OnShell S p → leviRow p ∈ goodLeviRows S) ∧
      goodLeviRows S ⊆ R ∧
      (∃ (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) (w : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ≥0∞), SFinite ρ ∧
        (∀ y, w y ≠ 0 ∧ w y ≠ ⊤) ∧
        (∀ y, ∀ F : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ≥0∞, Measurable F →
          ∫⁻ x, F (x * y) ∂ρ = w y * ∫⁻ x, F x ∂ρ) ∧
        Measure.map (fun p : ↥P₂ => mirabolicChart (p : ↥mirabolic)) μ₂ =
          ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
            ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) ∧
        (∃ ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂,
          Measurable ι ∧
          μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
            ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))) ∧
          (∀ v, mirabolicChart (ι v : ↥mirabolic) = v) ∧
          (∀ v, (((ι v : ↥mirabolic) : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) :
              Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
            !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1]))) ∧
      SFinite μ₂ ∧
      (∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
        componentAt3 (𝓞 ℚ) ℚ q (sec r : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) ∈
          localMaximalCompact3 (𝓞 ℚ) ℚ q) ∧
      MeasurableSet (goodLeviRows S) := by
  obtain ⟨P₂, sec, R, hP₂, hsec, hsecR, hR, hRact, hact, hgood, hshell, hK, hgoodMeas⟩ := exists_levi_section S
  haveI := sFinite_kernelMeasure P₂ hP₂
  haveI := isMulRightInvariant_leviFibration P₂ hP₂ hsec hR hact hsecR hRact
  haveI := isFiniteMeasureOnCompacts_leviFibration P₂ hP₂ hsec hR hact hsecR
  have hRpos : leviHaar R ≠ 0 := ((leviHaar_goodLeviRows_pos S).trans_le (measure_mono hgood)).ne'
  obtain ⟨c, hc0, hctop, hμP⟩ := exists_ne_zero_and_eq_smul_of_isMulRightInvariant_of_ne_zero
    (leviFibration P₂ hP₂ sec R) μP (leviFibration_ne_zero P₂ hP₂ hsec hR hRpos)
  refine ⟨P₂, sec, R, kernelMeasure P₂ hP₂, c, ⟨hc0, hctop, hμP⟩, hP₂, hsec, hsecR, hshell, hgood,
    ⟨torusMeasure, ideleWeight, sFinite_torusMeasure, fun y => ⟨ideleWeight_ne_zero y, ideleWeight_ne_top y⟩,
      fun y F hF => lintegral_mul_right_torusMeasure y hF, map_chart_kernelMeasure P₂ hP₂,
      kernelEltIn P₂ hP₂, measurable_kernelEltIn P₂ hP₂, rfl, fun v => mirabolicChart_kernelElt v, fun v => ?_⟩,
    sFinite_kernelMeasure P₂ hP₂, hK, hgoodMeas⟩
  simp only [kernelEltIn, kernelElt, kernelUnit, coe_glOf, kernelMatrix]

end LeviFibration
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end MirabolicLeviFibration
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end FibrationIdentity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section IdeleInverses

noncomputable section

namespace MirabolicLeviFibration

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end RowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section SectionAndRowSets

section SectionHeads

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

open scoped RestrictedProduct

open Topology

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

end SectionHeads
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end SectionAndRowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UniquenessPrinciple

section UniquenessHead

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open Filter Topology Set

open scoped NNReal Classical

attribute [local instance] archBorel

attribute [local instance] archBorelSpace

attribute [local instance] localBorel

attribute [local instance] localBorelSpace

attribute [local instance] countable_primes

attribute [local instance] properCompletion archSecondCountable

attribute [local instance] secondCountableAdeles NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

attribute [local instance] borelRows

attribute [local instance] haarRows

attribute [local instance] localSecondCountable

attribute [local instance] archRowsSecondCountable localRowsSecondCountable

attribute [local instance] secondCountableCoords

attribute [local instance] archRowsBorel localRowsBorel

attribute [local instance] borelCoords

attribute [local instance] locallyCompactCoords

attribute [local instance] sigmaCompactCoords

attribute [local instance] coordsHaar_isAddHaarMeasure

attribute [local instance] sigmaFinite_coordsHaar

end UniquenessHead
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end UniquenessPrinciple
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

open Topology

section KernelMatrix

variable {A : Type} [CommRing A]

end KernelMatrix
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section KernelMatrixContinuity

variable {A : Type} [CommRing A] [TopologicalSpace A] {X : Type} [TopologicalSpace X]

end KernelMatrixContinuity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UnitsMeasurability

variable {R : Type} [Monoid R] [MeasurableSpace R]

end UnitsMeasurability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UnitsBorelTopology

variable {R : Type} [Monoid R] [TopologicalSpace R]

end UnitsBorelTopology
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UnitsBorel

variable {R : Type} [Monoid R] [TopologicalSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]

end UnitsBorel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section MatrixBorel

variable {A : Type} [TopologicalSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

end MatrixBorel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section MatrixUnitsBorel

variable {A : Type} [CommRing A] [TopologicalSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

end MatrixUnitsBorel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section IdeleInversion

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

open Filter Topology Set
open scoped RestrictedProduct NNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] archBorel archBorelSpace localBorel localBorelSpace countable_primes
attribute [local instance] properCompletion archSecondCountable localSecondCountable secondCountableAdeles

end IdeleInversion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end MirabolicLeviFibration
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end IdeleInverses
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section CoefficientEngine

noncomputable section

namespace MirabolicLeviFibration

section Parameters

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private def ZeroOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (t : AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S → evalHom q t = 0

private def IntegralOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (u : AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S → evalHom q u ∈ q.adicCompletionIntegers ℚ) ∧
    (∀ q ∈ S, evalHom q u = 0) ∧ AdelicLevel.adeleArch (𝓞 ℚ) ℚ u = 0

private def IntegralOutsideAll (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (s : AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S → evalHom q s ∈ q.adicCompletionIntegers ℚ

private def UnitOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : Prop :=
  ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S → Valued.v (evalHom q (y : AdeleRing (𝓞 ℚ) ℚ)) = 1

private def UnitOutsideTrivialInside (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : Prop :=
  UnitOutside S u ∧ (∀ q ∈ S, evalHom q (u : AdeleRing (𝓞 ℚ) ℚ) = 1) ∧
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ (u : AdeleRing (𝓞 ℚ) ℚ) = 1

end Parameters
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Representative

open scoped Classical

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem continuous_evalHom (q : HeightOneSpectrum (𝓞 ℚ)) : Continuous (evalHom q) :=
  (AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ q).comp continuous_snd

private def tailAdele (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : AdeleRing (𝓞 ℚ) ℚ :=
  ((0 : InfiniteAdeleRing ℚ), 1 - ∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 1)

private theorem evalHom_tailAdele (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : HeightOneSpectrum (𝓞 ℚ)) :
    evalHom p (tailAdele S) = if p ∈ S then 0 else 1 := by
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p (1 - ∑ q ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ q.1 1) = _
  rw [map_sub, map_one, map_sum]
  simp only [AdelicLevel.finAdeleEval_apply]
  split_ifs with hp
  · rw [Finset.sum_eq_single (⟨p, hp⟩ : {p // p ∈ S})]
    · exact sub_eq_zero.2 (StandardAddChar.finAdeleSingleAt_apply_self ℚ p 1).symm
    · intro q _ hq
      exact StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hq (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_attach _ _) h
  · rw [Finset.sum_eq_zero fun q _ =>
      StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hp (by rw [h]; exact q.2), sub_zero]

private def headAdele (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : AdeleRing (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ :=
  (AdelicLevel.adeleArch (𝓞 ℚ) ℚ x, ∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (evalHom p.1 x))

private theorem adeleArch_headAdele (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : AdeleRing (𝓞 ℚ) ℚ) :
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ (headAdele S x) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ x :=
  rfl

private theorem evalHom_headAdele_of_mem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : AdeleRing (𝓞 ℚ) ℚ)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ S) : evalHom p (headAdele S x) = evalHom p x := by
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p
    (∑ q ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ q.1 (evalHom q.1 x)) = evalHom p x
  rw [map_sum]
  simp only [AdelicLevel.finAdeleEval_apply]
  rw [Finset.sum_eq_single (⟨p, hp⟩ : {p // p ∈ S})]
  · exact StandardAddChar.finAdeleSingleAt_apply_self ℚ p _
  · intro q _ hq
    exact StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hq (Subtype.ext h.symm)
  · intro h
    exact absurd (Finset.mem_attach _ _) h

private theorem evalHom_headAdele_of_notMem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : AdeleRing (𝓞 ℚ) ℚ)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S) : evalHom p (headAdele S x) = 0 := by
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p
    (∑ q ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ q.1 (evalHom q.1 x)) = 0
  rw [map_sum]
  simp only [AdelicLevel.finAdeleEval_apply]
  exact Finset.sum_eq_zero fun q _ =>
    StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hp (by rw [h]; exact q.2)

private theorem headAdele_add_of_integralOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x u : AdeleRing (𝓞 ℚ) ℚ)
    (hu : IntegralOutside S u) : headAdele S (x + u) = headAdele S x := by
  unfold headAdele
  refine Prod.ext ?_ ?_
  · show AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x + u) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ x
    rw [map_add, hu.2.2, add_zero]
  · show (∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (evalHom p.1 (x + u))) =
      ∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (evalHom p.1 x)
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_add, hu.2.1 p.1 p.2, add_zero]

private theorem continuous_headAdele (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Continuous (headAdele S) := by
  unfold headAdele
  refine Continuous.prodMk (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ) ?_
  exact continuous_finsetSum _ fun p _ =>
    (StandardAddChar.continuous_finAdeleSingleAt ℚ p.1).comp (continuous_evalHom p.1)

private def adeleRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : AdeleRing (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ :=
  headAdele S x + tailAdele S

private theorem evalHom_adeleRep_of_notMem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : AdeleRing (𝓞 ℚ) ℚ)
    {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ∉ S) : evalHom q (adeleRep S x) = 1 := by
  unfold adeleRep
  rw [map_add, evalHom_headAdele_of_notMem S x hq, evalHom_tailAdele, if_neg hq, zero_add]

private theorem evalHom_adeleRep_of_mem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : AdeleRing (𝓞 ℚ) ℚ)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ S) : evalHom p (adeleRep S x) = evalHom p x := by
  unfold adeleRep
  rw [map_add, evalHom_headAdele_of_mem S x hp, evalHom_tailAdele, if_pos hp, add_zero]

private theorem adeleArch_adeleRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : AdeleRing (𝓞 ℚ) ℚ) :
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ (adeleRep S x) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ x := by
  have h : AdelicLevel.adeleArch (𝓞 ℚ) ℚ (tailAdele S) = 0 := rfl
  unfold adeleRep
  rw [map_add, adeleArch_headAdele, h, add_zero]

private theorem adeleRep_add_of_integralOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x u : AdeleRing (𝓞 ℚ) ℚ)
    (hu : IntegralOutside S u) : adeleRep S (x + u) = adeleRep S x := by
  unfold adeleRep
  rw [headAdele_add_of_integralOutside S x u hu]

private theorem continuous_adeleRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Continuous (adeleRep S) :=
  (continuous_headAdele S).add continuous_const

private theorem measurable_adeleRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Measurable (adeleRep S) :=
  (continuous_adeleRep S).measurable

private theorem integralOutside_sub_adeleRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : AdeleRing (𝓞 ℚ) ℚ)
    (hx : IntegralOutsideAll S x) : IntegralOutside S (x - adeleRep S x) := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, ?_⟩
  · rw [map_sub, evalHom_adeleRep_of_notMem S x hq]
    exact sub_mem (hx q hq) (one_mem _)
  · rw [map_sub, evalHom_adeleRep_of_mem S x hq, sub_self]
  · rw [map_sub, adeleArch_adeleRep, sub_self]

end Representative
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end RowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section ShellCondition

section Shell

end Shell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end ShellCondition
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UniquenessPrinciple

section UniquenessHead

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open Filter Topology Set

open scoped NNReal Classical

private theorem exists_smooth_approx {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ g : ℕ → E → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      (∀ n t, 0 ≤ g n t) ∧ (∀ n t, g n t ≤ 1) ∧ (∀ n t, t ∉ U → g n t = 0) ∧
      ∀ t, Tendsto (fun n => g n t) atTop (𝓝 (U.indicator (fun _ => (1 : ℝ)) t)) := by
  obtain ⟨f, hf_supp, hf_smooth, hf_range⟩ := hU.exists_contDiff_support_eq (n := ⊤)
  have hK : IsCompact (closure U) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hUb.closure
  have hf_zero : ∀ t, t ∉ U → f t = 0 := by
    intro t ht
    by_contra h
    have hmem : t ∈ Function.support f := Function.mem_support.mpr h
    rw [hf_supp] at hmem
    exact ht hmem
  have hf_nonneg : ∀ t, 0 ≤ f t := fun t => (hf_range ⟨t, rfl⟩).1
  refine ⟨fun n t => Real.smoothTransition ((n : ℝ) * f t), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact Real.smoothTransition.contDiff.comp (contDiff_const.mul hf_smooth)
  · intro n
    refine HasCompactSupport.intro hK fun t ht => ?_
    have ht' : t ∉ U := fun h => ht (subset_closure h)
    simp only [hf_zero t ht', mul_zero, Real.smoothTransition.zero]
  · intro n t
    exact Real.smoothTransition.nonneg _
  · intro n t
    exact Real.smoothTransition.le_one _
  · intro n t ht
    simp only [hf_zero t ht, mul_zero, Real.smoothTransition.zero]
  · intro t
    by_cases ht : t ∈ U
    · have hmem : t ∈ Function.support f := by
        rw [hf_supp]
        exact ht
      have hpos : 0 < f t := lt_of_le_of_ne (hf_nonneg t) (Function.mem_support.mp hmem).symm
      rw [indicator_of_mem ht]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈(f t)⁻¹⌉₊] with n hn
      refine (Real.smoothTransition.one_of_one_le ?_).symm
      have h1 : (f t)⁻¹ ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
      calc (1 : ℝ) = (f t)⁻¹ * f t := (inv_mul_cancel₀ hpos.ne').symm
        _ ≤ (n : ℝ) * f t := mul_le_mul_of_nonneg_right h1 hpos.le
    · rw [indicator_of_notMem ht]
      simp only [hf_zero t ht, mul_zero, Real.smoothTransition.zero]
      exact tendsto_const_nhds

private theorem exists_smooth_dominant {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set E} (hUb : Bornology.IsBounded U) :
    ∃ G : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ HasCompactSupport G ∧ (∀ t, 0 ≤ G t) ∧ (∀ t, G t ≤ 1) ∧
      ∀ t ∈ U, G t = 1 := by
  obtain ⟨r, hr⟩ := hUb.subset_closedBall (0 : E)
  let b : ContDiffBump (0 : E) :=
    { rIn := max r 1
      rOut := max r 1 + 1
      rIn_pos := lt_of_lt_of_le one_pos (le_max_right r 1)
      rIn_lt_rOut := lt_add_one _ }
  refine ⟨b, b.contDiff, b.hasCompactSupport, fun t => b.nonneg, fun t => b.le_one, fun t ht => ?_⟩
  exact b.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (le_max_left r 1) (hr ht))

private def smoothFamily {A E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : A → E) :
    Set (A → ℝ≥0) :=
  {φ | ∃ g : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ (∀ t, 0 ≤ g t) ∧ (∀ t, g t ≤ 1) ∧
    φ = fun a => Real.toNNReal (g (r a))}

private theorem smoothFamily_approx {A E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (r : A → E) {c : Set A}
    (hc : c ∈ Set.preimage r '' {U : Set E | IsOpen U ∧ Bornology.IsBounded U}) :
    ∃ Φ ∈ smoothFamily r, ∃ φ : ℕ → A → ℝ≥0, (∀ n, φ n ∈ smoothFamily r) ∧
      (∀ n a, φ n a ≤ Φ a) ∧
      ∀ a, Tendsto (fun n => φ n a) atTop (𝓝 (c.indicator (fun _ => (1 : ℝ≥0)) a)) := by
  obtain ⟨U, ⟨hU, hUb⟩, rfl⟩ := hc
  obtain ⟨G, hG_smooth, hG_supp, hG_nonneg, hG_le, hG_one⟩ := exists_smooth_dominant hUb
  obtain ⟨g, hg_smooth, hg_supp, hg_nonneg, hg_le, hg_zero, hg_lim⟩ := exists_smooth_approx hU hUb
  refine ⟨fun a => Real.toNNReal (G (r a)), ⟨G, hG_smooth, hG_supp, hG_nonneg, hG_le, rfl⟩,
    fun n a => Real.toNNReal (g n (r a)),
    fun n => ⟨g n, hg_smooth n, hg_supp n, hg_nonneg n, hg_le n, rfl⟩, ?_, ?_⟩
  · intro n a
    apply Real.toNNReal_le_toNNReal
    by_cases ha : r a ∈ U
    · rw [hG_one _ ha]
      exact hg_le n _
    · rw [hg_zero n _ ha]
      exact hG_nonneg _
  · intro a
    have h := (continuous_real_toNNReal.tendsto _).comp (hg_lim (r a))
    have heq : Real.toNNReal (U.indicator (fun _ => (1 : ℝ)) (r a)) =
        (r ⁻¹' U).indicator (fun _ => (1 : ℝ≥0)) a := by
      by_cases ha : r a ∈ U
      · have ha' : a ∈ r ⁻¹' U := ha
        simp only [indicator_of_mem ha, indicator_of_mem ha', Real.toNNReal_one]
      · have ha' : a ∉ r ⁻¹' U := ha
        simp only [indicator_of_notMem ha, indicator_of_notMem ha', Real.toNNReal_zero]
    rw [← heq]
    exact h

private theorem isTopologicalBasis_compactOpen {X : Type} [TopologicalSpace X]
    (hnhds : ∀ x : X, ∀ U ∈ 𝓝 x, ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U)
    (hcpt : ∀ x : X, ∃ W : Set X, IsCompact W ∧ IsOpen W ∧ x ∈ W) :
    TopologicalSpace.IsTopologicalBasis {V : Set X | IsCompact V ∧ IsOpen V} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun V hV => hV.2) ?_
  intro x U hxU hU
  obtain ⟨W, hWc, hWo, hxW⟩ := hcpt x
  obtain ⟨V, hV, hxV, hVU⟩ := hnhds x (U ∩ W) ((hU.inter hWo).mem_nhds ⟨hxU, hxW⟩)
  refine ⟨V, ⟨?_, hV.isOpen⟩, hxV, fun y hy => (hVU hy).1⟩
  exact hWc.of_isClosed_subset hV.isClosed fun y hy => (hVU hy).2

private theorem exists_compactOpen_exhaustion {X : Type} [TopologicalSpace X]
    [SigmaCompactSpace X] (hcpt : ∀ x : X, ∃ W : Set X, IsCompact W ∧ IsOpen W ∧ x ∈ W) :
    ∃ V : ℕ → Set X, (∀ n, IsCompact (V n) ∧ IsOpen (V n)) ∧ Monotone V ∧ ⋃ n, V n = univ := by
  have key : ∀ K : Set X, IsCompact K → ∃ W : Set X, IsCompact W ∧ IsOpen W ∧ K ⊆ W := by
    intro K hK
    choose W hWc hWo hxW using hcpt
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover W hWo fun x _ => mem_iUnion.2 ⟨x, hxW x⟩
    exact ⟨⋃ x ∈ t, W x, t.isCompact_biUnion fun x _ => hWc x,
      isOpen_iUnion fun x => isOpen_iUnion fun _ => hWo x, ht⟩
  choose W hW using fun n => key (compactCovering X n) (isCompact_compactCovering X n)
  refine ⟨fun n => ⋃ m ∈ Finset.range (n + 1), W m, fun n => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (Finset.range (n + 1)).isCompact_biUnion fun m _ => (hW m).1
  · exact isOpen_iUnion fun m => isOpen_iUnion fun _ => (hW m).2.1
  · intro a b hab x hx
    simp only [mem_iUnion, Finset.mem_range] at hx ⊢
    obtain ⟨m, hm, hxm⟩ := hx
    exact ⟨m, by omega, hxm⟩
  · refine eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ n, compactCovering X n := by
      rw [iUnion_compactCovering]
      exact mem_univ x
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    simp only [mem_iUnion, Finset.mem_range]
    exact ⟨n, n, Nat.lt_succ_self n, (hW n).2.2 hn⟩

private theorem exists_compactOpen_mem {X : Type} [TopologicalSpace X] [AddGroup X]
    [IsTopologicalAddGroup X] {O : Set X} (hOc : IsCompact O) (hOo : IsOpen O)
    (h0 : (0 : X) ∈ O) (x : X) : ∃ W : Set X, IsCompact W ∧ IsOpen W ∧ x ∈ W := by
  refine ⟨(Homeomorph.subRight x) ⁻¹' O, (Homeomorph.subRight x).isCompact_preimage.2 hOc,
    hOo.preimage (Homeomorph.subRight x).continuous, ?_⟩
  show x - x ∈ O
  rwa [sub_self]

private theorem valued_exists_clopen {K Γ₀ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : K) (U : Set K) (hU : U ∈ 𝓝 x) :
    ∃ V : Set K, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  refine ⟨_, ?_, ?_, hγ⟩
  · exact (Valued.isClopen_ball K γ.1).preimage (continuous_sub_right x)
  · simp

private theorem borel_eq_generateFrom_preimage {A E : Type} [TopologicalSpace A] [PolishSpace A]
    [mA : MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [mE : MeasurableSpace E] [BorelSpace E] {r : A → E}
    (hr : Continuous r) (hinj : Function.Injective r) :
    mA = MeasurableSpace.generateFrom
      (Set.preimage r '' {U : Set E | IsOpen U ∧ Bornology.IsBounded U}) := by
  have hemb : MeasurableEmbedding r := hr.measurableEmbedding hinj
  have hE : mE = MeasurableSpace.generateFrom {U : Set E | IsOpen U ∧ Bornology.IsBounded U} := by
    apply le_antisymm
    · rw [BorelSpace.measurable_eq (α := E)]
      show MeasurableSpace.generateFrom {U : Set E | IsOpen U} ≤ _
      refine MeasurableSpace.generateFrom_le fun U hU => ?_
      have hdecomp : U = ⋃ n : ℕ, U ∩ Metric.ball (0 : E) n := by
        rw [← inter_iUnion, Metric.iUnion_ball_nat, inter_univ]
      rw [hdecomp]
      refine MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom ?_
      exact ⟨hU.inter Metric.isOpen_ball, Metric.isBounded_ball.subset inter_subset_right⟩
    · exact MeasurableSpace.generateFrom_le fun U hU => hU.1.measurableSet
  rw [← hemb.comap_eq, hE, MeasurableSpace.comap_generateFrom]

private theorem isLocallyConstant_indicator {X : Type} [TopologicalSpace X] {W : Set X} (hW : IsClopen W)
    (c : ℂ) : IsLocallyConstant (W.indicator fun _ => c) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ W
  · exact ⟨W, hW.isOpen, hx, fun x' hx' => by rw [indicator_of_mem hx', indicator_of_mem hx]⟩
  · exact ⟨Wᶜ, hW.isClosed.isOpen_compl, hx,
      fun x' hx' => by rw [indicator_of_notMem hx', indicator_of_notMem hx]⟩

private theorem hasCompactSupport_indicator {X : Type} [TopologicalSpace X] [T2Space X] {W : Set X} (hW : IsCompact W)
    (c : ℂ) : HasCompactSupport (W.indicator fun _ => c) :=
  HasCompactSupport.intro hW fun _ hx => indicator_of_notMem hx _

section Determination

variable {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {A : Type} [mA : MeasurableSpace A]
  {Q : ι₂ → Type} [mQ : ∀ k, MeasurableSpace (Q k)]

private def boxTest (φ : ι₁ → A → ℝ≥0) (V : ∀ k, Set (Q k)) (y : (ι₁ → A) × ∀ k, Q k) :
    ℝ≥0∞ :=
  (((∏ i, φ i (y.1 i)) * ∏ k, (V k).indicator (fun _ => (1 : ℝ≥0)) (y.2 k) : ℝ≥0) : ℝ≥0∞)

omit mA mQ in
private theorem boxTest_mono {φ ψ : ι₁ → A → ℝ≥0} (h : ∀ i a, φ i a ≤ ψ i a)
    (V : ∀ k, Set (Q k)) (y : (ι₁ → A) × ∀ k, Q k) : boxTest φ V y ≤ boxTest ψ V y := by
  unfold boxTest
  exact ENNReal.coe_le_coe.2 (mul_le_mul_left (Finset.prod_le_prod' fun i _ => h i _) _)

private theorem boxTest_measurable {φ : ι₁ → A → ℝ≥0} (hφ : ∀ i, Measurable (φ i))
    {V : ∀ k, Set (Q k)} (hV : ∀ k, MeasurableSet (V k)) : Measurable (boxTest φ V) := by
  unfold boxTest
  refine ENNReal.continuous_coe.measurable.comp (Measurable.mul ?_ ?_)
  · exact Finset.measurable_prod _ fun i _ =>
      (hφ i).comp ((measurable_pi_apply i).comp measurable_fst)
  · exact Finset.measurable_prod _ fun k _ =>
      (measurable_const.indicator (hV k)).comp ((measurable_pi_apply k).comp measurable_snd)

omit mA mQ in
private theorem boxTest_le_indicator {φ : ι₁ → A → ℝ≥0} {K : ι₁ → Set A} (hφ₁ : ∀ i a, φ i a ≤ 1)
    (hφK : ∀ i a, a ∉ K i → φ i a = 0) (V : ∀ k, Set (Q k)) (y : (ι₁ → A) × ∀ k, Q k) :
    boxTest φ V y ≤ ((univ.pi K) ×ˢ (univ.pi V)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
  by_cases hy : y ∈ (univ.pi K) ×ˢ (univ.pi V)
  · rw [indicator_of_mem hy]
    unfold boxTest
    refine ENNReal.coe_le_one_iff.2 (mul_le_one' (Finset.prod_le_one' fun i _ => hφ₁ i _)
      (Finset.prod_le_one' fun k _ => ?_))
    by_cases hk : y.2 k ∈ V k <;> simp [hk]
  · rw [indicator_of_notMem hy]
    unfold boxTest
    rcases not_and_or.1 (mem_prod.not.1 hy) with hy1 | hy2
    · obtain ⟨i, hi⟩ := not_forall.1 (mem_univ_pi.not.1 hy1)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (hφK i _ hi), zero_mul, ENNReal.coe_zero]
    · obtain ⟨k, hk⟩ := not_forall.1 (mem_univ_pi.not.1 hy2)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (indicator_of_notMem hk _), mul_zero, ENNReal.coe_zero]

private theorem lintegral_boxTest_le (μ : Measure ((ι₁ → A) × ∀ k, Q k)) {φ : ι₁ → A → ℝ≥0}
    {K : ι₁ → Set A} (hφ₁ : ∀ i a, φ i a ≤ 1) (hφK : ∀ i a, a ∉ K i → φ i a = 0)
    (hK : ∀ i, MeasurableSet (K i)) {V : ∀ k, Set (Q k)} (hV : ∀ k, MeasurableSet (V k)) :
    ∫⁻ y, boxTest φ V y ∂μ ≤ μ ((univ.pi K) ×ˢ (univ.pi V)) := by
  calc ∫⁻ y, boxTest φ V y ∂μ
      ≤ ∫⁻ y, ((univ.pi K) ×ˢ (univ.pi V)).indicator (fun _ => (1 : ℝ≥0∞)) y ∂μ :=
        lintegral_mono fun y => boxTest_le_indicator hφ₁ hφK V y
    _ = μ ((univ.pi K) ×ˢ (univ.pi V)) := by
        rw [lintegral_indicator_const ((MeasurableSet.univ_pi hK).prod (MeasurableSet.univ_pi hV)) 1, one_mul]

omit mA mQ in

private theorem indicator_box_eq (c : ι₁ → Set A) (V : ∀ k, Set (Q k))
    (y : (ι₁ → A) × ∀ k, Q k) :
    ((univ.pi c) ×ˢ (univ.pi V)).indicator (fun _ => (1 : ℝ≥0∞)) y =
      boxTest (fun i => (c i).indicator fun _ => (1 : ℝ≥0)) V y := by
  unfold boxTest
  by_cases hy : y ∈ (univ.pi c) ×ˢ (univ.pi V)
  · rw [indicator_of_mem hy]
    obtain ⟨hy1, hy2⟩ := hy
    rw [Finset.prod_eq_one fun i _ => indicator_of_mem (hy1 i (mem_univ i)) _,
      Finset.prod_eq_one fun k _ => indicator_of_mem (hy2 k (mem_univ k)) _, one_mul,
      ENNReal.coe_one]
  · rw [indicator_of_notMem hy]
    rw [mem_prod, mem_univ_pi, mem_univ_pi] at hy
    push Not at hy
    by_cases hy1 : ∀ i, y.1 i ∈ c i
    · obtain ⟨k, hk⟩ := hy hy1
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (indicator_of_notMem hk _), mul_zero,
        ENNReal.coe_zero]
    · push Not at hy1
      obtain ⟨i, hi⟩ := hy1
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _), zero_mul,
        ENNReal.coe_zero]

private theorem indicator_eq_indicator_one_mul {Y : Type} (s : Set Y) (u : Y → ℝ≥0∞) (y : Y) :
    s.indicator u y = s.indicator (fun _ => (1 : ℝ≥0∞)) y * u y := by
  by_cases hy : y ∈ s
  · rw [indicator_of_mem hy, indicator_of_mem hy, one_mul]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]

private theorem tendsto_lintegral_boxTest (μ : Measure ((ι₁ → A) × ∀ k, Q k)) {v : _ → ℝ≥0∞}
    (hv : Measurable v) {c : ι₁ → Set A} {Φ : ι₁ → A → ℝ≥0} {φ : ι₁ → ℕ → A → ℝ≥0}
    (hΦ : ∀ i, Measurable (Φ i)) (hφ : ∀ i n, Measurable (φ i n))
    (hle : ∀ i n a, φ i n a ≤ Φ i a)
    (hlim : ∀ i a, Tendsto (fun n => φ i n a) atTop (𝓝 ((c i).indicator (fun _ => (1 : ℝ≥0)) a)))
    {V : ∀ k, Set (Q k)} (hV : ∀ k, MeasurableSet (V k))
    (hfin : ∫⁻ y, boxTest Φ V y * v y ∂μ ≠ ∞) :
    Tendsto (fun n => ∫⁻ y, boxTest (fun i => φ i n) V y * v y ∂μ) atTop
      (𝓝 (∫⁻ y, boxTest (fun i => (c i).indicator fun _ => (1 : ℝ≥0)) V y * v y ∂μ)) := by
  have hind_le : ∀ i a, (c i).indicator (fun _ => (1 : ℝ≥0)) a ≤ Φ i a := fun i a =>
    le_of_tendsto' (hlim i a) fun n => hle i n a
  refine tendsto_lintegral_of_dominated_convergence (fun y => boxTest Φ V y * v y)
    (fun n => (boxTest_measurable (fun i => hφ i n) hV).mul hv) ?_ hfin ?_
  · intro n
    exact Eventually.of_forall fun y =>
      mul_le_mul_left (boxTest_mono (fun i a => hle i n a) V y) _
  · filter_upwards [ae_lt_top ((boxTest_measurable hΦ hV).mul hv) hfin] with y hy
    by_cases hΦy : boxTest Φ V y = 0
    · have hzero : ∀ n, boxTest (fun i => φ i n) V y = 0 := fun n =>
        le_antisymm ((boxTest_mono (fun i a => hle i n a) V y).trans hΦy.le) zero_le
      have hzero' : boxTest (fun i => (c i).indicator fun _ => (1 : ℝ≥0)) V y = 0 :=
        le_antisymm ((boxTest_mono hind_le V y).trans hΦy.le) zero_le
      simp only [hzero, hzero', zero_mul]
      exact tendsto_const_nhds
    · have hvy : v y ≠ ∞ := (ENNReal.lt_top_of_mul_ne_top_right hy.ne hΦy).ne
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr hvy)
      unfold boxTest
      refine (ENNReal.continuous_coe.tendsto _).comp ?_
      exact (tendsto_finsetProd _ fun i _ => hlim i (y.1 i)).mul tendsto_const_nhds

private theorem ae_eq_of_boxTests (μ : Measure ((ι₁ → A) × ∀ k, Q k)) [SigmaFinite μ]
    {u w : _ → ℝ≥0∞} (hu : Measurable u) (hw : Measurable w)
    (CA : Set (Set A)) (hCA : MeasurableSpace.generateFrom CA = mA) (hCAπ : IsPiSystem CA)
    (sA : ℕ → Set A) (hsA : ∀ n, sA n ∈ CA) (hsA_mono : Monotone sA) (hsA_univ : ⋃ n, sA n = univ)
    (CQ : ∀ k, Set (Set (Q k))) (hCQ : ∀ k, MeasurableSpace.generateFrom (CQ k) = mQ k)
    (hCQπ : ∀ k, IsPiSystem (CQ k)) (sQ : ∀ k, ℕ → Set (Q k)) (hsQ : ∀ k n, sQ k n ∈ CQ k)
    (hsQ_mono : ∀ k, Monotone (sQ k)) (hsQ_univ : ∀ k, ⋃ n, sQ k n = univ)
    (𝒜 : Set (A → ℝ≥0)) (h𝒜m : ∀ φ ∈ 𝒜, Measurable φ)
    (h𝒜 : ∀ c ∈ CA, ∃ Φ ∈ 𝒜, ∃ φ : ℕ → A → ℝ≥0, (∀ n, φ n ∈ 𝒜) ∧ (∀ n a, φ n a ≤ Φ a) ∧
      ∀ a, Tendsto (fun n => φ n a) atTop (𝓝 (c.indicator (fun _ => (1 : ℝ≥0)) a)))
    (hid : ∀ (φ : ι₁ → A → ℝ≥0) (V : ∀ k, Set (Q k)), (∀ i, φ i ∈ 𝒜) → (∀ k, V k ∈ CQ k) →
      ∫⁻ y, boxTest φ V y * u y ∂μ = ∫⁻ y, boxTest φ V y * w y ∂μ)
    (hfin : ∀ (φ : ι₁ → A → ℝ≥0) (V : ∀ k, Set (Q k)), (∀ i, φ i ∈ 𝒜) → (∀ k, V k ∈ CQ k) →
      ∫⁻ y, boxTest φ V y * w y ∂μ ≠ ∞) :
    u =ᵐ[μ] w := by
  have hCA_meas : ∀ c ∈ CA, MeasurableSet c := fun c hc =>
    hCA ▸ MeasurableSpace.measurableSet_generateFrom hc
  have hCQ_meas : ∀ k, ∀ V ∈ CQ k, MeasurableSet V := fun k V hV =>
    hCQ k ▸ MeasurableSpace.measurableSet_generateFrom hV
  have hCA_span : IsCountablySpanning CA := ⟨sA, hsA, hsA_univ⟩
  have hCQ_span : ∀ k, IsCountablySpanning (CQ k) := fun k => ⟨sQ k, hsQ k, hsQ_univ k⟩

  have hgen : (by infer_instance : MeasurableSpace ((ι₁ → A) × ∀ k, Q k)) =
      MeasurableSpace.generateFrom
        (image2 (· ×ˢ ·) (univ.pi '' univ.pi fun _ : ι₁ => CA) (univ.pi '' univ.pi CQ)) :=
    (generateFrom_eq_prod
      (generateFrom_eq_pi (fun _ => hCA) fun _ => hCA_span)
      (generateFrom_eq_pi hCQ hCQ_span)
      (IsCountablySpanning.pi fun _ => hCA_span) (IsCountablySpanning.pi hCQ_span)).symm
  have hπ : IsPiSystem
      (image2 (· ×ˢ ·) (univ.pi '' univ.pi fun _ : ι₁ => CA) (univ.pi '' univ.pi CQ)) :=
    (IsPiSystem.pi fun _ => hCAπ).prod (IsPiSystem.pi hCQπ)
  have hbox_mem : ∀ (c : ι₁ → Set A) (V : ∀ k, Set (Q k)), (∀ i, c i ∈ CA) →
      (∀ k, V k ∈ CQ k) → (univ.pi c) ×ˢ (univ.pi V) ∈
        image2 (· ×ˢ ·) (univ.pi '' univ.pi fun _ : ι₁ => CA) (univ.pi '' univ.pi CQ) :=
    fun c V hc hV => mem_image2_of_mem ⟨c, fun i _ => hc i, rfl⟩ ⟨V, fun k _ => hV k, rfl⟩
  have hbox_meas : ∀ (c : ι₁ → Set A) (V : ∀ k, Set (Q k)), (∀ i, c i ∈ CA) →
      (∀ k, V k ∈ CQ k) → MeasurableSet ((univ.pi c) ×ˢ (univ.pi V)) := fun c V hc hV =>
    (MeasurableSet.univ_pi fun i => hCA_meas _ (hc i)).prod
      (MeasurableSet.univ_pi fun k => hCQ_meas k _ (hV k))

  have hwith : ∀ (v : _ → ℝ≥0∞) (c : ι₁ → Set A) (V : ∀ k, Set (Q k)), (∀ i, c i ∈ CA) →
      (∀ k, V k ∈ CQ k) → μ.withDensity v ((univ.pi c) ×ˢ (univ.pi V)) =
        ∫⁻ y, boxTest (fun i => (c i).indicator fun _ => (1 : ℝ≥0)) V y * v y ∂μ := by
    intro v c V hc hV
    rw [withDensity_apply _ (hbox_meas c V hc hV), ← lintegral_indicator (hbox_meas c V hc hV)]
    refine lintegral_congr fun y => ?_
    rw [indicator_eq_indicator_one_mul, indicator_box_eq]

  have hagree : ∀ (c : ι₁ → Set A) (V : ∀ k, Set (Q k)), (∀ i, c i ∈ CA) → (∀ k, V k ∈ CQ k) →
      μ.withDensity u ((univ.pi c) ×ˢ (univ.pi V)) =
        μ.withDensity w ((univ.pi c) ×ˢ (univ.pi V)) := by
    intro c V hc hV
    choose Φ hΦ φ hφ hle hlim using fun i => h𝒜 (c i) (hc i)
    rw [hwith u c V hc hV, hwith w c V hc hV]
    have hΦm : ∀ i, Measurable (Φ i) := fun i => h𝒜m _ (hΦ i)
    have hφm : ∀ i n, Measurable (φ i n) := fun i n => h𝒜m _ (hφ i n)
    have hVm : ∀ k, MeasurableSet (V k) := fun k => hCQ_meas k _ (hV k)
    have hfinw : ∫⁻ y, boxTest Φ V y * w y ∂μ ≠ ∞ := hfin Φ V hΦ hV
    have hfinu : ∫⁻ y, boxTest Φ V y * u y ∂μ ≠ ∞ := by
      rw [hid Φ V hΦ hV]
      exact hfinw
    have h1 := (tendsto_lintegral_boxTest μ hu hΦm hφm hle hlim hVm hfinu).congr
      fun n => hid _ V (fun i => hφ i n) hV
    have h2 := tendsto_lintegral_boxTest μ hw hΦm hφm hle hlim hVm hfinw
    exact tendsto_nhds_unique h1 h2

  have hfin_box : ∀ n,
      μ.withDensity u ((univ.pi fun _ : ι₁ => sA n) ×ˢ (univ.pi fun k => sQ k n)) ≠ ∞ := by
    intro n
    rw [hagree _ _ (fun _ => hsA n) (fun k => hsQ k n),
      hwith w _ _ (fun _ => hsA n) (fun k => hsQ k n)]
    obtain ⟨Φ, hΦ, φ, -, hle, hlim⟩ := h𝒜 (sA n) (hsA n)
    have hind_le : ∀ a, (sA n).indicator (fun _ => (1 : ℝ≥0)) a ≤ Φ a := fun a =>
      le_of_tendsto' (hlim a) fun m => hle m a
    refine ne_top_of_le_ne_top
      (hfin (fun _ => Φ) (fun k => sQ k n) (fun _ => hΦ) fun k => hsQ k n) ?_
    exact lintegral_mono fun y => mul_le_mul_left (boxTest_mono (fun _ a => hind_le a) _ y) _

  have hcover : ⋃ n, (univ.pi fun _ : ι₁ => sA n) ×ˢ (univ.pi fun k => sQ k n) = univ := by
    refine eq_univ_of_forall fun y => ?_
    have h1 : ∀ i, ∀ᶠ n in atTop, y.1 i ∈ sA n := by
      intro i
      have hmem : y.1 i ∈ ⋃ n, sA n := by
        rw [hsA_univ]
        exact mem_univ _
      obtain ⟨n, hn⟩ := mem_iUnion.1 hmem
      exact eventually_atTop.2 ⟨n, fun m hm => hsA_mono hm hn⟩
    have h2 : ∀ k, ∀ᶠ n in atTop, y.2 k ∈ sQ k n := by
      intro k
      have hmem : y.2 k ∈ ⋃ n, sQ k n := by
        rw [hsQ_univ k]
        exact mem_univ _
      obtain ⟨n, hn⟩ := mem_iUnion.1 hmem
      exact eventually_atTop.2 ⟨n, fun m hm => hsQ_mono k hm hn⟩
    obtain ⟨n, hn1, hn2⟩ := ((eventually_all.2 h1).and (eventually_all.2 h2)).exists
    exact mem_iUnion.2 ⟨n, fun i _ => hn1 i, fun k _ => hn2 k⟩

  have hmeas_eq : μ.withDensity u = μ.withDensity w := by
    refine Measure.ext_of_generateFrom_of_iUnion _
      (fun n => (univ.pi fun _ : ι₁ => sA n) ×ˢ (univ.pi fun k => sQ k n)) hgen hπ hcover
      (fun n => hbox_mem _ _ (fun _ => hsA n) fun k => hsQ k n) hfin_box ?_
    rintro _ ⟨_, ⟨c, hc, rfl⟩, _, ⟨V, hV, rfl⟩, rfl⟩
    exact hagree c V (fun i => hc i (mem_univ i)) fun k => hV k (mem_univ k)
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hu hw fun s hs _ => ?_
  rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, hmeas_eq]

end Determination
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private def archCoord : InfiniteAdeleRing ℚ → mixedEmbedding.mixedSpace ℚ :=
  InfiniteAdeleRing.ringEquiv_mixedSpace ℚ

private theorem archCoord_injective : Function.Injective archCoord :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).injective

attribute [local instance] archBorel

attribute [local instance] archBorelSpace

private theorem archPolish [∀ w : InfinitePlace ℚ, ProperSpace w.Completion] :
    PolishSpace (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (PolishSpace ((w : InfinitePlace ℚ) → w.Completion))

private theorem isCompact_preimage_archCoord [∀ w : InfinitePlace ℚ, ProperSpace w.Completion]
    (hcont : Continuous archCoord) {C : Set (mixedEmbedding.mixedSpace ℚ)} (hC : IsCompact C) :
    IsCompact (archCoord ⁻¹' C) := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : mixedEmbedding.mixedSpace ℚ)
  have hsub : archCoord ⁻¹' C ⊆
      (univ.pi fun w : InfinitePlace ℚ => Metric.closedBall (0 : w.Completion) R : Set (InfiniteAdeleRing ℚ)) := by
    intro x hx
    have hxR : ‖archCoord x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
    refine mem_univ_pi.2 fun w => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    rcases w.isReal_or_isComplex with hw | hw
    · have h1 : ‖(archCoord x).1 ⟨w, hw⟩‖ ≤ ‖(archCoord x).1‖ := norm_le_pi_norm _ _
      have h2 : ‖(archCoord x).1‖ ≤ ‖archCoord x‖ := norm_fst_le _
      have h3 : ‖(archCoord x).1 ⟨w, hw⟩‖ = ‖x w‖ := by
        have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).dist_eq (x w) 0
        rw [map_zero, dist_zero_right, dist_zero_right] at h
        exact h
      rw [← h3]
      exact h1.trans (h2.trans hxR)
    · have h1 : ‖(archCoord x).2 ⟨w, hw⟩‖ ≤ ‖(archCoord x).2‖ := norm_le_pi_norm _ _
      have h2 : ‖(archCoord x).2‖ ≤ ‖archCoord x‖ := norm_snd_le _
      have h3 : ‖(archCoord x).2 ⟨w, hw⟩‖ = ‖x w‖ := by
        have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq (x w) 0
        rw [map_zero, dist_zero_right, dist_zero_right] at h
        exact h
      rw [← h3]
      exact h1.trans (h2.trans hxR)
  have hcpt : IsCompact
      (univ.pi fun w : InfinitePlace ℚ => Metric.closedBall (0 : w.Completion) R : Set (InfiniteAdeleRing ℚ)) :=
    isCompact_univ_pi fun w => isCompact_closedBall (0 : w.Completion) R
  exact hcpt.of_isClosed_subset (hC.isClosed.preimage hcont) hsub

private def archGenerators : Set (Set (InfiniteAdeleRing ℚ)) :=
  Set.preimage archCoord '' {U : Set (mixedEmbedding.mixedSpace ℚ) | IsOpen U ∧ Bornology.IsBounded U}

private theorem archGenerate [∀ w : InfinitePlace ℚ, ProperSpace w.Completion] (hcont : Continuous archCoord) :
    MeasurableSpace.generateFrom archGenerators = archBorel := by
  haveI := archPolish
  exact (borel_eq_generateFrom_preimage hcont archCoord_injective).symm

private theorem archGenerators_piSystem : IsPiSystem archGenerators := by
  rintro _ ⟨U, ⟨hU, hUb⟩, rfl⟩ _ ⟨U', ⟨hU', -⟩, rfl⟩ -
  exact ⟨U ∩ U', ⟨hU.inter hU', hUb.subset inter_subset_left⟩, preimage_inter⟩

private def archBalls (n : ℕ) : Set (InfiniteAdeleRing ℚ) :=
  archCoord ⁻¹' Metric.ball (0 : mixedEmbedding.mixedSpace ℚ) n

private theorem archBalls_mem (n : ℕ) : archBalls n ∈ archGenerators :=
  ⟨Metric.ball 0 n, ⟨Metric.isOpen_ball, Metric.isBounded_ball⟩, rfl⟩

private theorem archBalls_mono : Monotone archBalls := fun _ _ hab =>
  preimage_mono (Metric.ball_subset_ball (Nat.cast_le.2 hab))

private theorem archBalls_iUnion : ⋃ n, archBalls n = univ := by
  unfold archBalls
  rw [← preimage_iUnion, Metric.iUnion_ball_nat, preimage_univ]

private theorem smoothFamily_archCoord_measurable (hcont : Continuous archCoord)
    {φ : InfiniteAdeleRing ℚ → ℝ≥0} (hφ : φ ∈ smoothFamily archCoord) : Measurable φ := by
  obtain ⟨g, hg, -, -, -, rfl⟩ := hφ
  exact (continuous_real_toNNReal.comp (hg.continuous.comp hcont)).measurable

attribute [local instance] localBorel

attribute [local instance] localBorelSpace

private def localCompactOpens (p : HeightOneSpectrum (𝓞 ℚ)) : Set (Set (p.adicCompletion ℚ)) :=
  {V | IsCompact V ∧ IsOpen V}

private theorem localCompactOpens_piSystem (p : HeightOneSpectrum (𝓞 ℚ)) : IsPiSystem (localCompactOpens p) :=
  fun _ hV _ hW _ => ⟨hV.1.inter_right hW.1.isClosed, hV.2.inter hW.2⟩

private theorem isCompact_localIntegers (p : HeightOneSpectrum (𝓞 ℚ))
    [CompactSpace (p.adicCompletionIntegers ℚ)] :
    IsCompact (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
  haveI : CompactSpace ((p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) :=
    inferInstanceAs (CompactSpace (p.adicCompletionIntegers ℚ))
  exact isCompact_iff_compactSpace.2 this

private theorem exists_localCompactOpen_mem (p : HeightOneSpectrum (𝓞 ℚ))
    [CompactSpace (p.adicCompletionIntegers ℚ)] (x : p.adicCompletion ℚ) :
    ∃ W : Set (p.adicCompletion ℚ), IsCompact W ∧ IsOpen W ∧ x ∈ W :=
  exists_compactOpen_mem (isCompact_localIntegers p) (Valued.isOpen_valuationSubring _)
    (SetLike.mem_coe.2 (zero_mem _)) x

private theorem localGenerate (p : HeightOneSpectrum (𝓞 ℚ)) [ProperSpace (p.adicCompletion ℚ)]
    [CompactSpace (p.adicCompletionIntegers ℚ)] :
    MeasurableSpace.generateFrom (localCompactOpens p) = localBorel p :=
  (isTopologicalBasis_compactOpen (fun x _ hU => valued_exists_clopen x _ hU)
    (exists_localCompactOpen_mem p)).borel_eq_generateFrom.symm

private theorem exists_localExhaustion (p : HeightOneSpectrum (𝓞 ℚ)) [ProperSpace (p.adicCompletion ℚ)]
    [CompactSpace (p.adicCompletionIntegers ℚ)] :
    ∃ V : ℕ → Set (p.adicCompletion ℚ), (∀ n, V n ∈ localCompactOpens p) ∧ Monotone V ∧ ⋃ n, V n = univ := by
  obtain ⟨V, hV, hmono, huniv⟩ := exists_compactOpen_exhaustion (exists_localCompactOpen_mem p)
  exact ⟨V, fun n => hV n, hmono, huniv⟩

variable {n : ℕ}

private abbrev CoordsVec (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Type :=
  (Fin n → InfiniteAdeleRing ℚ) × ∀ k : Fin n × {p // p ∈ S}, k.2.1.adicCompletion ℚ

private def coordsOfVec (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin n → AdeleRing (𝓞 ℚ) ℚ) :
    CoordsVec n S :=
  (fun j => AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j), fun k => evalHom k.2.1 (x k.1))

private theorem continuous_coordsOfVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Continuous (coordsOfVec n S) := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun k => ?_)
  · exact (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ).comp (continuous_apply j)
  · exact (continuous_evalHom k.2.1).comp (continuous_apply k.1)

private def rowOfVec (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : CoordsVec n S) : Fin n → AdeleRing (𝓞 ℚ) ℚ :=
  fun j => (y.1 j, ∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (y.2 (j, p)))

private theorem adeleArch_rowOfVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : CoordsVec n S) (j : Fin n) :
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ (rowOfVec n S y j) = y.1 j :=
  rfl

private theorem evalHom_rowOf_of_memVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : CoordsVec n S) (j : Fin n)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ S) : evalHom p (rowOfVec n S y j) = y.2 (j, ⟨p, hp⟩) := by
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p (∑ q ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ q.1 (y.2 (j, q))) = _
  rw [map_sum]
  simp only [AdelicLevel.finAdeleEval_apply]
  rw [Finset.sum_eq_single (⟨p, hp⟩ : {p // p ∈ S})]
  · exact StandardAddChar.finAdeleSingleAt_apply_self ℚ p _
  · intro q _ hq
    exact StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hq (Subtype.ext h.symm)
  · intro h
    exact absurd (Finset.mem_attach _ _) h

private theorem evalHom_rowOf_of_notMemVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : CoordsVec n S) (j : Fin n)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S) : evalHom p (rowOfVec n S y j) = 0 := by
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p (∑ q ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ q.1 (y.2 (j, q))) = 0
  rw [map_sum]
  simp only [AdelicLevel.finAdeleEval_apply]
  exact Finset.sum_eq_zero fun q _ =>
    StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hp (by rw [h]; exact q.2)

private theorem continuous_rowOfVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Continuous (rowOfVec n S) := by
  refine continuous_pi fun j => Continuous.prodMk ((continuous_apply j).comp continuous_fst) ?_
  exact continuous_finsetSum _ fun p _ =>
    (StandardAddChar.continuous_finAdeleSingleAt ℚ p.1).comp ((continuous_apply (j, p)).comp continuous_snd)

private theorem coordsOf_add_rowOfVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin n → AdeleRing (𝓞 ℚ) ℚ)
    (t : CoordsVec n S) : coordsOfVec n S (x + rowOfVec n S t) = coordsOfVec n S x + t := by
  refine Prod.ext (funext fun j => ?_) (funext fun k => ?_)
  · show AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j + rowOfVec n S t j) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j) + t.1 j
    rw [map_add, adeleArch_rowOfVec]
  · show evalHom k.2.1 (x k.1 + rowOfVec n S t k.1) = evalHom k.2.1 (x k.1) + t.2 k
    rw [map_add, evalHom_rowOf_of_memVec S t k.1 k.2.2]

private theorem evalHom_add_rowOfVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin n → AdeleRing (𝓞 ℚ) ℚ)
    (t : CoordsVec n S) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S) (j : Fin n) :
    evalHom p ((x + rowOfVec n S t) j) = evalHom p (x j) := by
  show evalHom p (x j + rowOfVec n S t j) = evalHom p (x j)
  rw [map_add, evalHom_rowOf_of_notMemVec S t j hp, add_zero]

private def tailRowVec (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Fin n → AdeleRing (𝓞 ℚ) ℚ :=
  fun _ => tailAdele S

private theorem coordsOf_tailRowVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : coordsOfVec n S (tailRowVec n S) = 0 := by
  refine Prod.ext (funext fun _ => ?_) (funext fun k => ?_)
  · show AdelicLevel.adeleArch (𝓞 ℚ) ℚ (tailAdele S) = 0
    rfl
  · show evalHom k.2.1 (tailAdele S) = 0
    rw [evalHom_tailAdele, if_pos k.2.2]

private theorem evalHom_tailRow_of_notMemVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {p : HeightOneSpectrum (𝓞 ℚ)}
    (hp : p ∉ S) (j : Fin n) : evalHom p (tailRowVec n S j) = 1 := by
  show evalHom p (tailAdele S) = 1
  rw [evalHom_tailAdele, if_neg hp]

private def rowRepVec (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : CoordsVec n S) : Fin n → AdeleRing (𝓞 ℚ) ℚ :=
  tailRowVec n S + rowOfVec n S y

private theorem continuous_rowRepVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Continuous (rowRepVec n S) :=
  continuous_const.add (continuous_rowOfVec S)

private theorem coordsOf_rowRepVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : CoordsVec n S) :
    coordsOfVec n S (rowRepVec n S y) = y := by
  unfold rowRepVec
  rw [coordsOf_add_rowOfVec, coordsOf_tailRowVec, zero_add]

private theorem evalHom_rowRep_of_notMemVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : CoordsVec n S)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S) (j : Fin n) : evalHom p (rowRepVec n S y j) = 1 := by
  rw [rowRepVec, evalHom_add_rowOfVec S (tailRowVec n S) y hp j, evalHom_tailRow_of_notMemVec S hp j]

attribute [local instance] countable_primes

attribute [local instance] properCompletion archSecondCountable

attribute [local instance] secondCountableAdeles NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem borelRowsVec : BorelSpace (Fin n → AdeleRing (𝓞 ℚ) ℚ) := inferInstance

attribute [local instance] borelRowsVec

attribute [local instance] localSecondCountable

private theorem archRowsSecondCountableVec : SecondCountableTopology (Fin n → InfiniteAdeleRing ℚ) :=
  inferInstance

private theorem localRowsSecondCountableVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    SecondCountableTopology (∀ k : Fin n × {p // p ∈ S}, k.2.1.adicCompletion ℚ) :=
  inferInstance

attribute [local instance] archRowsSecondCountableVec localRowsSecondCountableVec

private theorem secondCountableCoordsVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    SecondCountableTopology (CoordsVec n S) :=
  inferInstance

attribute [local instance] secondCountableCoordsVec

private theorem archRowsBorelVec : BorelSpace (Fin n → InfiniteAdeleRing ℚ) := Pi.borelSpace

private theorem localRowsBorelVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    BorelSpace (∀ k : Fin n × {p // p ∈ S}, k.2.1.adicCompletion ℚ) :=
  Pi.borelSpace

attribute [local instance] archRowsBorelVec localRowsBorelVec

private theorem borelCoordsVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : BorelSpace (CoordsVec n S) := Prod.borelSpace

attribute [local instance] borelCoordsVec

private theorem measurable_rowRepVec (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Measurable (rowRepVec n S) :=
  (continuous_rowRepVec S).measurable

private theorem continuous_archCoord : Continuous archCoord := AdelicBox.continuous_ringEquiv_mixedSpace ℚ

private def finPart (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ))
    (z : FiniteAdeleRing (𝓞 ℚ) ℚ) : ℝ≥0 :=
  (∏ v : {p // p ∈ S}, (W v).indicator (fun _ => (1 : ℝ≥0)) (z v.1)) *
    if ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → z v ∈ v.adicCompletionIntegers ℚ then 1 else 0

private def testFactor (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : InfiniteAdeleRing ℚ → ℝ≥0)
    (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)) (a : AdeleRing (𝓞 ℚ) ℚ) : ℝ≥0 :=
  φ a.1 * finPart S W a.2

private def testFactorC (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : InfiniteAdeleRing ℚ → ℝ≥0)
    (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)) (a : AdeleRing (𝓞 ℚ) ℚ) : ℂ :=
  ((testFactor S φ W a : ℝ) : ℂ)

private def extSets (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ)) : Set (v.adicCompletion ℚ) :=
  if hv : v ∈ S then W ⟨v, hv⟩ else ∅

private theorem extSets_coe (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ))
    (v : {p // p ∈ S}) : extSets S W v.1 = W v := by
  show (if hv : v.1 ∈ S then W ⟨v.1, hv⟩ else ∅) = W v
  rw [dif_pos v.2]

private def localFactorC (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ)) (t : v.adicCompletion ℚ) : ℂ :=
  (extSets S W v).indicator (fun _ => (1 : ℂ)) t

private theorem coe_indicator_one_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)) (v : {p // p ∈ S}) (t : v.1.adicCompletion ℚ) :
    ((((W v).indicator (fun _ => (1 : ℝ≥0)) t : ℝ≥0) : ℝ) : ℂ) = localFactorC S W v.1 t := by
  unfold localFactorC
  rw [extSets_coe]
  by_cases ht : t ∈ W v <;> simp [ht]

private theorem finPart_eq_shape (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)) (z : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ((finPart S W z : ℝ) : ℂ) = (∏ v ∈ S, localFactorC S W v (z v)) *
      (if ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → z v ∈ v.adicCompletionIntegers ℚ then (1 : ℂ) else 0) := by
  unfold finPart
  rw [← Finset.prod_coe_sort S (fun v => localFactorC S W v (z v))]
  by_cases hc : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → z v ∈ v.adicCompletionIntegers ℚ
  · rw [if_pos hc, if_pos hc, mul_one, mul_one, NNReal.coe_prod, Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun v _ => coe_indicator_one_eq S W v (z v.1)
  · rw [if_neg hc, if_neg hc, mul_zero, mul_zero, NNReal.coe_zero, Complex.ofReal_zero]

private theorem isClopen_extSets (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)} (hW : ∀ v, W v ∈ localCompactOpens v.1)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ S) : IsClopen (extSets S W v) := by
  rw [show extSets S W v = W ⟨v, hv⟩ from dif_pos hv]
  exact ⟨(hW ⟨v, hv⟩).1.isClosed, (hW ⟨v, hv⟩).2⟩

private theorem isCompact_extSets (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)} (hW : ∀ v, W v ∈ localCompactOpens v.1)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ S) : IsCompact (extSets S W v) := by
  rw [show extSets S W v = W ⟨v, hv⟩ from dif_pos hv]
  exact (hW ⟨v, hv⟩).1

private theorem testFactorC_mem_pureTensorSet (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {φ : InfiniteAdeleRing ℚ → ℝ≥0} (hφ : φ ∈ smoothFamily archCoord)
    {W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)} (hW : ∀ v, W v ∈ localCompactOpens v.1) :
    testFactorC S φ W ∈ NumberField.AdelicFourier.pureTensorSet ℚ := by
  obtain ⟨g, hg_smooth, hg_supp, hg_nonneg, -, rfl⟩ := hφ
  have hgC_supp : HasCompactSupport fun t => (g t : ℂ) := hg_supp.comp_left Complex.ofReal_zero
  have hgC_smooth : ContDiff ℝ (⊤ : ℕ∞) fun t => (g t : ℂ) := Complex.ofRealCLM.contDiff.comp hg_smooth
  obtain ⟨hlc, hcs⟩ :=
    NumberField.AdelicFourier.isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
      ℚ S (localFactorC S W) (fun v hv => isLocallyConstant_indicator (isClopen_extSets S hW hv) 1)
      (fun v hv => hasCompactSupport_indicator (isCompact_extSets S hW hv) 1)
  refine ⟨hgC_supp.toSchwartzMap hgC_smooth, _, hlc, hcs, ?_⟩
  funext a
  show (((Real.toNNReal (g (archCoord a.1)) * finPart S W a.2 : ℝ≥0) : ℝ) : ℂ) = _
  rw [NNReal.coe_mul, Complex.ofReal_mul, Real.coe_toNNReal _ (hg_nonneg _), finPart_eq_shape]
  rfl

private theorem smoothFamily_exists_compact {φ : InfiniteAdeleRing ℚ → ℝ≥0} (hφ : φ ∈ smoothFamily archCoord) :
    ∃ K : Set (InfiniteAdeleRing ℚ), IsCompact K ∧ MeasurableSet K ∧ (∀ a, φ a ≤ 1) ∧ ∀ a, a ∉ K → φ a = 0 := by
  obtain ⟨g, -, hg_supp, -, hg_le, rfl⟩ := hφ
  refine ⟨archCoord ⁻¹' tsupport g, isCompact_preimage_archCoord continuous_archCoord hg_supp,
    ((isClosed_tsupport g).preimage continuous_archCoord).measurableSet, fun a => ?_, fun a ha => ?_⟩
  · exact Real.toNNReal_le_one.2 (hg_le _)
  · show Real.toNNReal (g (archCoord a)) = 0
    rw [image_eq_zero_of_notMem_tsupport ha, Real.toNNReal_zero]

end UniquenessHead
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end UniquenessPrinciple
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section CoefficientVanishing

open NumberField.StandardAddChar Filter Topology Set
open scoped NNReal Classical

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem psiQ_eq_one_of_integral (w : AdeleRing (𝓞 ℚ) ℚ)
    (hfin : ∀ q : HeightOneSpectrum (𝓞 ℚ), evalHom q w ∈ q.adicCompletionIntegers ℚ)
    (harch : AdelicLevel.adeleArch (𝓞 ℚ) ℚ w = 0) : psiQ w = 1 := by
  rw [psiQ_apply]
  have h1 : w.1 = 0 := harch
  rw [h1, AddChar.map_zero_eq_one, one_mul]
  exact psiFin_eq_one_of_forall_mem w.2 fun v => hfin v

private theorem kernel_eq_head {n : ℕ} (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (c t : Fin n → AdeleRing (𝓞 ℚ) ℚ)
    (hc : ∀ i, IntegralOutsideAll S (c i)) (ht : ∀ i, IntegralOutsideAll S (t i)) :
    psiQ (-(c ⬝ᵥ t)) = psiQ (-(c ⬝ᵥ fun i => headAdele S (t i))) := by
  have hsplit : c ⬝ᵥ t = (c ⬝ᵥ fun i => headAdele S (t i)) + c ⬝ᵥ (t - fun i => headAdele S (t i)) := by
    rw [dotProduct_sub, add_sub_cancel]
  rw [hsplit, neg_add, AddChar.map_add_eq_mul,
    psiQ_eq_one_of_integral (-(c ⬝ᵥ (t - fun i => headAdele S (t i)))) ?_ ?_, mul_one]
  · intro q
    rw [map_neg]
    refine neg_mem ?_
    simp only [dotProduct, map_sum, map_mul, map_sub, Pi.sub_apply]
    refine sum_mem fun i _ => ?_
    by_cases hq : q ∈ S
    · rw [evalHom_headAdele_of_mem S (t i) hq, sub_self, mul_zero]
      exact zero_mem _
    · rw [evalHom_headAdele_of_notMem S (t i) hq, sub_zero]
      exact mul_mem (hc i q hq) (ht i q hq)
  · simp only [map_neg, dotProduct, map_sum, map_mul, map_sub, Pi.sub_apply, adeleArch_headAdele, sub_self,
      mul_zero, Finset.sum_const_zero, neg_zero]

attribute [local instance] archBorel archBorelSpace localBorel localBorelSpace countable_primes properCompletion
  archSecondCountable secondCountableAdeles localSecondCountable archRowsSecondCountableVec localRowsSecondCountableVec
  secondCountableCoordsVec archRowsBorelVec localRowsBorelVec borelRowsVec borelCoordsVec

variable {n : ℕ}

private theorem measurable_coordsOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Measurable (coordsOfVec n S) :=
  (continuous_coordsOfVec S).measurable

private theorem integralOutside_sub_rowRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin n → AdeleRing (𝓞 ℚ) ℚ)
    (hx : ∀ i, IntegralOutsideAll S (x i)) (i : Fin n) :
    IntegralOutside S ((x - rowRepVec n S (coordsOfVec n S x)) i) := by
  have hc := coordsOf_rowRepVec S (coordsOfVec n S x)
  refine ⟨fun q hq => ?_, fun q hq => ?_, ?_⟩
  · rw [Pi.sub_apply, map_sub, evalHom_rowRep_of_notMemVec S _ hq i]
    exact sub_mem (hx i q hq) (one_mem _)
  · have h : evalHom q (rowRepVec n S (coordsOfVec n S x) i) = evalHom q (x i) :=
      congrArg (fun y : CoordsVec n S => y.2 (i, ⟨q, hq⟩)) hc
    rw [Pi.sub_apply, map_sub, sub_eq_zero]
    exact h.symm
  · have h : AdelicLevel.adeleArch (𝓞 ℚ) ℚ (rowRepVec n S (coordsOfVec n S x) i) =
        AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x i) :=
      congrArg (fun y : CoordsVec n S => y.1 i) hc
    rw [Pi.sub_apply, map_sub, sub_eq_zero]
    exact h.symm

private theorem eq_comp_rowRep_of_invariant (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (g : (Fin n → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (hginv : ∀ x u, (∀ i, IntegralOutside S (u i)) → g (x + u) = g x) (x : Fin n → AdeleRing (𝓞 ℚ) ℚ)
    (hx : ∀ i, IntegralOutsideAll S (x i)) : g x = g (rowRepVec n S (coordsOfVec n S x)) := by
  have h := hginv (rowRepVec n S (coordsOfVec n S x)) (x - rowRepVec n S (coordsOfVec n S x))
    (integralOutside_sub_rowRep S x hx)
  rwa [add_sub_cancel] at h

section Parts

variable {Z : Type} [MeasurableSpace Z] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ζ : Measure Z)
  (coord : Z → (Fin n → AdeleRing (𝓞 ℚ) ℚ))

private def pushed (ρ : Z → ℝ≥0) : Measure (CoordsVec n S) :=
  (ζ.withDensity fun z => (ρ z : ℝ≥0∞)).map (coordsOfVec n S ∘ coord)

private theorem isFiniteMeasure_pushed (_hcoord : Measurable coord) {ρ : Z → ℝ≥0} (hρ : ∫⁻ z, (ρ z : ℝ≥0∞) ∂ζ ≠ ∞) :
    IsFiniteMeasure (pushed S ζ coord ρ) := by
  haveI : IsFiniteMeasure (ζ.withDensity fun z => (ρ z : ℝ≥0∞)) := isFiniteMeasure_withDensity hρ
  unfold pushed
  infer_instance

private theorem integral_pushed (hcoord : Measurable coord) {ρ : Z → ℝ≥0} (hρm : AEMeasurable ρ ζ)
    {h : CoordsVec n S → ℂ} (hh : Measurable h) :
    ∫ y, h y ∂pushed S ζ coord ρ = ∫ z, h (coordsOfVec n S (coord z)) * ((ρ z : ℝ) : ℂ) ∂ζ := by
  unfold pushed
  rw [integral_map ((measurable_coordsOf S).comp hcoord).aemeasurable hh.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul₀ hρm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp, NNReal.smul_def, Complex.real_smul, mul_comm]

private theorem lintegral_pushed (hcoord : Measurable coord) {ρ : Z → ℝ≥0} (hρm : AEMeasurable ρ ζ)
    {b : CoordsVec n S → ℝ≥0∞} (hb : Measurable b) :
    ∫⁻ y, b y ∂pushed S ζ coord ρ = ∫⁻ z, (ρ z : ℝ≥0∞) * b (coordsOfVec n S (coord z)) ∂ζ := by
  unfold pushed
  rw [lintegral_map hb ((measurable_coordsOf S).comp hcoord)]
  exact (lintegral_withDensity_eq_lintegral_mul₀ hρm.coe_nnreal_ennreal
    (hb.comp ((measurable_coordsOf S).comp hcoord)).aemeasurable).trans rfl

end Parts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem pushed_eq_of_boxTests {Z : Type} [MeasurableSpace Z] (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ζ : Measure Z) (coord : Z → (Fin n → AdeleRing (𝓞 ℚ) ℚ)) (hcoord : Measurable coord) {ρ ρ' : Z → ℝ≥0}
    (hρ : ∫⁻ z, (ρ z : ℝ≥0∞) ∂ζ ≠ ∞) (hρ' : ∫⁻ z, (ρ' z : ℝ≥0∞) ∂ζ ≠ ∞)
    (hbox : ∀ (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0)
      (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)),
      (∀ i, φ i ∈ smoothFamily archCoord) → (∀ k, V k ∈ localCompactOpens k.2.1) →
      ∫⁻ y, boxTest φ V y ∂pushed S ζ coord ρ = ∫⁻ y, boxTest φ V y ∂pushed S ζ coord ρ') :
    pushed S ζ coord ρ = pushed S ζ coord ρ' := by
  haveI := isFiniteMeasure_pushed S ζ coord hcoord hρ
  haveI := isFiniteMeasure_pushed S ζ coord hcoord hρ'
  set μ : Measure (CoordsVec n S) := pushed S ζ coord ρ + pushed S ζ coord ρ' with hμ
  have hac : pushed S ζ coord ρ ≪ μ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hac' : pushed S ζ coord ρ' ≪ μ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hrn : μ.withDensity ((pushed S ζ coord ρ).rnDeriv μ) = pushed S ζ coord ρ :=
    Measure.withDensity_rnDeriv_eq _ _ hac
  have hrn' : μ.withDensity ((pushed S ζ coord ρ').rnDeriv μ) = pushed S ζ coord ρ' :=
    Measure.withDensity_rnDeriv_eq _ _ hac'
  have hmeas : ∀ (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0)
      (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)),
      (∀ i, φ i ∈ smoothFamily archCoord) → (∀ k, V k ∈ localCompactOpens k.2.1) → Measurable (boxTest φ V) :=
    fun φ V hφ hV => boxTest_measurable (fun i => smoothFamily_archCoord_measurable continuous_archCoord (hφ i))
      fun k => (hV k).2.measurableSet
  have hwd : ∀ {ν : Measure (CoordsVec n S)}, μ.withDensity (ν.rnDeriv μ) = ν →
      ∀ (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0) (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)),
      (∀ i, φ i ∈ smoothFamily archCoord) → (∀ k, V k ∈ localCompactOpens k.2.1) →
      ∫⁻ y, boxTest φ V y * ν.rnDeriv μ y ∂μ = ∫⁻ y, boxTest φ V y ∂ν := by
    intro ν hν φ V hφ hV
    conv_rhs => rw [← hν]
    rw [lintegral_withDensity_eq_lintegral_mul μ (Measure.measurable_rnDeriv _ _) (hmeas φ V hφ hV)]
    exact lintegral_congr fun y => mul_comm _ _
  choose sQ hsQ hsQ_mono hsQ_univ using fun k : Fin n × {p // p ∈ S} => exists_localExhaustion k.2.1
  have hae := ae_eq_of_boxTests μ (u := (pushed S ζ coord ρ).rnDeriv μ) (w := (pushed S ζ coord ρ').rnDeriv μ)
    (Measure.measurable_rnDeriv _ _) (Measure.measurable_rnDeriv _ _) archGenerators
    (archGenerate continuous_archCoord)
    archGenerators_piSystem archBalls archBalls_mem archBalls_mono archBalls_iUnion
    (fun k => localCompactOpens k.2.1)
    (fun k => localGenerate k.2.1) (fun k => localCompactOpens_piSystem k.2.1) sQ hsQ hsQ_mono hsQ_univ
    (smoothFamily archCoord) (fun _ hφ => smoothFamily_archCoord_measurable continuous_archCoord hφ)
    (fun _ hc => smoothFamily_approx archCoord hc) ?_ ?_
  · rw [← hrn, ← hrn', withDensity_congr_ae hae]
  · intro φ V hφ hV
    rw [hwd hrn φ V hφ hV, hwd hrn' φ V hφ hV]
    exact hbox φ V hφ hV
  · intro φ V hφ hV
    rw [hwd hrn' φ V hφ hV]
    choose K hK using fun i => smoothFamily_exists_compact (hφ i)
    refine ne_top_of_le_ne_top (measure_ne_top _ _)
      (lintegral_boxTest_le _ (fun i a => (hK i).2.2.1 a) (fun i a ha => (hK i).2.2.2 a ha) (fun i => (hK i).2.1)
        fun k => (hV k).2.measurableSet)

section Density

private theorem coe_toNNReal_sub_coe_toNNReal_neg (a : ℝ) : ((a.toNNReal : ℝ)) - ((-a).toNNReal : ℝ) = a := by
  rcases le_total 0 a with h | h
  · rw [Real.coe_toNNReal a h, Real.toNNReal_of_nonpos (neg_nonpos.2 h), NNReal.coe_zero, sub_zero]
  · rw [Real.toNNReal_of_nonpos h, Real.coe_toNNReal (-a) (neg_nonneg.2 h), NNReal.coe_zero, zero_sub, neg_neg]

private theorem density_eq_parts {Z : Type} (D : Z → ℂ) (z : Z) :
    D z = ((((D z).re.toNNReal : ℝ) : ℂ) - (((-(D z).re).toNNReal : ℝ) : ℂ)) +
      ((((D z).im.toNNReal : ℝ) : ℂ) - (((-(D z).im).toNNReal : ℝ) : ℂ)) * Complex.I := by
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, coe_toNNReal_sub_coe_toNNReal_neg, coe_toNNReal_sub_coe_toNNReal_neg]
  exact (Complex.re_add_im (D z)).symm

variable {Z : Type} [MeasurableSpace Z] {ζ : Measure Z}

private theorem toNNReal_re_le_nnnorm (w : ℂ) : w.re.toNNReal ≤ ‖w‖₊ := by
  rw [← Real.toNNReal_coe (r := ‖w‖₊), coe_nnnorm]
  exact Real.toNNReal_le_toNNReal (Complex.re_le_norm w)

private theorem toNNReal_neg_re_le_nnnorm (w : ℂ) : (-w.re).toNNReal ≤ ‖w‖₊ := by
  rw [← Real.toNNReal_coe (r := ‖w‖₊), coe_nnnorm]
  exact Real.toNNReal_le_toNNReal (by simpa using Complex.re_le_norm (-w))

private theorem toNNReal_im_le_nnnorm (w : ℂ) : w.im.toNNReal ≤ ‖w‖₊ := by
  rw [← Real.toNNReal_coe (r := ‖w‖₊), coe_nnnorm]
  exact Real.toNNReal_le_toNNReal (Complex.im_le_norm w)

private theorem toNNReal_neg_im_le_nnnorm (w : ℂ) : (-w.im).toNNReal ≤ ‖w‖₊ := by
  rw [← Real.toNNReal_coe (r := ‖w‖₊), coe_nnnorm]
  exact Real.toNNReal_le_toNNReal (by simpa using Complex.im_le_norm (-w))

private theorem lintegral_part_ne_top {D : Z → ℂ} (hD : Integrable D ζ) {ρ : Z → ℝ≥0} (hρ : ∀ z, ρ z ≤ ‖D z‖₊) :
    ∫⁻ z, (ρ z : ℝ≥0∞) ∂ζ ≠ ∞ :=
  ne_top_of_le_ne_top hD.2.ne (lintegral_mono fun z => by
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (mod_cast hρ z))

private theorem integrable_part {D : Z → ℂ} (hD : Integrable D ζ) {ρ : Z → ℝ≥0} (hρm : AEMeasurable ρ ζ)
    (hρ : ∀ z, ρ z ≤ ‖D z‖₊) : Integrable (fun z => ((ρ z : ℝ) : ℂ)) ζ := by
  refine Integrable.mono hD (Complex.continuous_ofReal.measurable.comp_aemeasurable
    (NNReal.continuous_coe.measurable.comp_aemeasurable hρm)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ρ z).coe_nonneg, ← coe_nnnorm]
  exact_mod_cast hρ z

private theorem integral_mul_density_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (coord : Z → (Fin n → AdeleRing (𝓞 ℚ) ℚ))
    (hcoord : Measurable coord) {D : Z → ℂ} (hD : Integrable D ζ) {h : CoordsVec n S → ℂ} (hh : Measurable h)
    (hhb : ∃ C : ℝ, ∀ y, ‖h y‖ ≤ C) :
    ∫ z, h (coordsOfVec n S (coord z)) * D z ∂ζ =
      (∫ y, h y ∂pushed S ζ coord (fun z => (D z).re.toNNReal) -
          ∫ y, h y ∂pushed S ζ coord (fun z => (-(D z).re).toNNReal)) +
        (∫ y, h y ∂pushed S ζ coord (fun z => (D z).im.toNNReal) -
          ∫ y, h y ∂pushed S ζ coord (fun z => (-(D z).im).toNNReal)) * Complex.I := by
  have hDm : AEMeasurable D ζ := hD.aemeasurable
  have h1 : AEMeasurable (fun z => (D z).re.toNNReal) ζ :=
    measurable_real_toNNReal.comp_aemeasurable (Complex.measurable_re.comp_aemeasurable hDm)
  have h2 : AEMeasurable (fun z => (-(D z).re).toNNReal) ζ :=
    measurable_real_toNNReal.comp_aemeasurable (Complex.measurable_re.comp_aemeasurable hDm).neg
  have h3 : AEMeasurable (fun z => (D z).im.toNNReal) ζ :=
    measurable_real_toNNReal.comp_aemeasurable (Complex.measurable_im.comp_aemeasurable hDm)
  have h4 : AEMeasurable (fun z => (-(D z).im).toNNReal) ζ :=
    measurable_real_toNNReal.comp_aemeasurable (Complex.measurable_im.comp_aemeasurable hDm).neg
  rw [integral_pushed S ζ coord hcoord h1 hh, integral_pushed S ζ coord hcoord h2 hh,
    integral_pushed S ζ coord hcoord h3 hh, integral_pushed S ζ coord hcoord h4 hh]
  have hhm : AEStronglyMeasurable (fun z => h (coordsOfVec n S (coord z))) ζ :=
    (hh.comp ((measurable_coordsOf S).comp hcoord)).aestronglyMeasurable
  obtain ⟨C, hC⟩ := hhb
  have hi : ∀ {ρ : Z → ℝ≥0}, AEMeasurable ρ ζ → (∀ z, ρ z ≤ ‖D z‖₊) →
      Integrable (fun z => h (coordsOfVec n S (coord z)) * ((ρ z : ℝ) : ℂ)) ζ :=
    fun hρm hρ => (integrable_part hD hρm hρ).bdd_mul hhm (Filter.Eventually.of_forall fun z => hC _)
  rw [← integral_sub (hi h1 fun z => toNNReal_re_le_nnnorm (D z)) (hi h2 fun z => toNNReal_neg_re_le_nnnorm (D z)),
    ← integral_sub (hi h3 fun z => toNNReal_im_le_nnnorm (D z)) (hi h4 fun z => toNNReal_neg_im_le_nnnorm (D z)),
    ← integral_mul_const, ← integral_add]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    linear_combination (h (coordsOfVec n S (coord z))) * density_eq_parts D z
  · exact (hi h1 fun z => toNNReal_re_le_nnnorm (D z)).sub (hi h2 fun z => toNNReal_neg_re_le_nnnorm (D z))
  · exact ((hi h3 fun z => toNNReal_im_le_nnnorm (D z)).sub
      (hi h4 fun z => toNNReal_neg_im_le_nnnorm (D z))).mul_const _

end Density
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section BoxLift

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ)))

private def boxNN (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (y : CoordsVec n S) : ℝ≥0 :=
  (∏ i, φ i (y.1 i)) * ∏ k, (V k).indicator (fun _ => (1 : ℝ≥0)) (y.2 k)

private theorem boxTest_eq_boxNN (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (y : CoordsVec n S) :
    boxTest φ V y = (boxNN S φ V y : ℝ≥0∞) :=
  rfl

private def boxC (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (y : CoordsVec n S) : ℂ :=
  ((boxNN S φ V y : ℝ) : ℂ)

private theorem measurable_boxNN {φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    {V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)} (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    Measurable (boxNN S φ V) := by
  have h := boxTest_measurable (fun i => smoothFamily_archCoord_measurable continuous_archCoord (hφ i))
    (fun k => (hV k).2.measurableSet) (φ := φ) (V := V)
  exact measurable_coe_nnreal_ennreal_iff.1 h

private theorem measurable_boxC {φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    {V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)} (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    Measurable (boxC S φ V) :=
  Complex.continuous_ofReal.measurable.comp (NNReal.continuous_coe.measurable.comp (measurable_boxNN S hφ hV))

private theorem boxNN_le_one {φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (y : CoordsVec n S) : boxNN S φ V y ≤ 1 := by
  unfold boxNN
  refine mul_le_one' (Finset.prod_le_one' fun i _ => (smoothFamily_exists_compact (hφ i)).choose_spec.2.2.1 _)
    (Finset.prod_le_one' fun k _ => ?_)
  by_cases h : y.2 k ∈ V k <;> simp [h]

private theorem norm_boxC_le_one {φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (y : CoordsVec n S) : ‖boxC S φ V y‖ ≤ 1 := by
  unfold boxC
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (boxNN S φ V y).coe_nonneg]
  exact_mod_cast boxNN_le_one S hφ V y

private theorem prod_testFactorC_eq_boxC (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin n → AdeleRing (𝓞 ℚ) ℚ)
    (hx : ∀ i, IntegralOutsideAll S (x i)) :
    (∏ i, testFactorC S (φ i) (fun v => V (i, v)) (x i)) = boxC S φ V (coordsOfVec n S x) := by
  have hfin : ∀ i, finPart S (fun v => V (i, v)) (x i).2 =
      ∏ v : {p // p ∈ S}, (V (i, v)).indicator (fun _ => (1 : ℝ≥0)) ((x i).2 v.1) := by
    intro i
    unfold finPart
    rw [if_pos (show ∀ v ∉ S, (x i).2 v ∈ v.adicCompletionIntegers ℚ from fun q hq => hx i q hq),
      mul_one]
  simp only [testFactorC, testFactor, hfin, boxC, boxNN]
  rw [← Complex.ofReal_prod, ← NNReal.coe_prod, Finset.prod_mul_distrib, Fintype.prod_prod_type]
  rfl

end BoxLift
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem pushed_parts_eq {Z : Type} [MeasurableSpace Z] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ζ : Measure Z)
    (coord : Z → (Fin n → AdeleRing (𝓞 ℚ) ℚ)) (hcoord : Measurable coord) {D : Z → ℂ} (hD : Integrable D ζ)
    (hsupp : ∀ z, D z ≠ 0 → ∀ i, IntegralOutsideAll S (coord z i))
    (hvan : ∀ (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0) (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)),
      (∀ i, φ i ∈ smoothFamily archCoord) → (∀ k, V k ∈ localCompactOpens k.2.1) →
      ∫ z, (∏ i, testFactorC S (φ i) (fun v => V (i, v)) (coord z i)) * D z ∂ζ = 0) :
    pushed S ζ coord (fun z => (D z).re.toNNReal) = pushed S ζ coord (fun z => (-(D z).re).toNNReal) ∧
      pushed S ζ coord (fun z => (D z).im.toNNReal) = pushed S ζ coord (fun z => (-(D z).im).toNNReal) := by

  have hbox : ∀ (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0) (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)),
      (∀ i, φ i ∈ smoothFamily archCoord) → (∀ k, V k ∈ localCompactOpens k.2.1) →
      (∫ y, boxC S φ V y ∂pushed S ζ coord (fun z => (D z).re.toNNReal) -
          ∫ y, boxC S φ V y ∂pushed S ζ coord (fun z => (-(D z).re).toNNReal)) +
        (∫ y, boxC S φ V y ∂pushed S ζ coord (fun z => (D z).im.toNNReal) -
          ∫ y, boxC S φ V y ∂pushed S ζ coord (fun z => (-(D z).im).toNNReal)) * Complex.I = 0 := by
    intro φ V hφ hV
    rw [← integral_mul_density_eq S coord hcoord hD (measurable_boxC S hφ hV) ⟨1, norm_boxC_le_one S hφ V⟩,
      ← hvan φ V hφ hV]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    by_cases hz : D z = 0
    · rw [hz, mul_zero, mul_zero]
    · rw [prod_testFactorC_eq_boxC S φ V (coord z) (hsupp z hz)]

  have hreal : ∀ (ρ : Z → ℝ≥0) (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0)
      (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)),
      ∫ y, boxC S φ V y ∂pushed S ζ coord ρ = ((∫ y, (boxNN S φ V y : ℝ) ∂pushed S ζ coord ρ : ℝ) : ℂ) :=
    fun ρ φ V => integral_ofReal
  have hlin : ∀ (ρ : Z → ℝ≥0) (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0)
      (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)), (∀ i, φ i ∈ smoothFamily archCoord) →
      (∀ k, V k ∈ localCompactOpens k.2.1) → (∀ z, ρ z ≤ ‖D z‖₊) →
      ∫⁻ y, boxTest φ V y ∂pushed S ζ coord ρ = ENNReal.ofReal (∫ y, (boxNN S φ V y : ℝ) ∂pushed S ζ coord ρ) := by
    intro ρ φ V hφ hV hρ
    haveI := isFiniteMeasure_pushed S ζ coord hcoord (lintegral_part_ne_top hD hρ)
    rw [ofReal_integral_eq_lintegral_ofReal]
    · simp only [boxTest_eq_boxNN, ENNReal.ofReal_coe_nnreal]
    · refine Integrable.of_bound
        ((NNReal.continuous_coe.measurable.comp (measurable_boxNN S hφ hV)).aestronglyMeasurable) 1
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (boxNN S φ V y).coe_nonneg]
      exact_mod_cast boxNN_le_one S hφ V y
    · exact Filter.Eventually.of_forall fun y => (boxNN S φ V y).coe_nonneg
  refine ⟨pushed_eq_of_boxTests S ζ coord hcoord (lintegral_part_ne_top hD fun z => toNNReal_re_le_nnnorm (D z))
      (lintegral_part_ne_top hD fun z => toNNReal_neg_re_le_nnnorm (D z)) fun φ V hφ hV => ?_,
    pushed_eq_of_boxTests S ζ coord hcoord (lintegral_part_ne_top hD fun z => toNNReal_im_le_nnnorm (D z))
      (lintegral_part_ne_top hD fun z => toNNReal_neg_im_le_nnnorm (D z)) fun φ V hφ hV => ?_⟩
  · have h := congrArg Complex.re (hbox φ V hφ hV)
    simp only [hreal, Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.sub_im, Complex.ofReal_im, sub_self, mul_zero, zero_mul, add_zero, Complex.zero_re] at h
    rw [hlin _ φ V hφ hV fun z => toNNReal_re_le_nnnorm (D z),
      hlin _ φ V hφ hV fun z => toNNReal_neg_re_le_nnnorm (D z), sub_eq_zero.1 h]
  · have h := congrArg Complex.im (hbox φ V hφ hV)
    simp only [hreal, Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.sub_re, Complex.ofReal_re, sub_self, mul_zero, mul_one, zero_add, add_zero, Complex.zero_im] at h
    rw [hlin _ φ V hφ hV fun z => toNNReal_im_le_nnnorm (D z),
      hlin _ φ V hφ hV fun z => toNNReal_neg_im_le_nnnorm (D z), sub_eq_zero.1 h]

section Support

open NumberField.AdelicFourier

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar secondCountableAdeles

private theorem testFactor_add_of_integralOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (φ : InfiniteAdeleRing ℚ → ℝ≥0)
    (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)) (a : AdeleRing (𝓞 ℚ) ℚ) {u : AdeleRing (𝓞 ℚ) ℚ}
    (hu : IntegralOutside S u) : testFactor S φ W (a + u) = testFactor S φ W a := by
  obtain ⟨hint, hS, harch⟩ := hu
  have h1 : (a + u).1 = a.1 := by
    change a.1 + u.1 = a.1
    rw [show u.1 = 0 from harch, add_zero]
  unfold testFactor finPart
  rw [h1]
  congr 1
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    change (W v).indicator _ (a.2 v.1 + u.2 v.1) = (W v).indicator _ (a.2 v.1)
    rw [show u.2 v.1 = 0 from hS v.1 v.2, add_zero]
  · refine if_congr (forall_congr' fun v => imp_congr_right fun hv => ?_) rfl rfl
    change a.2 v + u.2 v ∈ v.adicCompletionIntegers ℚ ↔ a.2 v ∈ v.adicCompletionIntegers ℚ
    exact add_mem_cancel_right (hint v hv)

private theorem fourierIntegral_eq_zero_of_invariant {Φ : AdeleRing (𝓞 ℚ) ℚ → ℂ} (u : AdeleRing (𝓞 ℚ) ℚ)
    (hΦ : ∀ a, Φ (a + u) = Φ a) (t : AdeleRing (𝓞 ℚ) ℚ) (ht : psiQ (-(u * t)) ≠ 1) :
    fourierIntegral psiQ (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) Φ t = 0 := by
  set μ := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ
  have key : fourierIntegral psiQ μ Φ t = psiQ (-(u * t)) * fourierIntegral psiQ μ Φ t := by
    conv_lhs => rw [fourierIntegral_def, ← integral_add_right_eq_self (fun v => psiQ (-(v * t)) * Φ v) u]
    rw [fourierIntegral_def, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only
    rw [hΦ v, add_mul, neg_add, AddChar.map_add_eq_mul]
    ring
  have h : (1 - psiQ (-(u * t))) * fourierIntegral psiQ μ Φ t = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h).symm ht
  · exact h

private theorem exists_psiV_intCast_mul_ne_one (q : HeightOneSpectrum (𝓞 ℚ)) {x : q.adicCompletion ℚ}
    (hx : x ∉ q.adicCompletionIntegers ℚ) :
    ∃ m : 𝓞 ℚ, psiV q (algebraMap ℚ (q.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ m) * x) ≠ 1 := by
  set π : q.adicCompletion ℚ :=
    algebraMap ℚ (q.adicCompletion ℚ) ((Rat.HeightOneSpectrum.natGenerator q : ℕ) : ℚ) with hπdef
  have hx0 : x ≠ 0 := fun h => hx (h ▸ zero_mem _)
  have hπv : Valued.v π = WithZero.exp (-1 : ℤ) := by
    rw [hπdef, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', RatIdele.valuation_natGenerator]
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπv
    exact WithZero.exp_ne_zero hπv.symm
  have hxv : 1 < Valued.v x := by
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hx

  have hz : π⁻¹ * x⁻¹ ∈ q.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, map_inv₀, hπv]
    have hn := WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx0 : Valued.v x ≠ 0)
    rw [← hn] at hxv ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hxv
    rw [← WithZero.exp_neg, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨m, hm⟩ :=
    NumberField.AdelicBox.exists_valued_algebraMap_sub_lt (𝓞 ℚ) ℚ q ⟨π⁻¹ * x⁻¹, hz⟩ x⁻¹ (inv_ne_zero hx0)
  refine ⟨m, ?_⟩
  set r : q.adicCompletion ℚ := algebraMap ℚ (q.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ m) with hrdef
  have hsplit : r * x = π⁻¹ + (r - π⁻¹ * x⁻¹) * x := by
    field_simp
    ring
  have hint : (r - π⁻¹ * x⁻¹) * x ∈ q.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul]
    have hx' : Valued.v x⁻¹ * Valued.v x = 1 := by
      rw [map_inv₀, inv_mul_cancel₀ ((Valuation.ne_zero_iff _).2 hx0)]
    calc Valued.v (r - π⁻¹ * x⁻¹) * Valued.v x ≤ Valued.v x⁻¹ * Valued.v x :=
          mul_le_mul_left (le_of_lt hm) _
      _ = 1 := hx'
  rw [hsplit, AddChar.map_add_eq_mul, psiV_eq_one_of_mem_integers q hint, mul_one, hπdef, ← map_inv₀]
  exact psiV_algebraMap_inv_ne_one q

private theorem exists_integralOutside_psiQ_mul_ne_one (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {t : AdeleRing (𝓞 ℚ) ℚ}
    (ht : ¬ IntegralOutsideAll S t) : ∃ u : AdeleRing (𝓞 ℚ) ℚ, IntegralOutside S u ∧ psiQ (-(u * t)) ≠ 1 := by
  unfold IntegralOutsideAll at ht
  simp only [not_forall] at ht
  obtain ⟨q, hqS, hq⟩ := ht
  obtain ⟨m, hm⟩ := exists_psiV_intCast_mul_ne_one q hq
  classical
  refine ⟨((0 : InfiniteAdeleRing ℚ), singlePlaceAdele q (algebraMap (𝓞 ℚ) ℚ m)),
    ⟨fun p _ => ?_, fun p hp => ?_, rfl⟩, ?_⟩
  · change (singlePlaceAdele q (algebraMap (𝓞 ℚ) ℚ m)) p ∈ p.adicCompletionIntegers ℚ
    rw [singlePlaceAdele_apply]
    split_ifs with hpq
    · subst hpq
      exact NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers (𝓞 ℚ) ℚ p m
    · exact zero_mem _
  · change (singlePlaceAdele q (algebraMap (𝓞 ℚ) ℚ m)) p = 0
    rw [singlePlaceAdele_apply, if_neg]
    rintro rfl
    exact hqS hp
  · rw [AddChar.map_neg_eq_inv, inv_ne_one, psiQ_apply]
    change psiArch (0 * t.1) * psiFin (singlePlaceAdele q (algebraMap (𝓞 ℚ) ℚ m) * t.2) ≠ 1
    rw [zero_mul, AddChar.map_zero_eq_one, one_mul, psiFin_apply]
    rw [finprod_eq_single (fun w => psiV w ((singlePlaceAdele q (algebraMap (𝓞 ℚ) ℚ m) * t.2) w)) q]
    · change psiV q ((singlePlaceAdele q (algebraMap (𝓞 ℚ) ℚ m)) q * t.2 q) ≠ 1
      rwa [singlePlaceAdele_apply, if_pos rfl]
    · intro w hw
      change psiV w ((singlePlaceAdele q (algebraMap (𝓞 ℚ) ℚ m)) w * t.2 w) = 1
      rw [singlePlaceAdele_apply, if_neg hw, zero_mul, AddChar.map_zero_eq_one]

private theorem fourierIntegral_testFactorC_eq_zero (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (φ : InfiniteAdeleRing ℚ → ℝ≥0)
    (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)) {t : AdeleRing (𝓞 ℚ) ℚ} (ht : ¬ IntegralOutsideAll S t) :
    fourierIntegral psiQ (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (testFactorC S φ W) t = 0 := by
  obtain ⟨u, hu, hut⟩ := exists_integralOutside_psiQ_mul_ne_one S ht
  refine fourierIntegral_eq_zero_of_invariant u (fun a => ?_) t hut
  unfold testFactorC
  rw [testFactor_add_of_integralOutside S φ W a hu]

end Support
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Inversion

open NumberField.AdelicFourier

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar secondCountableAdeles

private theorem psiQ_neg_dotProduct (c t : Fin n → AdeleRing (𝓞 ℚ) ℚ) :
    psiQ (-(t ⬝ᵥ c)) = ∏ i, psiQ (-(t i * c i)) := by
  unfold dotProduct
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, neg_zero, AddChar.map_zero_eq_one, Finset.prod_empty]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, neg_add, AddChar.map_add_eq_mul, ih]

private theorem prod_testFactorC_neg_eq_integral (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0)
    (hφ : ∀ i, φ i ∈ smoothFamily archCoord) (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ))
    (hV : ∀ k, V k ∈ localCompactOpens k.2.1) (c : Fin n → AdeleRing (𝓞 ℚ) ℚ) :
    ((((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (NumberField.AdelicBox.adelicBox ℚ)).toReal : ℂ) ^ 2) ^ n *
        ∏ i, testFactorC S (φ i) (fun v => V (i, v)) (-(c i)) =
      ∫ t, psiQ (-(c ⬝ᵥ t)) * ∏ i, fourierIntegral psiQ (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
          (testFactorC S (φ i) (fun v => V (i, v))) (t i)
        ∂(Measure.pi fun _ : Fin n => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by
  set μ := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ
  have hmem : ∀ i, testFactorC S (φ i) (fun v => V (i, v)) ∈ schwartzBruhat ℚ := fun i =>
    mem_schwartzBruhat_of_mem_pureTensorSet (testFactorC_mem_pureTensorSet S (hφ i) fun v => hV (i, v))

  have hinv : ∀ i, (((μ (NumberField.AdelicBox.adelicBox ℚ)).toReal : ℂ) ^ 2) *
        testFactorC S (φ i) (fun v => V (i, v)) (-(c i)) =
      ∫ s, psiQ (-(s * c i)) * fourierIntegral psiQ μ (testFactorC S (φ i) (fun v => V (i, v))) s ∂μ := fun i =>
    (fourierIntegral_fourierIntegral_eq ℚ μ (isGlobalAddChar_psiQ) (hmem i) (c i)).symm
  rw [show ((((μ (NumberField.AdelicBox.adelicBox ℚ)).toReal : ℂ) ^ 2) ^ n) =
      ∏ _i : Fin n, ((μ (NumberField.AdelicBox.adelicBox ℚ)).toReal : ℂ) ^ 2 by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
    ← Finset.prod_mul_distrib]
  simp_rw [hinv]
  rw [← integral_fintype_prod_eq_prod (ι := Fin n) (f := fun i (s : AdeleRing (𝓞 ℚ) ℚ) =>
      psiQ (-(s * c i)) * fourierIntegral psiQ μ (testFactorC S (φ i) (fun v => V (i, v))) s)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [Finset.prod_mul_distrib, dotProduct_comm, psiQ_neg_dotProduct]

private theorem integrable_prod_fourierIntegral (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0)
    (hφ : ∀ i, φ i ∈ smoothFamily archCoord) (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ))
    (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    Integrable (fun t : Fin n → AdeleRing (𝓞 ℚ) ℚ => ∏ i,
        fourierIntegral psiQ (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
          (testFactorC S (φ i) (fun v => V (i, v))) (t i))
      (Measure.pi fun _ : Fin n => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
  Integrable.fintype_prod fun i => integrable_of_mem_schwartzBruhat ℚ _ (fourierIntegral_mem_schwartzBruhat_psiQ _
    (mem_schwartzBruhat_of_mem_pureTensorSet (testFactorC_mem_pureTensorSet S (hφ i) fun v => hV (i, v))))

private theorem measurableSet_integralOutsideAll (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    MeasurableSet {s : AdeleRing (𝓞 ℚ) ℚ | IntegralOutsideAll S s} := by
  have : {s : AdeleRing (𝓞 ℚ) ℚ | IntegralOutsideAll S s} =
      ⋂ q ∈ {q : HeightOneSpectrum (𝓞 ℚ) | q ∉ S},
        evalHom q ⁻¹' (q.adicCompletionIntegers ℚ : Set (q.adicCompletion ℚ)) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  rw [this]
  refine MeasurableSet.biInter (Set.to_countable _) fun q _ => ?_
  exact (continuous_evalHom q).measurable (AdelicLevel.isClosed_adicCompletionIntegers (K := ℚ) q).measurableSet

private theorem inversion_step {Z : Type} [MeasurableSpace Z] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ζ : Measure Z)
    [SFinite ζ] (coord : Z → (Fin n → AdeleRing (𝓞 ℚ) ℚ)) (hcoord : Measurable coord) {D : Z → ℂ} (hD : Integrable D ζ)
    (hcoef : ∀ᵐ t ∂(Measure.pi fun _ : Fin n =>
        (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s}),
      ∫ z, psiQ (-(coord z ⬝ᵥ t)) * D z ∂ζ = 0)
    (φ : Fin n → InfiniteAdeleRing ℚ → ℝ≥0) (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    (V : ∀ k : Fin n × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    ∫ z, (∏ i, testFactorC S (φ i) (fun v => V (i, v)) (-(coord z i))) * D z ∂ζ = 0 := by
  classical
  set μ := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ with hμ
  set μn : Measure (Fin n → AdeleRing (𝓞 ℚ) ℚ) := Measure.pi fun _ : Fin n => μ with hμn
  set G : (Fin n → AdeleRing (𝓞 ℚ) ℚ) → ℂ := fun t =>
    ∏ i, NumberField.AdelicFourier.fourierIntegral psiQ μ (testFactorC S (φ i) (fun v => V (i, v))) (t i) with hG
  set cbox : ℂ := (((μ (NumberField.AdelicBox.adelicBox ℚ)).toReal : ℂ) ^ 2) ^ n with hcbox
  have hcbox0 : cbox ≠ 0 := by
    rw [hcbox]
    refine pow_ne_zero _ (pow_ne_zero _ ?_)
    exact_mod_cast (ENNReal.toReal_pos (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
      (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne).ne'

  suffices h : cbox * ∫ z, (∏ i, testFactorC S (φ i) (fun v => V (i, v)) (-(coord z i))) * D z ∂ζ = 0 from
    (mul_eq_zero.1 h).resolve_left hcbox0
  have hG_int : Integrable G μn := integrable_prod_fourierIntegral S φ hφ V hV
  have hGsupp : ∀ t, G t ≠ 0 → ∀ i, IntegralOutsideAll S (t i) := by
    intro t ht i
    by_contra hti
    exact ht (Finset.prod_eq_zero (Finset.mem_univ i) (fourierIntegral_testFactorC_eq_zero S (φ i) _ hti))

  have hprod : Integrable
      (fun zt : Z × (Fin n → AdeleRing (𝓞 ℚ) ℚ) => psiQ (-(coord zt.1 ⬝ᵥ zt.2)) * (D zt.1 * G zt.2))
      (ζ.prod μn) := by
    refine (hD.mul_prod hG_int).bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun zt => le_of_eq ?_)
    · refine (Continuous.measurable ?_).comp_aemeasurable ?_ |>.aestronglyMeasurable
      · exact NumberField.StandardAddChar.continuous_psiQ
      · exact (measurable_neg.comp (Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp (hcoord.comp
          measurable_fst)).mul ((measurable_pi_apply i).comp measurable_snd))).aemeasurable
    · exact norm_apply_eq_one_of_isGlobalAddChar ℚ isGlobalAddChar_psiQ _
  calc cbox * ∫ z, (∏ i, testFactorC S (φ i) (fun v => V (i, v)) (-(coord z i))) * D z ∂ζ
      = ∫ z, (∫ t, psiQ (-(coord z ⬝ᵥ t)) * G t ∂μn) * D z ∂ζ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [← mul_assoc, prod_testFactorC_neg_eq_integral S φ hφ V hV (coord z)]
    _ = ∫ z, ∫ t, psiQ (-(coord z ⬝ᵥ t)) * (D z * G t) ∂μn ∂ζ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        ring
    _ = ∫ t, ∫ z, psiQ (-(coord z ⬝ᵥ t)) * (D z * G t) ∂ζ ∂μn := integral_integral_swap hprod
    _ = ∫ t, G t * ∫ z, psiQ (-(coord z ⬝ᵥ t)) * D z ∂ζ ∂μn := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        ring
    _ = 0 := by

        rw [← integral_zero (Fin n → AdeleRing (𝓞 ℚ) ℚ) ℂ (μ := μn)]
        refine integral_congr_ae ?_
        have hres : μn.restrict (Set.univ.pi fun _ : Fin n => {s : AdeleRing (𝓞 ℚ) ℚ | IntegralOutsideAll S s}) =
            Measure.pi fun _ : Fin n => μ.restrict {s | IntegralOutsideAll S s} :=
          Measure.restrict_pi_pi _ _
        rw [← hres, ae_restrict_iff' (MeasurableSet.univ_pi fun _ => measurableSet_integralOutsideAll S)] at hcoef
        filter_upwards [hcoef] with t ht
        by_cases hGt : G t = 0
        · rw [hGt, zero_mul]
        · rw [ht (by simpa only [Set.mem_univ_pi, Set.mem_setOf_eq] using hGsupp t hGt), mul_zero]

end Inversion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem integralOutsideAll_neg (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {x : AdeleRing (𝓞 ℚ) ℚ}
    (hx : IntegralOutsideAll S x) : IntegralOutsideAll S (-x) := fun q hq => by
  rw [map_neg]
  exact neg_mem (hx q hq)

private theorem integralOutside_neg (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {u : AdeleRing (𝓞 ℚ) ℚ}
    (hu : IntegralOutside S u) : IntegralOutside S (-u) :=
  ⟨fun q hq => by rw [map_neg]; exact neg_mem (hu.1 q hq), fun q hq => by rw [map_neg, hu.2.1 q hq, neg_zero],
    by rw [map_neg, hu.2.2, neg_zero]⟩

private theorem measurable_neg_rows {n : ℕ} : Measurable fun x : Fin n → AdeleRing (𝓞 ℚ) ℚ => -x :=
  measurable_neg

end CoefficientVanishing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Engine

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private theorem integral_mul_eq_zero_of_coefficients {Z : Type} [MeasurableSpace Z]
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) (ζ : Measure Z) [SFinite ζ]
    (coord : Z → (Fin n → AdeleRing (𝓞 ℚ) ℚ)) (hcoord : Measurable coord)
    (D : Z → ℂ) (hD : Integrable D ζ)
    (hsupp : ∀ z, D z ≠ 0 → ∀ i, IntegralOutsideAll S (coord z i))
    (hcoef : ∀ᵐ t ∂(Measure.pi fun _ : Fin n =>
        (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s}),
      ∫ z, NumberField.StandardAddChar.psiQ (-(coord z ⬝ᵥ t)) * D z ∂ζ = 0)
    (g : (Fin n → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (hg : Measurable g) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (hginv : ∀ x u, (∀ i, IntegralOutside S (u i)) → g (x + u) = g x) :
    ∫ z, g (coord z) * D z ∂ζ = 0 := by

  have hsupp' : ∀ z, D z ≠ 0 → ∀ i, IntegralOutsideAll S ((-coord z) i) :=
    fun z hz i => integralOutsideAll_neg S (hsupp z hz i)
  have hginv' : ∀ x u, (∀ i, IntegralOutside S (u i)) → (g ∘ Neg.neg) (x + u) = (g ∘ Neg.neg) x := by
    intro x u hu
    simp only [Function.comp, neg_add_rev, add_comm (-u) (-x)]
    exact hginv (-x) (-u) fun i => integralOutside_neg S (hu i)

  obtain ⟨h12, h34⟩ := pushed_parts_eq S ζ (fun z => -coord z) (measurable_neg_rows.comp hcoord) hD hsupp'
    fun φ V hφ hV => inversion_step S ζ coord hcoord hD hcoef φ hφ V hV

  have hg' : (fun z => g (coord z) * D z) =
      fun z => ((g ∘ Neg.neg) ∘ rowRepVec n S) (coordsOfVec n S (-coord z)) * D z := by
    funext z
    show g (coord z) * D z = (g ∘ Neg.neg) (rowRepVec n S (coordsOfVec n S (-coord z))) * D z
    by_cases hz : D z = 0
    · rw [hz, mul_zero, mul_zero]
    · rw [← eq_comp_rowRep_of_invariant S (g ∘ Neg.neg) hginv' (-coord z) (hsupp' z hz)]
      simp only [Function.comp, neg_neg]
  rw [hg', integral_mul_density_eq S (fun z => -coord z) (measurable_neg_rows.comp hcoord) hD
    (h := (g ∘ Neg.neg) ∘ rowRepVec n S) ((hg.comp measurable_neg_rows).comp (measurable_rowRepVec S)) ?_,
    h12, h34, sub_self, sub_self, zero_mul, add_zero]
  obtain ⟨C, hC⟩ := hgb
  exact ⟨C, fun y => hC _⟩

private theorem coefficient_eq_zero_of_forall_zeroOutside {Z : Type} [MeasurableSpace Z]
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) (ζ : Measure Z)
    (coord : Z → (Fin n → AdeleRing (𝓞 ℚ) ℚ)) (D : Z → ℂ)
    (hsupp : ∀ z, D z ≠ 0 → ∀ i, IntegralOutsideAll S (coord z i))
    (hcoef : ∀ t : Fin n → AdeleRing (𝓞 ℚ) ℚ, (∀ i, ZeroOutside S (t i)) →
      ∫ z, NumberField.StandardAddChar.psiQ (-(coord z ⬝ᵥ t)) * D z ∂ζ = 0)
    (t : Fin n → AdeleRing (𝓞 ℚ) ℚ) (ht : ∀ i, IntegralOutsideAll S (t i)) :
    ∫ z, NumberField.StandardAddChar.psiQ (-(coord z ⬝ᵥ t)) * D z ∂ζ = 0 := by
  have hker : (fun z => NumberField.StandardAddChar.psiQ (-(coord z ⬝ᵥ t)) * D z) =
      fun z => NumberField.StandardAddChar.psiQ (-(coord z ⬝ᵥ fun i => headAdele S (t i))) * D z := by
    funext z
    by_cases hz : D z = 0
    · simp only [hz, mul_zero]
    · rw [kernel_eq_head S (coord z) t (hsupp z hz) ht]
  rw [hker]
  exact hcoef _ fun i q hq => evalHom_headAdele_of_notMem S (t i) hq

end Engine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end MirabolicLeviFibration
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end CoefficientEngine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section TorusDilation

noncomputable section

namespace MirabolicLeviFibration

section Parameters

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end Parameters
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Representative

open scoped Classical

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

end Representative
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UnitRepresentative

open scoped Classical

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private def RepUnitLocus (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  (∀ w : InfinitePlace ℚ, AdelicLevel.adeleArch (𝓞 ℚ) ℚ b w ≠ 0) ∧ ∀ p ∈ S, evalHom p b ≠ 0

private theorem repUnitLocus_add_iff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b u : AdeleRing (𝓞 ℚ) ℚ)
    (hu : IntegralOutside S u) : RepUnitLocus S (b + u) ↔ RepUnitLocus S b := by
  have h₁ : ∀ w : InfinitePlace ℚ,
      AdelicLevel.adeleArch (𝓞 ℚ) ℚ (b + u) w = AdelicLevel.adeleArch (𝓞 ℚ) ℚ b w := by
    intro w
    rw [map_add, hu.2.2, add_zero]
  have h₂ : ∀ p ∈ S, evalHom p (b + u) = evalHom p b := by
    intro p hp
    rw [map_add, hu.2.1 p hp, add_zero]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨fun w => ?_, fun p hp => ?_⟩
    · rw [← h₁ w]
      exact ha w
    · rw [← h₂ p hp]
      exact hb p hp
  · rintro ⟨ha, hb⟩
    refine ⟨fun w => ?_, fun p hp => ?_⟩
    · rw [h₁ w]
      exact ha w
    · rw [h₂ p hp]
      exact hb p hp

private theorem isOpen_repUnitLocus (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    IsOpen {b : AdeleRing (𝓞 ℚ) ℚ | RepUnitLocus S b} := by
  have h : {b : AdeleRing (𝓞 ℚ) ℚ | RepUnitLocus S b} =
      (⋂ w : InfinitePlace ℚ, {b : AdeleRing (𝓞 ℚ) ℚ | AdelicLevel.adeleArch (𝓞 ℚ) ℚ b w ≠ 0}) ∩
        ⋂ p ∈ S, {b : AdeleRing (𝓞 ℚ) ℚ | evalHom p b ≠ 0} := by
    ext b
    simp only [RepUnitLocus, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h]
  refine IsOpen.inter (isOpen_iInter_of_finite fun w => ?_) (Set.Finite.isOpen_biInter S.finite_toSet fun p _ => ?_)
  · exact isOpen_ne.preimage ((continuous_apply w).comp (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ))
  · exact isOpen_ne.preimage (continuous_evalHom p)

private def repInvHead (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : AdeleRing (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ :=
  (fun w => (AdelicLevel.adeleArch (𝓞 ℚ) ℚ b w)⁻¹,
    ∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (evalHom p.1 b)⁻¹)

private def repInv (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : AdeleRing (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ :=
  repInvHead S b + tailAdele S

private theorem adeleArch_repInv (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : AdeleRing (𝓞 ℚ) ℚ) :
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ (repInv S b) = fun w => (AdelicLevel.adeleArch (𝓞 ℚ) ℚ b w)⁻¹ := by
  have h : AdelicLevel.adeleArch (𝓞 ℚ) ℚ (tailAdele S) = 0 := rfl
  unfold repInv
  rw [map_add, h, add_zero]
  rfl

private theorem evalHom_repInv_of_mem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : AdeleRing (𝓞 ℚ) ℚ)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ S) : evalHom p (repInv S b) = (evalHom p b)⁻¹ := by
  unfold repInv
  rw [map_add, evalHom_tailAdele, if_pos hp, add_zero]
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p
    (∑ q ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ q.1 (evalHom q.1 b)⁻¹) = (evalHom p b)⁻¹
  rw [map_sum]
  simp only [AdelicLevel.finAdeleEval_apply]
  rw [Finset.sum_eq_single (⟨p, hp⟩ : {p // p ∈ S})]
  · exact StandardAddChar.finAdeleSingleAt_apply_self ℚ p _
  · intro q _ hq
    exact StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hq (Subtype.ext h.symm)
  · intro h
    exact absurd (Finset.mem_attach _ _) h

private theorem evalHom_repInv_of_notMem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : AdeleRing (𝓞 ℚ) ℚ)
    {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ∉ S) : evalHom q (repInv S b) = 1 := by
  unfold repInv
  rw [map_add, evalHom_tailAdele, if_neg hq]
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ q
    (∑ r ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ r.1 (evalHom r.1 b)⁻¹) + 1 = 1
  rw [map_sum]
  simp only [AdelicLevel.finAdeleEval_apply]
  rw [Finset.sum_eq_zero fun r _ =>
    StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ r.1 _ fun h => hq (by rw [h]; exact r.2), zero_add]

private theorem adeleRep_mul_repInv (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : AdeleRing (𝓞 ℚ) ℚ)
    (hb : RepUnitLocus S b) : adeleRep S b * repInv S b = 1 := by
  refine Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext ℚ fun v => ?_)
  · change AdelicLevel.adeleArch (𝓞 ℚ) ℚ (adeleRep S b * repInv S b) w = (1 : InfiniteAdeleRing ℚ) w
    rw [map_mul, adeleArch_adeleRep, adeleArch_repInv]
    exact mul_inv_cancel₀ (hb.1 w)
  · change evalHom v (adeleRep S b * repInv S b) = 1
    rw [map_mul]
    by_cases hv : v ∈ S
    · rw [evalHom_adeleRep_of_mem S b hv, evalHom_repInv_of_mem S b hv, mul_inv_cancel₀ (hb.2 v hv)]
    · rw [evalHom_adeleRep_of_notMem S b hv, evalHom_repInv_of_notMem S b hv, mul_one]

private theorem repInv_mul_adeleRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : AdeleRing (𝓞 ℚ) ℚ)
    (hb : RepUnitLocus S b) : repInv S b * adeleRep S b = 1 := by
  rw [mul_comm]
  exact adeleRep_mul_repInv S b hb

private def unitRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : AdeleRing (𝓞 ℚ) ℚ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  if hb : RepUnitLocus S b then ⟨adeleRep S b, repInv S b, adeleRep_mul_repInv S b hb, repInv_mul_adeleRep S b hb⟩
  else 1

private theorem coe_unitRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : AdeleRing (𝓞 ℚ) ℚ) :
    (unitRep S b : AdeleRing (𝓞 ℚ) ℚ) = if RepUnitLocus S b then adeleRep S b else 1 := by
  unfold unitRep
  split_ifs <;> rfl

private theorem coe_unitRep_of_locus (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : AdeleRing (𝓞 ℚ) ℚ)
    (hb : RepUnitLocus S b) : (unitRep S b : AdeleRing (𝓞 ℚ) ℚ) = adeleRep S b := by
  rw [coe_unitRep, if_pos hb]

private theorem coe_inv_unitRep_of_locus (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : AdeleRing (𝓞 ℚ) ℚ)
    (hb : RepUnitLocus S b) : ((unitRep S b)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = (repInv S b : AdeleRing (𝓞 ℚ) ℚ) := by
  unfold unitRep
  rw [dif_pos hb]
  rfl

private theorem measurable_coe_unitRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    Measurable fun b => (unitRep S b : AdeleRing (𝓞 ℚ) ℚ) := by
  simp only [coe_unitRep]
  exact Measurable.ite (isOpen_repUnitLocus S).measurableSet (measurable_adeleRep S) measurable_const

private theorem measurable_unitRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Measurable (unitRep S) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (unitRep S) (MeasurableSpace.comap Units.val _) ≤ _
  rw [MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 (measurable_coe_unitRep S)

private theorem unitRep_add_of_integralOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (b u : AdeleRing (𝓞 ℚ) ℚ)
    (hu : IntegralOutside S u) : unitRep S (b + u) = unitRep S b := by
  refine Units.ext ?_
  rw [coe_unitRep, coe_unitRep, adeleRep_add_of_integralOutside S b u hu]
  by_cases hb : RepUnitLocus S b
  · rw [if_pos ((repUnitLocus_add_iff S b u hu).2 hb), if_pos hb]
  · rw [if_neg fun h => hb ((repUnitLocus_add_iff S b u hu).1 h), if_neg hb]

private theorem repUnitLocus_of_unit (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    RepUnitLocus S (x : AdeleRing (𝓞 ℚ) ℚ) := by
  refine ⟨fun w => ?_, fun p _ => ?_⟩
  · have h : AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x : AdeleRing (𝓞 ℚ) ℚ) *
        AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((x⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hw : AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x : AdeleRing (𝓞 ℚ) ℚ) w *
        AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((x⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) w = 1 := congrFun h w
    exact left_ne_zero_of_mul_eq_one hw
  · have h : evalHom p (x : AdeleRing (𝓞 ℚ) ℚ) *
        evalHom p ((x⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact left_ne_zero_of_mul_eq_one h

private theorem coe_unitRep_of_unit (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (unitRep S x : AdeleRing (𝓞 ℚ) ℚ) = adeleRep S x :=
  coe_unitRep_of_locus S x (repUnitLocus_of_unit S x)

private theorem exists_unitOutsideTrivialInside_mul (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hx : UnitOutside S x) : ∃ u, UnitOutsideTrivialInside S u ∧ x = unitRep S x * u := by
  have hloc := repUnitLocus_of_unit S x
  refine ⟨(unitRep S x)⁻¹ * x, ?_, (mul_inv_cancel_left (unitRep S x) x).symm⟩
  have hcoe : (((unitRep S x)⁻¹ * x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) =
      repInv S x * (x : AdeleRing (𝓞 ℚ) ℚ) := by
    rw [Units.val_mul, coe_inv_unitRep_of_locus S x hloc]
  refine ⟨fun q hq => ?_, fun p hp => ?_, ?_⟩
  · rw [hcoe, map_mul, evalHom_repInv_of_notMem S x hq, one_mul]
    exact hx q hq
  · rw [hcoe, map_mul, evalHom_repInv_of_mem S x hp, inv_mul_cancel₀ (hloc.2 p hp)]
  · rw [hcoe, map_mul, adeleArch_repInv]
    funext w
    exact inv_mul_cancel₀ (hloc.1 w)

end UnitRepresentative
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UnitsMeasurability

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private scoped instance secondCountableTopology_adeleRing : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

private theorem measurable_units_coe :
    Measurable (fun u : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (u : AdeleRing (𝓞 ℚ) ℚ)) :=
  fun _ hs => ⟨_, hs, rfl⟩

private theorem measurable_to_units {X : Type} [MeasurableSpace X] {f : X → (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hf : Measurable fun x => (f x : AdeleRing (𝓞 ℚ) ℚ)) : Measurable f := by
  rintro _ ⟨s, hs, rfl⟩
  exact hf hs

private scoped instance measurableMul₂_units : MeasurableMul₂ (AdeleRing (𝓞 ℚ) ℚ)ˣ := by
  refine ⟨measurable_to_units ?_⟩
  simp only [Units.val_mul]
  exact (measurable_units_coe.comp measurable_fst).mul (measurable_units_coe.comp measurable_snd)

private theorem integralOutsideAll_of_unitOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {x : (AdeleRing (𝓞 ℚ) ℚ)ˣ} (hx : UnitOutside S x) : IntegralOutsideAll S (x : AdeleRing (𝓞 ℚ) ℚ) :=
  fun q hq => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hx q hq).le

end UnitsMeasurability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Disjunction

variable {A : Type} [CommGroup A] [MeasurableSpace A] [MeasurableMul₂ A] (μ : Measure A) [SFinite μ]

private theorem ae_eq_zero_or_of_mul_translate {P : A → Prop} (hP : ∀ᵐ y ∂μ, P y)
    {w : A → ℝ≥0∞} (hw : ∀ y, P y → w y ≠ 0)
    (hshift : ∀ y, P y → ∀ F : A → ℝ≥0∞, Measurable F → ∫⁻ x, F (x * y) ∂μ = w y * ∫⁻ x, F x ∂μ)
    {k l : A → ℝ≥0∞} (hk : Measurable k) (hl : Measurable l)
    (h : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, k (x * y) * l x = 0) : k =ᵐ[μ] 0 ∨ l =ᵐ[μ] 0 := by
  have hk2 : Measurable fun p : A × A => k (p.1 * p.2) := hk.comp (measurable_fst.mul measurable_snd)
  have hkl : Measurable fun p : A × A => k (p.1 * p.2) * l p.1 := hk2.mul (hl.comp measurable_fst)
  have hΦ : Measurable fun x => ∫⁻ y, k (x * y) ∂μ := hk2.lintegral_prod_right'
  have hI : ∫⁻ x, (∫⁻ y, k (x * y) ∂μ) * l x ∂μ = 0 := by
    calc ∫⁻ x, (∫⁻ y, k (x * y) ∂μ) * l x ∂μ
        = ∫⁻ x, ∫⁻ y, k (x * y) * l x ∂μ ∂μ := by
          congr 1; ext x
          exact (lintegral_mul_const (l x) (hk.comp (measurable_const_mul x))).symm
      _ = ∫⁻ y, ∫⁻ x, k (x * y) * l x ∂μ ∂μ := lintegral_lintegral_swap hkl.aemeasurable
      _ = ∫⁻ y, 0 ∂μ := lintegral_congr_ae (h.mono fun y hy =>
          (lintegral_congr_ae hy).trans lintegral_zero)
      _ = 0 := lintegral_zero
  have hae : ∀ᵐ x ∂μ, (∫⁻ y, k (x * y) ∂μ) * l x = 0 := (lintegral_eq_zero_iff (hΦ.mul hl)).mp hI
  by_cases hk0 : ∫⁻ x, k x ∂μ = 0
  · exact Or.inl ((lintegral_eq_zero_iff hk).mp hk0)
  · refine Or.inr ?_
    filter_upwards [hae, hP] with x hx hPx
    have hfun : (fun y => k (x * y)) = fun y => k (y * x) := funext fun y => by rw [mul_comm]
    have hshx : ∫⁻ y, k (x * y) ∂μ = w x * ∫⁻ y, k y ∂μ := by
      rw [hfun]
      exact hshift x hPx k hk
    rw [hshx] at hx
    rcases mul_eq_zero.mp hx with h0 | h0
    · exact absurd h0 (mul_ne_zero (hw x hPx) hk0)
    · simpa using h0

private theorem ae_eq_zero_or_of_conj_mul_translate {P : A → Prop} (hP : ∀ᵐ y ∂μ, P y)
    {w : A → ℝ≥0∞} (hw : ∀ y, P y → w y ≠ 0)
    (hshift : ∀ y, P y → ∀ F : A → ℝ≥0∞, Measurable F → ∫⁻ x, F (x * y) ∂μ = w y * ∫⁻ x, F x ∂μ)
    {k l : A → ℂ} (hk : Measurable k) (hl : Measurable l)
    (h : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, starRingEnd ℂ (k (x * y)) * l x = 0) : k =ᵐ[μ] 0 ∨ l =ᵐ[μ] 0 := by
  have h' : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ,
      ((‖k (x * y)‖₊ : ℝ≥0∞) ^ 2) * ((‖l x‖₊ : ℝ≥0∞) ^ 2) = 0 := by
    filter_upwards [h] with y hy
    filter_upwards [hy] with x hx
    rcases mul_eq_zero.mp hx with h1 | h1
    · have h2 : k (x * y) = 0 := by simpa using h1
      simp [h2]
    · simp [h1]
  have hkm : Measurable fun a => (‖k a‖₊ : ℝ≥0∞) ^ 2 := hk.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hlm : Measurable fun a => (‖l a‖₊ : ℝ≥0∞) ^ 2 := hl.nnnorm.coe_nnreal_ennreal.pow_const 2
  rcases ae_eq_zero_or_of_mul_translate μ hP hw hshift hkm hlm h' with h0 | h0
  · refine Or.inl ?_
    filter_upwards [h0] with a ha
    simpa using ha
  · refine Or.inr ?_
    filter_upwards [h0] with a ha
    simpa using ha

private theorem mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · exact le_add_left (by rw [sq]; exact mul_le_mul' h le_rfl)
  · exact le_add_right (by rw [sq]; exact mul_le_mul' le_rfl h)

omit [SFinite μ] in

private theorem integrable_conj_mul_translate {w : ℝ≥0∞} (hw : w ≠ ⊤) {y : A}
    (hshift : ∀ F : A → ℝ≥0∞, Measurable F → ∫⁻ x, F (x * y) ∂μ = w * ∫⁻ x, F x ∂μ)
    {k l : A → ℂ} (hk : Measurable k) (hl : Measurable l)
    (hk₂ : ∫⁻ x, (‖k x‖₊ : ℝ≥0∞) ^ 2 ∂μ ≠ ⊤) (hl₂ : ∫⁻ x, (‖l x‖₊ : ℝ≥0∞) ^ 2 ∂μ ≠ ⊤) :
    Integrable (fun x => starRingEnd ℂ (k (x * y)) * l x) μ := by
  have hky : Measurable fun x => k (x * y) := hk.comp (measurable_mul_const y)
  have hmeas : Measurable fun x => starRingEnd ℂ (k (x * y)) * l x :=
    (Complex.continuous_conj.measurable.comp hky).mul hl
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hbound : ∀ x, (‖starRingEnd ℂ (k (x * y)) * l x‖₊ : ℝ≥0∞) ≤
      (‖k (x * y)‖₊ : ℝ≥0∞) ^ 2 + (‖l x‖₊ : ℝ≥0∞) ^ 2 := by
    intro x
    rw [nnnorm_mul, starRingEnd_apply, nnnorm_star, ENNReal.coe_mul]
    exact mul_le_sq_add_sq _ _
  have hk₂y : ∫⁻ x, (‖k (x * y)‖₊ : ℝ≥0∞) ^ 2 ∂μ = w * ∫⁻ x, (‖k x‖₊ : ℝ≥0∞) ^ 2 ∂μ :=
    hshift (fun x => (‖k x‖₊ : ℝ≥0∞) ^ 2) (hk.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hfin : ∫⁻ x, (‖k (x * y)‖₊ : ℝ≥0∞) ^ 2 + (‖l x‖₊ : ℝ≥0∞) ^ 2 ∂μ ≠ ⊤ := by
    rw [lintegral_add_left (hky.nnnorm.coe_nnreal_ennreal.pow_const 2), hk₂y]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hw hk₂, hl₂⟩
  exact ((lintegral_mono fun x => hbound x).trans_lt hfin.lt_top)

end Disjunction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Engine

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end Engine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section TorusStage

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem density_ae_eq_zero (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ] (hC : ∀ᵐ x ∂ρ, UnitOutside S x)
    {w : ℝ≥0∞} (hw : w ≠ ⊤) {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hshift : ∀ F : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ≥0∞, Measurable F → ∫⁻ x, F (x * y) ∂ρ = w * ∫⁻ x, F x ∂ρ)
    (k l : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ) (hk : Measurable k) (hl : Measurable l)
    (hk₂ : ∫⁻ x, (‖k x‖₊ : ℝ≥0∞) ^ 2 ∂ρ ≠ ⊤) (hl₂ : ∫⁻ x, (‖l x‖₊ : ℝ≥0∞) ^ 2 ∂ρ ≠ ⊤)
    (hkinv : ∀ x u, UnitOutsideTrivialInside S u → k (x * u) = k x)
    (hlinv : ∀ x u, UnitOutsideTrivialInside S u → l (x * u) = l x)
    (hy : ∀ᵐ s ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s},
      ∫ x, NumberField.StandardAddChar.psiQ (-((x : AdeleRing (𝓞 ℚ) ℚ) * s)) *
        ((starRingEnd ℂ) (k (x * y)) * l x) ∂ρ = 0) :
    ∀ᵐ x ∂ρ, (starRingEnd ℂ) (k (x * y)) * l x = 0 := by

  set D : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ := fun x => (starRingEnd ℂ) (k (x * y)) * l x with hD_def
  have hD : Integrable D ρ := integrable_conj_mul_translate ρ hw hshift hk hl hk₂ hl₂
  have hDm : Measurable D :=
    (Complex.continuous_conj.measurable.comp (hk.comp (measurable_mul_const y))).mul hl
  set C : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ := {x | UnitOutside S x} with hC_def
  have hCae : ∀ᵐ x ∂ρ, x ∈ C := hC
  set D' : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ := C.indicator D with hD'_def
  have hDD' : D =ᵐ[ρ] D' := by
    filter_upwards [hCae] with x hx
    rw [hD'_def, Set.indicator_of_mem hx]
  have hD' : Integrable D' ρ := hD.congr hDD'

  set coord : (AdeleRing (𝓞 ℚ) ℚ)ˣ → (Fin 1 → AdeleRing (𝓞 ℚ) ℚ) := fun z _ => (z : AdeleRing (𝓞 ℚ) ℚ)
    with hcoord_def
  have hcoord : Measurable coord := measurable_pi_lambda _ fun _ => measurable_units_coe
  have hdot : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (t : Fin 1 → AdeleRing (𝓞 ℚ) ℚ),
      coord z ⬝ᵥ t = (z : AdeleRing (𝓞 ℚ) ℚ) * t 0 := fun z t => by
    simp [hcoord_def, dotProduct, Fin.sum_univ_one]
  have hsupp : ∀ z, D' z ≠ 0 → ∀ i, IntegralOutsideAll S (coord z i) := fun z hz _ =>
    integralOutsideAll_of_unitOutside S (Set.mem_of_indicator_ne_zero hz)

  have hy' : ∀ᵐ s ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s},
      ∫ z, NumberField.StandardAddChar.psiQ (-((z : AdeleRing (𝓞 ℚ) ℚ) * s)) * D' z ∂ρ = 0 := by
    filter_upwards [hy] with s hs
    refine (integral_congr_ae ?_).trans hs
    filter_upwards [hDD'] with z hz
    rw [← hz]
  have hcoef : ∀ᵐ t ∂(Measure.pi fun _ : Fin 1 =>
      (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s}),
      ∫ z, NumberField.StandardAddChar.psiQ (-(coord z ⬝ᵥ t)) * D' z ∂ρ = 0 := by
    have hmp := measurePreserving_funUnique
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s}) (Fin 1)
    filter_upwards [hmp.quasiMeasurePreserving.ae hy'] with t ht
    have h0 : (MeasurableEquiv.funUnique (Fin 1) (AdeleRing (𝓞 ℚ) ℚ)) t = t 0 :=
      congrArg t (Subsingleton.elim _ _)
    simp_rw [hdot, ← h0]
    exact ht

  set Θ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ := fun e => ((1 + ‖D e‖)⁻¹ : ℝ) • (starRingEnd ℂ) (D e) with hΘ_def
  set g : (Fin 1 → AdeleRing (𝓞 ℚ) ℚ) → ℂ := fun v => Θ (unitRep S (v 0)) with hg_def
  have hΘm : Measurable Θ := by
    refine Measurable.fun_smul ?_ (Complex.continuous_conj.measurable.comp hDm)
    exact ((continuous_const.add continuous_norm).measurable.comp hDm).inv
  have hg : Measurable g := hΘm.comp ((measurable_unitRep S).comp (measurable_pi_apply 0))
  have hgb : ∃ C : ℝ, ∀ v, ‖g v‖ ≤ C := by
    refine ⟨1, fun v => ?_⟩
    show ‖((1 + ‖D (unitRep S (v 0))‖)⁻¹ : ℝ) • (starRingEnd ℂ) (D (unitRep S (v 0)))‖ ≤ 1
    have hn : 0 ≤ ‖D (unitRep S (v 0))‖ := norm_nonneg _
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity), RCLike.norm_conj,
      inv_mul_le_iff₀ (by positivity)]
    linarith
  have hginv : ∀ v u, (∀ i, IntegralOutside S (u i)) → g (v + u) = g v := fun v u hu => by
    show Θ (unitRep S (v 0 + u 0)) = Θ (unitRep S (v 0))
    rw [unitRep_add_of_integralOutside S (v 0) (u 0) (hu 0)]

  have hzero := integral_mul_eq_zero_of_coefficients S 1 ρ coord hcoord D' hD' hsupp hcoef g hg hgb hginv

  have hDrep : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, UnitOutside S z → D (unitRep S (z : AdeleRing (𝓞 ℚ) ℚ)) = D z := by
    intro z hz
    obtain ⟨u, hu, hzu⟩ := exists_unitOutsideTrivialInside_mul S z hz
    show (starRingEnd ℂ) (k (unitRep S (z : AdeleRing (𝓞 ℚ) ℚ) * y)) * l (unitRep S (z : AdeleRing (𝓞 ℚ) ℚ)) =
      (starRingEnd ℂ) (k (z * y)) * l z
    conv_rhs => rw [hzu, mul_right_comm, hkinv _ u hu, hlinv _ u hu]
  set F : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ := fun z => (1 + ‖D z‖)⁻¹ * ‖D z‖ ^ 2 with hF_def
  have hgF : ∀ᵐ z ∂ρ, g (coord z) * D' z = (F z : ℂ) := by
    filter_upwards [hCae] with z hz
    show Θ (unitRep S (z : AdeleRing (𝓞 ℚ) ℚ)) * C.indicator D z = (((1 + ‖D z‖)⁻¹ * ‖D z‖ ^ 2 : ℝ) : ℂ)
    rw [Set.indicator_of_mem hz, hΘ_def]
    dsimp only
    rw [hDrep z hz, smul_mul_assoc, Complex.conj_mul', Complex.real_smul]
    push_cast
    ring
  have hF0 : ∫ z, F z ∂ρ = 0 := by
    have h1 : ∫ z, (F z : ℂ) ∂ρ = 0 := (integral_congr_ae (hgF.mono fun z hz => hz.symm)).trans hzero
    rw [integral_complex_ofReal] at h1
    exact_mod_cast h1
  have hFnn : ∀ z, 0 ≤ F z := fun z => by positivity
  have hFle : ∀ z, F z ≤ ‖D z‖ := fun z => by
    have hn : 0 ≤ ‖D z‖ := norm_nonneg _
    rw [hF_def]
    dsimp only
    rw [inv_mul_le_iff₀ (by positivity)]
    nlinarith
  have hFm : Measurable F :=
    ((continuous_const.add continuous_norm).measurable.comp hDm).inv.mul
      ((continuous_norm.measurable.comp hDm).pow_const 2)
  have hFi : Integrable F ρ :=
    hD.norm.mono' hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (hFnn z)]; exact hFle z)
  have hFae : F =ᵐ[ρ] 0 := (integral_eq_zero_iff_of_nonneg (fun z => hFnn z) hFi).mp hF0
  filter_upwards [hFae] with z hz
  have hz' : (1 + ‖D z‖)⁻¹ * ‖D z‖ ^ 2 = 0 := hz
  have hpos : 0 < (1 + ‖D z‖)⁻¹ := by positivity
  have hsq : ‖D z‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hz' with h | h
    · exact absurd h hpos.ne'
    · exact h
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

private theorem profile_eq_zero_or_eq_zero (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ] (hρ : ρ {y | ¬ UnitOutside S y} = 0)
    (w : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ≥0∞) (hw : ∀ y, UnitOutside S y → w y ≠ 0 ∧ w y ≠ ⊤)
    (hshift : ∀ y, UnitOutside S y → ∀ F : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ≥0∞, Measurable F →
      ∫⁻ x, F (x * y) ∂ρ = w y * ∫⁻ x, F x ∂ρ)
    (k l : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ) (hk : Measurable k) (hl : Measurable l)
    (hk₂ : ∫⁻ x, (‖k x‖₊ : ℝ≥0∞) ^ 2 ∂ρ ≠ ⊤) (hl₂ : ∫⁻ x, (‖l x‖₊ : ℝ≥0∞) ^ 2 ∂ρ ≠ ⊤)
    (hkinv : ∀ x u, UnitOutsideTrivialInside S u → k (x * u) = k x)
    (hlinv : ∀ x u, UnitOutsideTrivialInside S u → l (x * u) = l x)
    (hvan : ∀ᵐ y ∂ρ, ∀ᵐ s ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s},
      ∫ x, NumberField.StandardAddChar.psiQ (-((x : AdeleRing (𝓞 ℚ) ℚ) * s)) *
        ((starRingEnd ℂ) (k (x * y)) * l x) ∂ρ = 0) :
    k =ᵐ[ρ] 0 ∨ l =ᵐ[ρ] 0 := by
  have hC : ∀ᵐ x ∂ρ, UnitOutside S x := ae_iff.2 hρ
  have hmain : ∀ᵐ y ∂ρ, ∀ᵐ x ∂ρ, (starRingEnd ℂ) (k (x * y)) * l x = 0 := by
    filter_upwards [hvan, hC] with y hy hPy
    exact density_ae_eq_zero S ρ hC (hw y hPy).2 (hshift y hPy) k l hk hl hk₂ hl₂ hkinv hlinv hy
  exact ae_eq_zero_or_of_conj_mul_translate ρ hC (fun y hy => (hw y hy).1) hshift hk hl hmain

end TorusStage
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end MirabolicLeviFibration
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end TorusDilation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowTransport

noncomputable section

namespace MirabolicLeviFibration

section Parameters

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end Parameters
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Furniture

end Furniture
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end RowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Modulus

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end Modulus
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section GenericDevice

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] {Y : Type} [MeasurableSpace Y]

end GenericDevice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section LeviFibration

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end LeviFibration
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end RowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section SectionAndRowSets

section SectionHeads

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

open scoped RestrictedProduct

open Topology

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

end SectionHeads
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end SectionAndRowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UniquenessPrinciple

section UniquenessHead

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open Filter Topology Set

open scoped NNReal Classical

attribute [local instance] archBorel

attribute [local instance] archBorelSpace

attribute [local instance] localBorel

attribute [local instance] localBorelSpace

attribute [local instance] countable_primes

attribute [local instance] properCompletion archSecondCountable

attribute [local instance] secondCountableAdeles NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

attribute [local instance] borelRows

attribute [local instance] haarRows

attribute [local instance] localSecondCountable

attribute [local instance] archRowsSecondCountable localRowsSecondCountable

attribute [local instance] secondCountableCoords

attribute [local instance] archRowsBorel localRowsBorel

attribute [local instance] borelCoords

attribute [local instance] locallyCompactCoords

attribute [local instance] sigmaCompactCoords

attribute [local instance] coordsHaar_isAddHaarMeasure

attribute [local instance] sigmaFinite_coordsHaar

end UniquenessHead
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end UniquenessPrinciple
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

open Topology

section KernelMatrix

variable {A : Type} [CommRing A]

end KernelMatrix
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section KernelMatrixContinuity

variable {A : Type} [CommRing A] [TopologicalSpace A] {X : Type} [TopologicalSpace X]

end KernelMatrixContinuity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UnitsMeasurability

variable {R : Type} [Monoid R] [MeasurableSpace R]

end UnitsMeasurability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UnitsBorelTopology

variable {R : Type} [Monoid R] [TopologicalSpace R]

end UnitsBorelTopology
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UnitsBorel

variable {R : Type} [Monoid R] [TopologicalSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]

end UnitsBorel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section MatrixBorel

variable {A : Type} [TopologicalSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

end MatrixBorel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section MatrixUnitsBorel

variable {A : Type} [CommRing A] [TopologicalSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

end MatrixUnitsBorel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section IdeleInversion

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

open Filter Topology Set
open scoped RestrictedProduct NNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] archBorel archBorelSpace localBorel localBorelSpace countable_primes
attribute [local instance] properCompletion archSecondCountable localSecondCountable secondCountableAdeles

end IdeleInversion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Furniture

end Furniture
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end RowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section JacobianAndModulus

section JacobianUnimodular

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

open scoped NNReal Pointwise

open NumberField.AdelicHaar

section Generation

variable {R : Type*} [CommRing R] {M : Type*} [CommGroup M]

section Pivots

variable {e : Fin 3 → R} (hii : ∀ i, e i * e i = e i) (hij : ∀ i j, i ≠ j → e i * e j = 0)
  (hsum : e 0 + e 1 + e 2 = 1)

include hii hij hsum

end Pivots
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end Generation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Adele

variable (K : Type*) [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K

end Adele
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

section Torsion

end Torsion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowAction

end RowAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem unipotentSubgroup3_le_mirabolic : WhittakerBlock.unipotentSubgroup3 ≤ mirabolic := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨t, rfl⟩
  show bottomRow _ = e₃
  funext j
  fin_cases j <;> simp [bottomRow, e₃, upperUnipotent3_coe]

end JacobianUnimodular
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end JacobianAndModulus
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section CosetDensity

section Cosets

variable {G : Type} [Group G] (H : Subgroup G)

private theorem exists_mem_mul_eq_out (g : G) :
    ∃ n ∈ H, n * g = (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out := by
  have h : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out ∈ MulAction.orbit H g := by
    rw [← MulAction.orbitRel.Quotient.orbit_mk]
    exact MulAction.orbitRel.Quotient.mem_orbit.2 (Quotient.out_eq' _)
  obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.1 h
  exact ⟨n, n.2, hn⟩

variable {H}

private theorem apply_out_mk {α : Type} {h : G → α} (hinv : ∀ n ∈ H, ∀ g, h (n * g) = h g) (g : G) :
    h (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = h g := by
  obtain ⟨n, hn, e⟩ := exists_mem_mul_eq_out H g
  rw [← e, hinv n hn]

private theorem prop_out_mk_iff {P : G → Prop} (hinv : ∀ n ∈ H, ∀ g, P (n * g) ↔ P g) (g : G) :
    P (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out ↔ P g := by
  obtain ⟨n, hn, e⟩ := exists_mem_mul_eq_out H g
  rw [← e, hinv n hn]

private theorem measurableSet_setOf_out [MeasurableSpace G] {P : G → Prop} (hP : MeasurableSet {g | P g})
    (hinv : ∀ n ∈ H, ∀ g, P (n * g) ↔ P g) : MeasurableSet {q : MulAction.orbitRel.Quotient H G | P q.out} := by
  rw [measurableSet_quotient]
  convert hP using 1
  ext g
  exact prop_out_mk_iff hinv g

end Cosets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section QuotientDensity

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem measurable_weight (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · haveI := h.1
    haveI := h.2
    exact Measurable.tsum fun n =>
      measurable_const.mul (measurable_const.indicator isOpen_interior.measurableSet)
  · exact measurable_const

private theorem measurable_density (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] : Measurable (HaarQuotient.density H μH) := by
  haveI : SigmaCompactSpace H := hH.sigmaCompactSpace
  unfold HaarQuotient.density
  refine (measurable_weight H μH).div ?_
  refine Measurable.lintegral_prod_right (f := fun g (x : H) => HaarQuotient.weight H μH ((x : G) * g)) ?_
  exact (measurable_weight H μH).comp
    ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable

private theorem lintegral_out_eq_lintegral_density_mul (μ : Measure G) (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] (h : G → ℝ≥0∞) (hh : Measurable h)
    (hinv : ∀ n ∈ H, ∀ g, h (n * g) = h g) :
    ∫⁻ q, h q.out ∂(HaarQuotient.measure μ H μH) = ∫⁻ g, HaarQuotient.density H μH g * h g ∂μ := by
  have hout : (fun g : G => h (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) = h := by
    funext g
    exact apply_out_mk hinv g
  have hq : Measurable fun q : MulAction.orbitRel.Quotient H G => h q.out := by
    rw [measurable_from_quotient]
    have hcomp : ((fun q : MulAction.orbitRel.Quotient H G => h q.out) ∘
        (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)) = h := hout
    rw [hcomp]
    exact hh
  unfold HaarQuotient.measure
  rw [lintegral_map hq measurable_quotient_mk'', hout,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_density H hH μH) hh]
  rfl

end QuotientDensity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Block

attribute [local instance] secondCountableTopology_adelicGL3 NumberField.AdelicHaar.borelSpace_glBorel

private def integrand (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ≥0∞ :=
  (‖W g‖₊ : ℝ≥0∞) ^ 2 * (‖Φ fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
    ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ)

private theorem block_eq_setLIntegral (pins : AutomorphicForm.CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    WhittakerBlock.block pins ψ f Φ σ S =
      ∫⁻ q in WhittakerBlock.zerothShell S, integrand (whittaker3 pins ψ f) Φ σ q.out
        ∂WhittakerBlock.quotientMeasure :=
  rfl

private theorem block_eq_lintegral_density_mul (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) [WhittakerBlock.unipotentHaar3.IsHaarMeasure]
    (C : AdelicGL 3 (𝓞 ℚ) ℚ → Prop) (hC : WhittakerBlock.zerothShell S = {q | C q.out})
    (hCmeas : MeasurableSet {g | C g})
    (hCinv : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g, C (n * g) ↔ C g)
    (hI : Measurable (integrand (whittaker3 pins ψ f) Φ σ))
    (hIinv : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g,
      integrand (whittaker3 pins ψ f) Φ σ (n * g) = integrand (whittaker3 pins ψ f) Φ σ g) :
    WhittakerBlock.block pins ψ f Φ σ S =
      ∫⁻ g, HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 g *
        {g | C g}.indicator (integrand (whittaker3 pins ψ f) Φ σ) g
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  classical
  rw [block_eq_setLIntegral, hC, ← lintegral_indicator (measurableSet_setOf_out hCmeas hCinv)]
  have hrepr : ∀ q : MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ),
      {q | C q.out}.indicator (fun q => integrand (whittaker3 pins ψ f) Φ σ q.out) q =
        {g | C g}.indicator (integrand (whittaker3 pins ψ f) Φ σ) q.out := by
    intro q
    by_cases hq : C q.out
    · rw [Set.indicator_of_mem (show q ∈ {q | C q.out} from hq),
        Set.indicator_of_mem (show q.out ∈ {g | C g} from hq)]
    · rw [Set.indicator_of_notMem (show q ∉ {q | C q.out} from hq),
        Set.indicator_of_notMem (show q.out ∉ {g | C g} from hq)]
  simp only [hrepr]
  have hmain := lintegral_out_eq_lintegral_density_mul (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
    WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3 WhittakerBlock.unipotentHaar3
    ({g | C g}.indicator (integrand (whittaker3 pins ψ f) Φ σ)) (hI.indicator hCmeas) ?_
  · exact hmain
  · intro n hn g
    by_cases hg : C g
    · rw [Set.indicator_of_mem (show n * g ∈ {g | C g} from (hCinv n hn g).2 hg),
        Set.indicator_of_mem (show g ∈ {g | C g} from hg), hIinv n hn g]
    · rw [Set.indicator_of_notMem (show n * g ∉ {g | C g} from fun h => hg ((hCinv n hn g).1 h)),
        Set.indicator_of_notMem (show g ∉ {g | C g} from hg)]

end Block
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end CosetDensity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section ShellCondition

section Shell

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

private def LocUnip (n : LocalGL3 p) : Prop :=
  ∃ x y z : p.adicCompletion ℚ, n = upperUnipotent3 x y z

private theorem locUnip_mul {n n' : LocalGL3 p} (hn : LocUnip p n) (hn' : LocUnip p n') : LocUnip p (n * n') := by
  obtain ⟨x, y, z, rfl⟩ := hn
  obtain ⟨x', y', z', rfl⟩ := hn'
  refine ⟨x' + x, y' + y, z' + x * y' + z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem locUnip_inv {n : LocalGL3 p} (hn : LocUnip p n) : LocUnip p n⁻¹ := by
  obtain ⟨x, y, z, rfl⟩ := hn
  exact ⟨-x, -y, x * y - z, Units.ext rfl⟩

private def ZeroShellAt (x : LocalGL3 p) : Prop :=
  ∃ (a b c : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ x = upperUnipotent3 a b c * k

private theorem zeroShellAt_unip_mul_iff {n : LocalGL3 p} (hn : LocUnip p n) (x : LocalGL3 p) :
    ZeroShellAt p (n * x) ↔ ZeroShellAt p x := by
  constructor
  · rintro ⟨a, b, c, k, hk, h⟩
    obtain ⟨a', b', c', hm⟩ := locUnip_mul p (locUnip_inv p hn) ⟨a, b, c, rfl⟩
    exact ⟨a', b', c', k, hk, by rw [← hm, mul_assoc, ← h, inv_mul_cancel_left]⟩
  · rintro ⟨a, b, c, k, hk, rfl⟩
    obtain ⟨a', b', c', hm⟩ := locUnip_mul p hn ⟨a, b, c, rfl⟩
    exact ⟨a', b', c', k, hk, by rw [← mul_assoc, hm]⟩

private theorem zeroShellAt_mul_right_iff {k₀ : LocalGL3 p} (hk₀ : k₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (x : LocalGL3 p) : ZeroShellAt p (x * k₀) ↔ ZeroShellAt p x := by
  constructor
  · rintro ⟨a, b, c, k, hk, h⟩
    exact ⟨a, b, c, k * k₀⁻¹, mul_mem hk (inv_mem hk₀), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  · rintro ⟨a, b, c, k, hk, rfl⟩
    exact ⟨a, b, c, k * k₀, mul_mem hk hk₀, by rw [mul_assoc]⟩

private theorem isOpen_localMaximalCompact3 : IsOpen ((localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p))) := by
  have hpre : ∀ f : LocalGL3 p → p.adicCompletion ℚ, Continuous f → IsOpen {k : LocalGL3 p | Valued.v (f k) ≤ 1} :=
    fun f hf => by
      simpa [Set.preimage, Valuation.mem_integer_iff] using (Valued.isOpen_integer (p.adicCompletion ℚ)).preimage hf
  have hK : (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p)) =
      (⋂ i, ⋂ j, {k : LocalGL3 p | Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1}) ∩
        ⋂ i, ⋂ j, {k : LocalGL3 p |
          Valued.v (((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1} := by
    ext k
    simp only [SetLike.mem_coe, mem_localMaximalCompact3_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hK]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hpre _ (Units.continuous_val.matrix_elem i j)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hpre _ (Units.continuous_coe_inv.matrix_elem i j))

private theorem isOpen_setOf_zeroShellAt : IsOpen {x : LocalGL3 p | ZeroShellAt p x} := by
  have h : {x : LocalGL3 p | ZeroShellAt p x} =
      ⋃ t : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ,
        (fun k : LocalGL3 p => upperUnipotent3 t.1 t.2.1 t.2.2 * k) ''
          (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨a, b, c, k, hk, rfl⟩
      exact ⟨(a, b, c), k, hk, rfl⟩
    · rintro ⟨t, k, hk, rfl⟩
      exact ⟨t.1, t.2.1, t.2.2, k, hk, rfl⟩
  rw [h]
  exact isOpen_iUnion fun t => (isOpenMap_mul_left _) _ (isOpen_localMaximalCompact3 p)

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem map_upperUnipotent3 {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x y z : A) :
    Matrix.GeneralLinearGroup.map f (upperUnipotent3 x y z) = upperUnipotent3 (f x) (f y) (f z) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply, upperUnipotent3_coe]

private theorem locUnip_componentAt3 {n : AdelicGL 3 (𝓞 ℚ) ℚ} (hn : n ∈ WhittakerBlock.unipotentSubgroup3)
    (p : HeightOneSpectrum (𝓞 ℚ)) : LocUnip p (componentAt3 (𝓞 ℚ) ℚ p n) := by
  obtain ⟨x, y, z, rfl⟩ := (WhittakerBlock.mem_unipotentSubgroup3_iff n).1 hn
  exact ⟨_, _, _, map_upperUnipotent3 (evalHom p) x y z⟩

private theorem continuous_componentAt3 (q : HeightOneSpectrum (𝓞 ℚ)) : Continuous (componentAt3 (𝓞 ℚ) ℚ q) :=
  Continuous.units_map _ ((continuous_id.matrix_map (continuous_evalHom q)) :
    Continuous fun m : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) => m.map (evalHom q))

private theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 ℚ)) :=
  Countable.of_equiv _ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm

private theorem zerothShell_eq_setOf_shellCond (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    WhittakerBlock.zerothShell S = {q | ShellCond S q.out} := by
  ext q
  rfl

private theorem measurableSet_shellCond (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    MeasurableSet {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := countable_heightOneSpectrum
  have h : {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} =
      ⋂ p, ⋂ (_ : p ∉ S), {g : AdelicGL 3 (𝓞 ℚ) ℚ | ZeroShellAt p (componentAt3 (𝓞 ℚ) ℚ p g)} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [h]
  exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ =>
    ((isOpen_setOf_zeroShellAt p).preimage (continuous_componentAt3 p)).measurableSet

private theorem shellCond_mul_left_iff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ShellCond S (n * g) ↔ ShellCond S g := by
  intro n hn g
  show (∀ p, p ∉ S → ZeroShellAt p (componentAt3 (𝓞 ℚ) ℚ p (n * g))) ↔
    ∀ p, p ∉ S → ZeroShellAt p (componentAt3 (𝓞 ℚ) ℚ p g)
  exact forall_congr' fun p => imp_congr_right fun _ => by
    rw [map_mul]
    exact zeroShellAt_unip_mul_iff p (locUnip_componentAt3 hn p) _

private theorem shellCond_mul_right_iff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (g h : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hh : ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p h ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ShellCond S (g * h) ↔ ShellCond S g := by
  show (∀ p, p ∉ S → ZeroShellAt p (componentAt3 (𝓞 ℚ) ℚ p (g * h))) ↔
    ∀ p, p ∉ S → ZeroShellAt p (componentAt3 (𝓞 ℚ) ℚ p g)
  exact forall_congr' fun p => imp_congr_right fun hp => by
    rw [map_mul]
    exact zeroShellAt_mul_right_iff p (hh p hp) _

end Shell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end ShellCondition
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section SectionAndRowSets

section SectionHeads

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

open scoped RestrictedProduct

open Topology

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

private theorem mem_explicitRows {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {x : Fin 3 → 𝔸} :
    x ∈ explicitRows S ↔ (∀ p, p ∉ S → PrimitiveAt p x) ∧ (∀ p ∈ S, NonzeroAt p x) ∧ NonzeroArch x :=
  Iff.rfl

private theorem mem_rowDomain_of_mem_explicitRows {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {x : Fin 3 → 𝔸}
    (hx : x ∈ explicitRows S) : x ∈ rowDomain := by
  obtain ⟨hprim, hS, harch⟩ := mem_explicitRows.mp hx
  refine mem_rowDomain.mpr ⟨fun p => ?_, harch, ?_⟩
  · by_cases hp : p ∈ S
    · exact hS p hp
    · obtain ⟨j, hj⟩ := (hprim p hp).2
      exact ⟨j, fun h0 => by rw [h0, map_zero] at hj; exact zero_ne_one hj⟩
  · refine Filter.eventually_cofinite.mpr (S.finite_toSet.subset fun p hp => ?_)
    by_contra hpS
    exact hp (hprim p fun h => hpS (Finset.mem_coe.mpr h))

section Chart

variable {A : Type*} [CommRing A]

end Chart
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem explicitRows_subset_rowDomain (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : explicitRows S ⊆ rowDomain := by
  exact fun _ hx => mem_rowDomain_of_mem_explicitRows hx

end SectionHeads
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end SectionAndRowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section HaarUniqueness

section RightInvariantUniqueness

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private theorem exists_eq_smul_of_isMulRightInvariant (m μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts m] [m.IsMulRightInvariant] :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ m = c • μ := by
  haveI : Measure.IsHaarMeasure μ.inv :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  obtain ⟨c, hc⟩ : ∃ c : NNReal, m.inv = c • μ.inv := ⟨_, Measure.isMulLeftInvariant_eq_smul m.inv μ.inv⟩
  refine ⟨c, ENNReal.coe_ne_top, ?_⟩
  ext s hs
  calc m s = m.inv.inv s := by rw [Measure.inv_inv]
    _ = m.inv s⁻¹ := Measure.inv_apply _ _
    _ = (c • μ.inv) s⁻¹ := by rw [hc]
    _ = c * μ.inv s⁻¹ := Measure.coe_nnreal_smul_apply _ _ _
    _ = c * μ s := by rw [Measure.inv_apply, inv_inv]
    _ = ((c : ℝ≥0∞) • μ) s := by rw [Measure.smul_apply, smul_eq_mul]

private theorem exists_ne_zero_and_eq_smul_of_isMulRightInvariant (m μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts m] [m.IsMulRightInvariant] (hm : m ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ m = c • μ := by
  obtain ⟨c, hc, h⟩ := exists_eq_smul_of_isMulRightInvariant m μ
  refine ⟨c, ?_, hc, h⟩
  rintro rfl
  exact hm (by rw [h, zero_smul])

end RightInvariantUniqueness
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end HaarUniqueness
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section WhittakerContinuity

private theorem continuous_integral_of_isCompact_carrier {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] (hY : OpensMeasurableSpace Y) (ν : MeasureTheory.Measure Y)
    (hν : MeasureTheory.IsFiniteMeasure ν) {C : Set Y} (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C) (F : X → Y → ℂ)
    (hF : Continuous fun p : X × Y => F p.1 p.2) : Continuous fun x => ∫ y, F x y ∂ν := by
  haveI := hY
  haveI := hν
  have hslice : ∀ x, Continuous (F x) := fun x =>
    hF.comp (continuous_const.prodMk continuous_id : Continuous fun y : Y => (x, y))
  have hint : ∀ x, MeasureTheory.Integrable (F x) ν := by
    intro x
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hslice x).continuousOn
    exact MeasureTheory.Integrable.of_bound (hslice x).aestronglyMeasurable M (hνC.mono fun y hy => hM y hy)
  have hcurry : Continuous (ContinuousMap.curry (⟨fun p : X × Y => F p.1 p.2, hF⟩ : ContinuousMap (X × Y) ℂ)) :=
    (ContinuousMap.curry _).continuous
  rw [continuous_iff_continuousAt]
  intro x₀
  have hunif : TendstoUniformlyOn (fun x y => F x y) (F x₀) (nhds x₀) C :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 (hcurry.tendsto x₀)) C hC
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hmpos : (0 : ℝ) < ν.real Set.univ + 1 := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg one_pos
  have hδ : (0 : ℝ) < ε / (ν.real Set.univ + 1) := div_pos hε hmpos
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif _ hδ] with x hx
  show dist (∫ y, F x y ∂ν) (∫ y, F x₀ y ∂ν) < ε
  rw [dist_eq_norm, ← MeasureTheory.integral_sub (hint x) (hint x₀)]
  calc ‖∫ y, (F x y - F x₀ y) ∂ν‖ ≤ ε / (ν.real Set.univ + 1) * ν.real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const (hνC.mono fun y hy => by
          rw [← dist_eq_norm, dist_comm]; exact (hx y hy).le)
    _ < ε / (ν.real Set.univ + 1) * (ν.real Set.univ + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hδ
    _ = ε := div_mul_cancel₀ ε hmpos.ne'

private theorem continuous_upperUnipotent3_triple {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous fun p : A × A × A => LanglandsTunnell.CubicInduction.upperUnipotent3 p.1 p.2.1 p.2.2 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.upperUnipotent3] <;> fun_prop

private theorem exists_isCompact_ae_mem_productionPins_measure :
    ∃ C : Set (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ), IsCompact C ∧
      (∀ᵐ y ∂(AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (NumberField.AdelicBox.adelicBox ℚ)).ν,
        y ∈ C) := by
  obtain ⟨C, hC, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset ℚ
  refine ⟨C, hC, ?_⟩
  have h : ∀ᵐ y ∂(AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1)
      (NumberField.AdelicBox.adelicBox ℚ)).ν, y ∈ NumberField.AdelicBox.adelicBox ℚ :=
    MeasureTheory.Measure.ae_smul_measure
      (MeasureTheory.ae_restrict_mem (NumberField.AdelicBox.measurableSet_adelicBox ℚ)) _
  exact h.mono fun y hy => hsub hy

private theorem continuous_whittaker3_productionPins
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (f : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hf : Continuous f) :
    Continuous (LanglandsTunnell.CubicInduction.whittaker3
      (AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (NumberField.AdelicBox.adelicBox ℚ)) ψ f) := by
  letI : MeasurableSpace (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :=
    NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers ℚ) ℚ
  have hY : OpensMeasurableSpace (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :=
    (NumberField.AdelicHaar.borelSpace_adeleBorel (NumberField.RingOfIntegers ℚ) ℚ).opensMeasurable
  set ν : @MeasureTheory.Measure (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
      (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers ℚ) ℚ) :=
    (AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (NumberField.AdelicBox.adelicBox ℚ)).ν
  haveI : MeasureTheory.IsProbabilityMeasure ν := NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  have hν : MeasureTheory.IsFiniteMeasure ν := inferInstance
  obtain ⟨C, hC, hνC⟩ := exists_isCompact_ae_mem_productionPins_measure
  have hn := continuous_upperUnipotent3_triple (A := NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)

  have hF₃ : Continuous fun p : (LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
      NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
      NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ =>
      ∫ z, f (LanglandsTunnell.CubicInduction.upperUnipotent3 p.1.2 p.2 z * p.1.1) * ψ (-(p.1.2 + p.2)) ∂ν := by
    refine continuous_integral_of_isCompact_carrier hY ν hν hC hνC _ ?_

    have hq : Continuous fun pz : ((LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ => (pz.1.1.2, pz.1.2, pz.2) :=
      (continuous_snd.comp (continuous_fst.comp continuous_fst)).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    have hU : Continuous fun pz : ((LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ =>
        LanglandsTunnell.CubicInduction.upperUnipotent3 pz.1.1.2 pz.1.2 pz.2 := hn.comp hq
    have hg : Continuous fun pz : ((LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ => pz.1.1.1 :=
      continuous_fst.comp (continuous_fst.comp continuous_fst)
    have hs : Continuous fun pz : ((LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ => -(pz.1.1.2 + pz.1.2) :=
      ((continuous_snd.comp (continuous_fst.comp continuous_fst)).add (continuous_snd.comp continuous_fst)).neg
    exact (hf.comp (hU.mul hg)).mul (hψ.comp hs)

  have hF₂ : Continuous fun gx : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
      NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ =>
      ∫ y, ∫ z, f (LanglandsTunnell.CubicInduction.upperUnipotent3 gx.2 y z * gx.1) * ψ (-(gx.2 + y)) ∂ν ∂ν := by
    refine continuous_integral_of_isCompact_carrier hY ν hν hC hνC _ ?_
    exact hF₃

  have h1 : Continuous fun g : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ =>
      ∫ x, ∫ y, ∫ z, f (LanglandsTunnell.CubicInduction.upperUnipotent3 x y z * g) * ψ (-(x + y)) ∂ν ∂ν ∂ν := by
    refine continuous_integral_of_isCompact_carrier hY ν hν hC hνC _ ?_
    exact hF₂
  exact h1

end WhittakerContinuity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Assembly

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

attribute [local instance] secondCountableTopology_adelicGL3 isMulRightInvariant_adelicGLHaar

attribute [local instance] WhittakerBlock.isHaarMeasure_unipotentHaar3

attribute [local instance] WhittakerBlock.isMulRightInvariant_unipotentHaar3

private theorem shellCond_one (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : ShellCond S 1 := by
  intro p _
  refine ⟨0, 0, 0, 1, Subgroup.one_mem _, ?_⟩
  rw [map_one, mul_one]
  ext i j
  simp [Matrix.one_apply]

private theorem shellCond_coe_mul_sec0_iff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ explicitRows S) (p : ↥mirabolic) :
    ShellCond S ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x) ↔ ShellCond S (p : AdelicGL 3 (𝓞 ℚ) ℚ) :=
  shellCond_mul_right_iff S _ _ fun q hq => componentAt3_sec0_mem (explicitRows_subset_rowDomain S hx) (hx.1 q hq)

private theorem unipotentHaar3_inv_eq_self : WhittakerBlock.unipotentHaar3.inv = WhittakerBlock.unipotentHaar3 := by
  set μ := WhittakerBlock.unipotentHaar3
  have hne : μ.inv ≠ 0 := by
    intro h
    have hu : μ.inv Set.univ ≠ 0 := by
      rw [Measure.inv_apply, Set.inv_univ]
      exact isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    exact hu (by rw [h, Measure.coe_zero, Pi.zero_apply])
  haveI : SecondCountableTopology ↥WhittakerBlock.unipotentSubgroup3 :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨c, -, -, hc⟩ := exists_ne_zero_and_eq_smul_of_isMulRightInvariant μ.inv μ hne
  have hsq : μ = (c ^ 2) • μ := by
    calc μ = μ.inv.inv := (Measure.inv_inv μ).symm
      _ = (c • μ).inv := by rw [hc]
      _ = c • μ.inv := by rw [Measure.inv_def, Measure.inv_def, Measure.map_smul]
      _ = c • (c • μ) := by rw [← hc, hc]
      _ = (c ^ 2) • μ := by rw [smul_smul, pow_two]
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts ↥WhittakerBlock.unipotentSubgroup3) := inferInstance
  have hK0 : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior (μ := μ) K.interior_nonempty).ne'
  have hKtop : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hc2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [one_pow, one_mul, hsq]
    rw [Measure.smul_apply, smul_eq_mul]
  have hc1 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective ((ENNReal.mul_left_inj hK0 hKtop).1 hc2)
  rw [hc, hc1, one_smul]

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end RowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UniquenessPrinciple

section UniquenessHead

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open Filter Topology Set

open scoped NNReal Classical

attribute [local instance] archBorel

attribute [local instance] archBorelSpace

attribute [local instance] localBorel

attribute [local instance] localBorelSpace

private theorem coe_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    ((localToAdelic3 p x : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) :=
  rfl

private theorem coe_componentAt3 (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((componentAt3 (𝓞 ℚ) ℚ q g : GL (Fin 3) (q.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) =
      (evalHom q).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_archComponent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem componentAt3_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ p (localToAdelic3 p x) = x := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3]
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, finMatN, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_self]

private theorem componentAt3_localToAdelic3_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ q (localToAdelic3 p x) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3, Units.val_one]
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, finMatN, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ i j hq]

private theorem archComponent3_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 p x) = 1 := by
  apply Units.ext
  rw [coe_archComponent3, coe_localToAdelic3, mapMatrix_arch_finMatN, Units.val_one]

private theorem ext_of_components {g h : AdelicGL 3 (𝓞 ℚ) ℚ}
    (harch : archComponent3 (𝓞 ℚ) ℚ g = archComponent3 (𝓞 ℚ) ℚ h)
    (hfin : ∀ q : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ q g = componentAt3 (𝓞 ℚ) ℚ q h) : g = h := by
  apply Units.ext
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · have h₁ := congrArg Units.val harch
    rwa [coe_archComponent3, coe_archComponent3] at h₁
  · refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    have h₂ := congrArg Units.val (hfin w)
    rw [coe_componentAt3, coe_componentAt3] at h₂
    ext i j : 1
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun h₂ i) j

private theorem commute_localToAdelic3 {p : HeightOneSpectrum (𝓞 ℚ)} {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : componentAt3 (𝓞 ℚ) ℚ p g = 1) (x : LocalGL3 p) :
    g * localToAdelic3 p x = localToAdelic3 p x * g := by
  refine ext_of_components ?_ fun q => ?_
  · rw [map_mul, map_mul, archComponent3_localToAdelic3, mul_one, one_mul]
  · by_cases hq : q = p
    · subst hq
      rw [map_mul, map_mul, hg, one_mul, mul_one]
    · rw [map_mul, map_mul, componentAt3_localToAdelic3_of_ne hq, mul_one, one_mul]

private theorem componentAt3_apply (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j =
      evalHom p ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) := by
  rw [coe_componentAt3]
  rfl

private def structureFin :
    (∀ q : HeightOneSpectrum (𝓞 ℚ), (q.adicCompletionIntegers ℚ : Set (q.adicCompletion ℚ))) →
      FiniteAdeleRing (𝓞 ℚ) ℚ :=
  RestrictedProduct.structureMap _ _ _

private theorem continuous_structureFin : Continuous structureFin :=
  (RestrictedProduct.isEmbedding_structureMap (𝓕 := Filter.cofinite)).continuous

private theorem tendsto_finAdele_of_components {ι : Type} {l : Filter ι} (a : ι → FiniteAdeleRing (𝓞 ℚ) ℚ)
    (a₀ : FiniteAdeleRing (𝓞 ℚ) ℚ) (ha : ∀ i q, a i q ∈ q.adicCompletionIntegers ℚ)
    (ha₀ : ∀ q, a₀ q ∈ q.adicCompletionIntegers ℚ) (hlim : ∀ q, ∀ᶠ i in l, a i q = a₀ q) :
    Tendsto a l (𝓝 a₀) := by
  let fam : ι → ∀ q : HeightOneSpectrum (𝓞 ℚ), (q.adicCompletionIntegers ℚ : Set (q.adicCompletion ℚ)) :=
    fun i q => ⟨a i q, ha i q⟩
  let fam₀ : ∀ q : HeightOneSpectrum (𝓞 ℚ), (q.adicCompletionIntegers ℚ : Set (q.adicCompletion ℚ)) :=
    fun q => ⟨a₀ q, ha₀ q⟩
  have hfam : ∀ i, structureFin (fam i) = a i := fun i => by
    apply RestrictedProduct.ext
    intro q
    rfl
  have hfam₀ : structureFin fam₀ = a₀ := by
    apply RestrictedProduct.ext
    intro q
    rfl
  have hpi : Tendsto fam l (𝓝 fam₀) := by
    refine tendsto_pi_nhds.2 fun q => tendsto_const_nhds.congr' ?_
    filter_upwards [hlim q] with i hi
    exact Subtype.ext hi.symm
  have h := (continuous_structureFin.tendsto fam₀).comp hpi
  rw [hfam₀] at h
  exact h.congr hfam

private theorem tendsto_adele_of_components {ι : Type} {l : Filter ι} (a : ι → AdeleRing (𝓞 ℚ) ℚ)
    (a₀ : AdeleRing (𝓞 ℚ) ℚ) (harch : ∀ i, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (a i) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ a₀)
    (ha : ∀ i q, evalHom q (a i) ∈ q.adicCompletionIntegers ℚ) (ha₀ : ∀ q, evalHom q a₀ ∈ q.adicCompletionIntegers ℚ)
    (hlim : ∀ q, ∀ᶠ i in l, evalHom q (a i) = evalHom q a₀) : Tendsto a l (𝓝 a₀) := by
  have h1 : Tendsto (fun i => (a i).1) l (𝓝 a₀.1) := tendsto_const_nhds.congr fun i => (harch i).symm
  have h2 : Tendsto (fun i => (a i).2) l (𝓝 a₀.2) := tendsto_finAdele_of_components (fun i => (a i).2) a₀.2 ha ha₀ hlim
  exact (Prod.tendsto_iff a a₀).2 ⟨h1, h2⟩

private theorem tendsto_val_of_components {ι : Type} {l : Filter ι} (g : ι → AdelicGL 3 (𝓞 ℚ) ℚ)
    (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (harch : ∀ i, archComponent3 (𝓞 ℚ) ℚ (g i) = archComponent3 (𝓞 ℚ) ℚ g₀)
    (hK : ∀ i q, componentAt3 (𝓞 ℚ) ℚ q (g i) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (hK₀ : ∀ q, componentAt3 (𝓞 ℚ) ℚ q g₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (hlim : ∀ q, ∀ᶠ i in l, componentAt3 (𝓞 ℚ) ℚ q (g i) = componentAt3 (𝓞 ℚ) ℚ q g₀) :
    Tendsto (fun i => ((g i : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) l
      (𝓝 ((g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) := by
  refine tendsto_pi_nhds.2 fun r => tendsto_pi_nhds.2 fun c => ?_
  refine tendsto_adele_of_components
    (fun i => ((g i : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) r c) _ ?_ ?_ ?_ ?_
  · intro i
    have h := congrArg (fun u : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      (u : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) r c) (harch i)
    simpa only [coe_archComponent3, RingHom.mapMatrix_apply, Matrix.map_apply] using h
  · intro i q
    have h := (hK i q).1 r c
    rw [componentAt3_apply] at h
    exact (HeightOneSpectrum.mem_adicCompletionIntegers ..).2 h
  · intro q
    have h := (hK₀ q).1 r c
    rw [componentAt3_apply] at h
    exact (HeightOneSpectrum.mem_adicCompletionIntegers ..).2 h
  · intro q
    filter_upwards [hlim q] with i hi
    have h := congrArg (fun u : GL (Fin 3) (q.adicCompletion ℚ) =>
      (u : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) r c) hi
    simpa only [componentAt3_apply] using h

private theorem tendsto_of_components {ι : Type} {l : Filter ι} (g : ι → AdelicGL 3 (𝓞 ℚ) ℚ)
    (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (harch : ∀ i, archComponent3 (𝓞 ℚ) ℚ (g i) = archComponent3 (𝓞 ℚ) ℚ g₀)
    (hK : ∀ i q, componentAt3 (𝓞 ℚ) ℚ q (g i) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (hK₀ : ∀ q, componentAt3 (𝓞 ℚ) ℚ q g₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (hlim : ∀ q, ∀ᶠ i in l, componentAt3 (𝓞 ℚ) ℚ q (g i) = componentAt3 (𝓞 ℚ) ℚ q g₀) :
    Tendsto g l (𝓝 g₀) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  simp only [Function.comp_def, Units.embedProduct_apply]
  refine (Prod.tendsto_iff _ _).2 ⟨tendsto_val_of_components g g₀ harch hK hK₀ hlim, ?_⟩
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  refine tendsto_val_of_components (fun i => (g i)⁻¹) g₀⁻¹ (fun i => ?_) (fun i q => ?_) (fun q => ?_) fun q => ?_
  · simp only [map_inv, harch i]
  · simp only [map_inv]
    exact inv_mem (hK i q)
  · simp only [map_inv]
    exact inv_mem (hK₀ q)
  · filter_upwards [hlim q] with i hi
    simp only [map_inv, hi]

private def keptAt (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  T.noncommProd (fun q => localToAdelic3 q (componentAt3 (𝓞 ℚ) ℚ q g)) fun _ _ _ _ hab =>
    (commute_localToAdelic3 (componentAt3_localToAdelic3_of_ne hab _) _).symm

private theorem keptAt_insert (g : AdelicGL 3 (𝓞 ℚ) ℚ) {T : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {a : HeightOneSpectrum (𝓞 ℚ)} (ha : a ∉ T) :
    keptAt g (insert a T) = localToAdelic3 a (componentAt3 (𝓞 ℚ) ℚ a g) * keptAt g T := by
  unfold keptAt
  rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]

private theorem archComponent3_keptAt (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    archComponent3 (𝓞 ℚ) ℚ (keptAt g T) = 1 := by
  refine Finset.induction_on T ?_ ?_
  · simp [keptAt]
  · intro a T ha ih
    rw [keptAt_insert g ha, map_mul, archComponent3_localToAdelic3, one_mul, ih]

private theorem componentAt3_keptAt (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (q : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ q (keptAt g T) = if q ∈ T then componentAt3 (𝓞 ℚ) ℚ q g else 1 := by
  refine Finset.induction_on T ?_ ?_
  · simp [keptAt]
  · intro a T ha ih
    rw [keptAt_insert g ha, map_mul, ih]
    by_cases hqa : q = a
    · subst hqa
      simp [componentAt3_localToAdelic3, ha]
    · simp [componentAt3_localToAdelic3_of_ne hqa, hqa]

private theorem translate_keptAt_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hinv : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    {k : AdelicGL 3 (𝓞 ℚ) ℚ} (hkS : ∀ p ∈ S, componentAt3 (𝓞 ℚ) ℚ p k = 1)
    (hkK : ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) : ∀ h : AdelicGL 3 (𝓞 ℚ) ℚ, F (h * keptAt k T) = F h := by
  refine Finset.induction_on T ?_ ?_
  · intro h
    simp [keptAt]
  · intro a T ha ih h
    rw [keptAt_insert k ha, ← mul_assoc, ih]
    by_cases haS : a ∈ S
    · rw [hkS a haS, map_one, mul_one]
    · exact hinv a haS h _ (Subgroup.mem_map.2 ⟨_, hkK a haS, rfl⟩)

private theorem translate_eq_of_components (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : Continuous F)
    (hinv : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    {k : AdelicGL 3 (𝓞 ℚ) ℚ} (hkArch : archComponent3 (𝓞 ℚ) ℚ k = 1) (hkS : ∀ p ∈ S, componentAt3 (𝓞 ℚ) ℚ p k = 1)
    (hkK : ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    F (h * k) = F h := by
  have hkK' : ∀ q, componentAt3 (𝓞 ℚ) ℚ q k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q := fun q => by
    by_cases hq : q ∈ S
    · rw [hkS q hq]
      exact one_mem _
    · exact hkK q hq
  have hlim : Tendsto (fun T => keptAt k T) atTop (𝓝 k) := by
    refine tendsto_of_components _ k (fun T => ?_) (fun T q => ?_) hkK' fun q => ?_
    · rw [archComponent3_keptAt, hkArch]
    · rw [componentAt3_keptAt]
      split_ifs
      · exact hkK' q
      · exact one_mem _
    · filter_upwards [eventually_ge_atTop ({q} : Finset (HeightOneSpectrum (𝓞 ℚ)))] with T hT
      rw [componentAt3_keptAt, if_pos (Finset.singleton_subset_iff.1 hT)]
  have h1 : Tendsto (fun T => F (h * keptAt k T)) atTop (𝓝 (F (h * k))) :=
    (hF.tendsto _).comp (tendsto_const_nhds.mul hlim)
  have h2 : (fun T => F (h * keptAt k T)) = fun _ => F h := funext fun T => translate_keptAt_eq S hinv hkS hkK T h
  rw [h2] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

attribute [local instance] countable_primes

attribute [local instance] properCompletion archSecondCountable

attribute [local instance] secondCountableAdeles NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

attribute [local instance] borelRows

attribute [local instance] haarRows

attribute [local instance] localSecondCountable

attribute [local instance] archRowsSecondCountable localRowsSecondCountable

attribute [local instance] secondCountableCoords

attribute [local instance] archRowsBorel localRowsBorel

attribute [local instance] borelCoords

attribute [local instance] locallyCompactCoords

attribute [local instance] sigmaCompactCoords

attribute [local instance] coordsHaar_isAddHaarMeasure

attribute [local instance] sigmaFinite_coordsHaar

end UniquenessHead
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end UniquenessPrinciple
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section OffPlacesRepresentatives

open scoped Classical

private def archMat (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.of fun i j => ((g i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)

private theorem mapMatrix_arch_archMat (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (archMat g) = g := by
  ext i j
  simp [archMat, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

private theorem mapMatrix_fin_archMat (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat g) = 1 := by
  ext i j
  simp [archMat, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

private def archPart (A : GL (Fin 3) (InfiniteAdeleRing ℚ)) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  glOf (archMat (A : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)))
    (archMat ((A⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)))
    (matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ
      (by rw [map_mul, mapMatrix_arch_archMat, mapMatrix_arch_archMat, map_one, Units.mul_inv])
      (by rw [map_mul, mapMatrix_fin_archMat, mapMatrix_fin_archMat, map_one, one_mul]))

private theorem archComponent3_archPart (A : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (archPart A) = A := by
  apply Units.ext
  rw [coe_archComponent3]
  exact mapMatrix_arch_archMat _

private theorem componentAt3_archPart (p : HeightOneSpectrum (𝓞 ℚ)) (A : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ p (archPart A) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, Units.val_one]
  show (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix
    ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat (A : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)))) = 1
  rw [mapMatrix_fin_archMat, map_one]

private def keptOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (h : AdelicGL 3 (𝓞 ℚ) ℚ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  archPart (archComponent3 (𝓞 ℚ) ℚ h) * keptAt h S

private theorem archComponent3_keptOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archComponent3 (𝓞 ℚ) ℚ (keptOutside S h) = archComponent3 (𝓞 ℚ) ℚ h := by
  rw [keptOutside, map_mul, archComponent3_archPart, archComponent3_keptAt, mul_one]

private theorem componentAt3_keptOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (h : AdelicGL 3 (𝓞 ℚ) ℚ)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ p (keptOutside S h) = if p ∈ S then componentAt3 (𝓞 ℚ) ℚ p h else 1 := by
  rw [keptOutside, map_mul, componentAt3_archPart, one_mul, componentAt3_keptAt]

private theorem translateRight_eq_translateRight_keptOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {h : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hh : ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p h ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hG : Continuous G)
    (hinv : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) G) :
    translateRight h G = translateRight (keptOutside S h) G := by
  have hk : ∀ y, G (y * ((keptOutside S h)⁻¹ * h)) = G y := fun y =>
    translate_eq_of_components S hG hinv
      (by rw [map_mul, map_inv, archComponent3_keptOutside, inv_mul_cancel])
      (fun p hp => by rw [map_mul, map_inv, componentAt3_keptOutside, if_pos hp, inv_mul_cancel])
      (fun p hp => by
        rw [map_mul, map_inv, componentAt3_keptOutside, if_neg hp, inv_one, one_mul]
        exact hh p hp) y
  funext y
  rw [translateRight_apply, translateRight_apply, ← hk (y * keptOutside S h), mul_assoc, mul_inv_cancel_left]

private theorem measurableSet_zerothShell (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    MeasurableSet (WhittakerBlock.zerothShell S) := by
  rw [measurableSet_quotient]
  convert measurableSet_shellCond S using 1
  ext g
  simp only [Set.mem_preimage, zerothShell_eq_setOf_shellCond, Set.mem_setOf_eq]
  have hmem : g ∈ MulAction.orbit WhittakerBlock.unipotentSubgroup3
      (Quotient.mk'' g : MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)).out := by
    rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq', MulAction.orbitRel.Quotient.orbit_mk]
    exact MulAction.mem_orbit_self g
  obtain ⟨m, hm⟩ := MulAction.mem_orbit_iff.mp hmem
  conv_rhs => rw [← hm]
  rw [Subgroup.smul_def, smul_eq_mul, shellCond_mul_left_iff S m m.2]

end OffPlacesRepresentatives
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Engine

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end Engine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Transport

attribute [local instance] NumberField.AdelicHaar.adeleBorel

section QuotientUnfolding

attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology secondCountableTopology_adelicGL3

attribute [local instance] WhittakerBlock.isHaarMeasure_unipotentHaar3

attribute [local instance] WhittakerBlock.isMulRightInvariant_unipotentHaar3

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem quotientMk_unipotent_mul {n : ↥mirabolic}
    (hn : (n : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ WhittakerBlock.unipotentSubgroup3) (p : ↥mirabolic) :
    (Quotient.mk'' (n * p) :
        MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic) =
      Quotient.mk'' p :=
  Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨⟨n, Subgroup.mem_subgroupOf.mpr hn⟩, rfl⟩)

private theorem indicator_shell_unipotent_mul (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {n : AdelicGL 3 (𝓞 ℚ) ℚ} (hn : n ∈ WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (n * g) =
      Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) g := by
  by_cases hg : ShellCond S g
  · rw [Set.indicator_of_mem (show n * g ∈ {g | ShellCond S g} from (shellCond_mul_left_iff S n hn g).mpr hg),
      Set.indicator_of_mem (show g ∈ {g | ShellCond S g} from hg)]
  · rw [Set.indicator_of_notMem (show n * g ∉ {g | ShellCond S g} from
        fun h => hg ((shellCond_mul_left_iff S n hn g).mp h)),
      Set.indicator_of_notMem (show g ∉ {g | ShellCond S g} from hg)]

private theorem lintegral_density_upperUnipotent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫⁻ a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ),
        HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
          (upperUnipotent3 a.1 a.2.2 a.2.1 * g)
        ∂((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
          (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) = 1 := by
  have hdens := measurable_density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
    WhittakerBlock.unipotentHaar3
  have hU : Continuous fun b : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      (upperUnipotent3 b.1 b.2.1 b.2.2 : AdelicGL 3 (𝓞 ℚ) ℚ) := continuous_upperUnipotent3_triple
  have hswap : MeasurePreserving
      (Prod.map id Prod.swap : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) →
        AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
        (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
        (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) :=
    (MeasurePreserving.id _).prod Measure.measurePreserving_swap
  calc ∫⁻ a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ),
          HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
            (upperUnipotent3 a.1 a.2.2 a.2.1 * g)
          ∂((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
            (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
      = ∫⁻ b : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ),
          HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
            (upperUnipotent3 b.1 b.2.1 b.2.2 * g)
          ∂((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
            (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) :=
        hswap.lintegral_comp (hdens.comp (hU.measurable.mul_const g))
    _ = ∫⁻ n : ↥WhittakerBlock.unipotentSubgroup3,
          HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
            ((n : AdelicGL 3 (𝓞 ℚ) ℚ) * g)
          ∂(Measure.map (fun t : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
              (⟨upperUnipotent3 t.1 t.2.1 t.2.2, Subgroup.subset_closure ⟨t, rfl⟩⟩ :
                ↥WhittakerBlock.unipotentSubgroup3))
            ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
              (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))) :=
        (lintegral_map (hdens.comp (measurable_subtype_coe.mul_const g)) (hU.measurable.subtype_mk)).symm
    _ = 1 := HaarQuotient.lintegral_density_mul_eq_one WhittakerBlock.unipotentSubgroup3
        WhittakerBlock.isClosed_unipotentSubgroup3 WhittakerBlock.unipotentHaar3 g

private theorem lintegral_fibre_eq (P₂ : Subgroup ↥mirabolic) (μ₂ : Measure ↥P₂)
    (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ]
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιm : Measurable ι)
    (hμ₂ι : μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))))
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    {G : ↥mirabolic → ℝ≥0∞} (hG : Measurable G)
    (hGinv : ∀ n : ↥mirabolic, (n : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ WhittakerBlock.unipotentSubgroup3 → ∀ p, G (n * p) = G p)
    (s : ↥mirabolic) :
    ∫⁻ p₂ : ↥P₂, HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((((p₂ : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ) * G ((p₂ : ↥mirabolic) * s) ∂μ₂ =
      ∫⁻ y, G ((ι (y, 0, 0, 0) : ↥mirabolic) * s) ∂ρ := by
  have hdens := measurable_density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
    WhittakerBlock.unipotentHaar3
  have hΦ : Measurable fun p : ↥mirabolic =>
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
        G p := (hdens.comp measurable_subtype_coe).mul hG
  have hΦs : Measurable fun p₂ : ↥P₂ =>
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((((p₂ : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ) * G ((p₂ : ↥mirabolic) * s) :=
    hΦ.comp (measurable_subtype_coe.mul_const s)
  have hN : ∀ a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ),
      (upperUnipotent3 a.1 a.2.2 a.2.1 : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ WhittakerBlock.unipotentSubgroup3 := fun a =>
    (WhittakerBlock.mem_unipotentSubgroup3_iff _).mpr ⟨_, _, _, rfl⟩
  have hιU : ∀ (y : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)),
      (ι (y, a) : ↥mirabolic) =
        ⟨upperUnipotent3 a.1 a.2.2 a.2.1, unipotentSubgroup3_le_mirabolic (hN a)⟩ * (ι (y, 0, 0, 0) : ↥mirabolic) := by
    intro y a
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hιmat (y, a), hιmat (y, 0, 0, 0)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Matrix.mul_apply, Fin.sum_univ_three]
  have hUm : Measurable fun a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      (upperUnipotent3 a.1 a.2.2 a.2.1 : AdelicGL 3 (𝓞 ℚ) ℚ) :=
    (continuous_upperUnipotent3_triple.comp (continuous_id.prodMap continuous_swap)).measurable
  calc ∫⁻ p₂ : ↥P₂, HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
          ((((p₂ : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ) * G ((p₂ : ↥mirabolic) * s) ∂μ₂
      = ∫⁻ v, HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
          ((((ι v : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ) * G ((ι v : ↥mirabolic) * s)
          ∂(ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
            ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))) :=
          by rw [hμ₂ι, lintegral_map hΦs hιm]
    _ = ∫⁻ y, ∫⁻ a, HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
          ((((ι (y, a) : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ) * G ((ι (y, a) : ↥mirabolic) * s)
          ∂((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
            (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) ∂ρ :=
        lintegral_prod _ (hΦs.comp hιm).aemeasurable
    _ = ∫⁻ y, G ((ι (y, 0, 0, 0) : ↥mirabolic) * s) ∂ρ := by
        refine lintegral_congr fun y => ?_
        have hrw : ∀ a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ),
            HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
                ((((ι (y, a) : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ) * G ((ι (y, a) : ↥mirabolic) * s) =
              HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
                (((⟨upperUnipotent3 a.1 a.2.2 a.2.1, unipotentSubgroup3_le_mirabolic (hN a)⟩ : ↥mirabolic) *
                    ((ι (y, 0, 0, 0) : ↥mirabolic) * s) : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) *
                G ((ι (y, 0, 0, 0) : ↥mirabolic) * s) := by
          intro a
          rw [hιU y a, mul_assoc, hGinv _ (hN a)]
        have hmeas : Measurable fun a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
            HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
              (((⟨upperUnipotent3 a.1 a.2.2 a.2.1, unipotentSubgroup3_le_mirabolic (hN a)⟩ : ↥mirabolic) *
                  ((ι (y, 0, 0, 0) : ↥mirabolic) * s) : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) :=
          hdens.comp (measurable_subtype_coe.comp ((hUm.subtype_mk).mul_const _))
        simp_rw [hrw]
        calc ∫⁻ a, HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
                (((⟨upperUnipotent3 a.1 a.2.2 a.2.1, unipotentSubgroup3_le_mirabolic (hN a)⟩ : ↥mirabolic) *
                    ((ι (y, 0, 0, 0) : ↥mirabolic) * s) : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) *
                G ((ι (y, 0, 0, 0) : ↥mirabolic) * s)
                ∂((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
                  ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
            = (∫⁻ a, HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
                (((⟨upperUnipotent3 a.1 a.2.2 a.2.1, unipotentSubgroup3_le_mirabolic (hN a)⟩ : ↥mirabolic) *
                    ((ι (y, 0, 0, 0) : ↥mirabolic) * s) : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)
                ∂((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
                  ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
                    (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))) * G ((ι (y, 0, 0, 0) : ↥mirabolic) * s) :=
              lintegral_mul_const _ hmeas
          _ = 1 * G ((ι (y, 0, 0, 0) : ↥mirabolic) * s) :=
              congrArg (· * G ((ι (y, 0, 0, 0) : ↥mirabolic) * s)) (lintegral_density_upperUnipotent3 _)
          _ = G ((ι (y, 0, 0, 0) : ↥mirabolic) * s) := one_mul _

end QuotientUnfolding
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private def torusProfile (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic)
    (r : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) (y : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ℂ :=
  whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ
    F (torusElement y * (sec r : AdelicGL 3 (𝓞 ℚ) ℚ))

private theorem eq_mirabolic_of_forall_mem_iff (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hP : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      g ∈ P ↔ (fun j => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) =
        (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)) :
    P = mirabolic :=
  Subgroup.ext fun g => (hP g).trans Iff.rfl

attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.AdeleRing.secondCountableTopology in

private theorem sFinite_leviHaar_restrict (A : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) : SFinite (leviHaar.restrict A) :=
  inferInstance

attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel in

private theorem measurableSet_setOf_unitOutside (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    MeasurableSet {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ | UnitOutside S y} := by
  have h : ∀ q : HeightOneSpectrum (𝓞 ℚ),
      MeasurableSet {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ | q ∉ S → Valued.v (evalHom q (y : AdeleRing (𝓞 ℚ) ℚ)) = 1} := by
    intro q
    by_cases hq : q ∈ S
    · have he : {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ | q ∉ S → Valued.v (evalHom q (y : AdeleRing (𝓞 ℚ) ℚ)) = 1} = Set.univ :=
        Set.eq_univ_of_forall fun y h => (h hq).elim
      rw [he]
      exact MeasurableSet.univ
    · have he : {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ | q ∉ S → Valued.v (evalHom q (y : AdeleRing (𝓞 ℚ) ℚ)) = 1} =
          (fun y : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (y : AdeleRing (𝓞 ℚ) ℚ)) ⁻¹'
            ((fun x : AdeleRing (𝓞 ℚ) ℚ => evalHom q x) ⁻¹' {t : q.adicCompletion ℚ | Valued.v t = 1}) :=
        Set.ext fun y => ⟨fun h' => h' hq, fun h' _ => h'⟩
      rw [he]
      exact ((isClopen_setOf_valued_eq_one q).isOpen.preimage (continuous_evalHom q)).measurableSet.preimage
        measurable_units_val
  have hU : {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ | UnitOutside S y} =
      ⋂ q, {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ | q ∉ S → Valued.v (evalHom q (y : AdeleRing (𝓞 ℚ) ℚ)) = 1} :=
    Set.ext fun y => by
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact Iff.rfl
  rw [hU]
  exact MeasurableSet.iInter h

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel in

private theorem measurable_torusProfile {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : Continuous F)
    (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (r : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) :
    Measurable (torusProfile F sec r) := by
  unfold torusProfile
  exact (continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hF).measurable.comp
    (measurable_torusElement.mul_const _)

private theorem kernelMatrix_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (a x y z : A) :
    (kernelMatrix a x y z).map φ = kernelMatrix (φ a) (φ x) (φ y) (φ z) := by
  ext i j
  rw [Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp [kernelMatrix]

private theorem kernelMatrix_one_zero {A : Type} [CommRing A] : kernelMatrix (1 : A) 0 0 0 = 1 := by
  rw [Matrix.one_fin_three]
  rfl

private theorem componentAt3_torusElement_eq_one {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ} {p : HeightOneSpectrum (𝓞 ℚ)}
    (h : evalHom p (y : AdeleRing (𝓞 ℚ) ℚ) = 1) : componentAt3 (𝓞 ℚ) ℚ p (torusElement y) = 1 := by
  apply Units.ext
  rw [val_componentAt3, coe_torusElement, kernelMatrix_map, map_zero, h, kernelMatrix_one_zero, Units.val_one]

private theorem archComponent3_torusElement_eq_one {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (h : AdelicLevel.adeleArch (𝓞 ℚ) ℚ (y : AdeleRing (𝓞 ℚ) ℚ) = 1) : archComponent3 (𝓞 ℚ) ℚ (torusElement y) = 1 := by
  apply Units.ext
  rw [coe_archComponent3, RingHom.mapMatrix_apply, coe_torusElement, kernelMatrix_map, map_zero, h,
    kernelMatrix_one_zero, Units.val_one]

private theorem componentAt3_torusElement_mem {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ} {q : HeightOneSpectrum (𝓞 ℚ)}
    (h : Valued.v (evalHom q (y : AdeleRing (𝓞 ℚ) ℚ)) = 1) :
    componentAt3 (𝓞 ℚ) ℚ q (torusElement y) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q := by
  have h₁ : evalHom q (y : AdeleRing (𝓞 ℚ) ℚ) ∈ q.adicCompletionIntegers ℚ :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ q).mpr h.le
  have h₂ : evalHom q ((y⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) ∈ q.adicCompletionIntegers ℚ := by
    refine (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ q).mpr (le_of_eq ?_)
    rw [map_units_inv, map_inv₀, h, inv_one]
  refine mem_localMaximalCompact3_of_forall (fun i j => ?_) (fun i j => ?_)
  · rw [val_componentAt3, coe_torusElement, kernelMatrix_map, map_zero]
    fin_cases i <;> fin_cases j <;> simp only [kernelMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] <;> first | exact h₁ | exact zero_mem _ | exact one_mem _
  · rw [val_componentAt3_inv, coe_torusElement_inv]
    simp only [kernelMatrixInv, mul_zero, neg_zero, sub_zero]
    rw [kernelMatrix_map, map_zero]
    fin_cases i <;> fin_cases j <;> simp only [kernelMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] <;> first | exact h₂ | exact zero_mem _ | exact one_mem _

private theorem whittaker3_mul_eq_of_components (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : Continuous F)
    (hinv : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    {κ : AdelicGL 3 (𝓞 ℚ) ℚ} (hκarch : archComponent3 (𝓞 ℚ) ℚ κ = 1)
    (hκS : ∀ p ∈ S, componentAt3 (𝓞 ℚ) ℚ p κ = 1)
    (hκK : ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p κ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ F (g * κ) =
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ F g := by
  simp only [whittaker3]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  funext z
  rw [← mul_assoc, translate_eq_of_components S hF hinv hκarch hκS hκK]

private theorem torusProfile_mul_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : Continuous F)
    (hinv : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    {sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic}
    (hK : ∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (sec r : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) ∈
        localMaximalCompact3 (𝓞 ℚ) ℚ q)
    {r : Fin 2 → AdeleRing (𝓞 ℚ) ℚ} (hr : r ∈ goodLeviRows S) (x u : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hu : UnitOutsideTrivialInside S u) : torusProfile F sec r (x * u) = torusProfile F sec r x := by
  unfold torusProfile
  rw [torusElement_mul, show torusElement x * torusElement u * (sec r : AdelicGL 3 (𝓞 ℚ) ℚ) =
    torusElement x * (sec r : AdelicGL 3 (𝓞 ℚ) ℚ) *
      ((sec r : AdelicGL 3 (𝓞 ℚ) ℚ)⁻¹ * torusElement u * (sec r : AdelicGL 3 (𝓞 ℚ) ℚ)) by group]
  refine whittaker3_mul_eq_of_components S hF hinv ?_ (fun p hp => ?_) (fun p hp => ?_) _
  · rw [map_mul, map_mul, map_inv, archComponent3_torusElement_eq_one hu.2.2, mul_one, inv_mul_cancel]
  · rw [map_mul, map_mul, map_inv, componentAt3_torusElement_eq_one (hu.2.1 p hp), mul_one, inv_mul_cancel]
  · rw [map_mul, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hK r hr p hp))
      (componentAt3_torusElement_mem (hu.1 p hp))) (hK r hr p hp)

section FibreIntegral

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] {Y : Type} [MeasurableSpace Y]

end FibreIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section ProfileBounds

attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology secondCountableTopology_adelicGL3

attribute [local instance] WhittakerBlock.isHaarMeasure_unipotentHaar3

attribute [local instance] WhittakerBlock.isMulRightInvariant_unipotentHaar3

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem shellCond_torusElement_mul {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic}
    (hK : ∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    {r : Fin 2 → AdeleRing (𝓞 ℚ) ℚ} (hr : r ∈ goodLeviRows S) {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ} (hy : UnitOutside S y) :
    ShellCond S (torusElement y * (sec r : AdelicGL 3 (𝓞 ℚ) ℚ)) := by
  intro q hq
  have hk : componentAt3 (𝓞 ℚ) ℚ q (torusElement y * (sec r : AdelicGL 3 (𝓞 ℚ) ℚ)) ∈
      localMaximalCompact3 (𝓞 ℚ) ℚ q := by
    rw [map_mul]
    exact mul_mem (componentAt3_torusElement_mem (hy q hq)) (hK r hr q hq)
  have h1 : (upperUnipotent3 0 0 0 : GL (Fin 3) (q.adicCompletion ℚ)) = 1 := Units.ext Matrix.one_fin_three.symm
  exact ⟨0, 0, 0, _, hk, by rw [h1, one_mul]⟩

private theorem nnnorm_whittaker3_out {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hWn : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F (n * g)‖ =
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F g‖)
    (p : ↥mirabolic) :
    ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ F
        (((Quotient.mk'' p :
            MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic).out :
          ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ =
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ F (p : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ := by
  have h : ((Quotient.mk'' p :
        MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic).out :
      ↥mirabolic) ∈ MulAction.orbit ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) p :=
    MulAction.orbitRel_apply.mp
      (@Quotient.mk_out' _ (MulAction.orbitRel ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic) p)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
  rw [← hg, ← NNReal.coe_inj, coe_nnnorm, coe_nnnorm]
  exact hWn _ (Subgroup.mem_subgroupOf.mp g.2) _

private theorem lintegral_quotient_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (μP : Measure ↥mirabolic) (c₀ : ℝ≥0∞)
    (ν : Measure (MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic))
    (hν : ν = c₀ • Measure.map Quotient.mk''
      (μP.withDensity fun p : ↥mirabolic =>
        HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
            (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
          Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ)))
    (P₂ : Subgroup ↥mirabolic) (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ))
    (μ₂ : Measure ↥P₂) [SFinite μ₂] (c : ℝ≥0∞)
    (hfib : μP = c • fibMeasure P₂ sec
      (fun p : ↥mirabolic => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ)) μ₂ leviHaar R)
    (hsec : Measurable sec) (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ]
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιm : Measurable ι)
    (hμ₂ι : μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))))
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    {G : MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ q, G q ∂ν = c₀ * (c * ∫⁻ x in R, (modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ *
      ∫⁻ y, Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞))
          (((ι (y, 0, 0, 0) : ↥mirabolic) * sec x : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) *
        G (Quotient.mk'' ((ι (y, 0, 0, 0) : ↥mirabolic) * sec x)) ∂ρ ∂leviHaar) := by
  have hmk : Measurable (Quotient.mk'' : ↥mirabolic →
      MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic) :=
    measurable_quotient_mk''
  have hSH : MeasurableSet {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} := measurableSet_shellCond S
  have hdens := measurable_density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
    WhittakerBlock.unipotentHaar3
  have hind : Measurable fun p : ↥mirabolic =>
      Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) :=
    (measurable_const.indicator hSH).comp measurable_subtype_coe
  have hD : Measurable fun p : ↥mirabolic =>
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
        Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) :=
    (hdens.comp measurable_subtype_coe).mul hind
  have hGmk : Measurable fun p : ↥mirabolic => G (Quotient.mk'' p) := hG.comp hmk
  have hδ : Measurable fun p : ↥mirabolic => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) :=
    measurable_modulus.comp measurable_subtype_coe
  have hGi : Measurable fun p : ↥mirabolic =>
      Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
        G (Quotient.mk'' p) := hind.mul hGmk
  have hGinv : ∀ n : ↥mirabolic, (n : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ WhittakerBlock.unipotentSubgroup3 → ∀ p : ↥mirabolic,
      Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞))
            ((n * p : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * G (Quotient.mk'' (n * p)) =
        Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
          G (Quotient.mk'' p) := by
    intro n hn p
    rw [Subgroup.coe_mul, indicator_shell_unipotent_mul S hn, quotientMk_unipotent_mul hn]
  have hF : Measurable fun p : ↥mirabolic =>
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
        Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
        G (Quotient.mk'' p) := hD.mul hGmk
  rw [hν, lintegral_smul_measure, lintegral_map hG hmk, lintegral_withDensity_eq_lintegral_mul _ hD hGmk, hfib,
    lintegral_smul_measure]
  simp only [smul_eq_mul, Pi.mul_apply]
  rw [lintegral_fibMeasure P₂ hsec hδ μ₂ leviHaar R hF]
  congr 2
  refine lintegral_congr fun x => ?_
  congr 1
  exact (lintegral_congr fun p₂ => mul_assoc _ _ _).trans
    (lintegral_fibre_eq P₂ μ₂ ρ ι hιm hμ₂ι hιmat hGi hGinv (sec x))

private theorem lintegral_sq_torusProfile_ne_top (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (μP : Measure ↥mirabolic)
    {c₀ : ℝ≥0∞} (hc₀ : c₀ ≠ 0)
    (ν : Measure (MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic))
    (hν : ν = c₀ • Measure.map Quotient.mk''
      (μP.withDensity fun p : ↥mirabolic =>
        HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
            (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
          Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ)))
    (P₂ : Subgroup ↥mirabolic) (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ))
    (μ₂ : Measure ↥P₂) [SFinite μ₂] {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hfib : μP = c • fibMeasure P₂ sec
      (fun p : ↥mirabolic => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ)) μ₂ leviHaar R)
    (hsec : Measurable sec) (hgoodR : goodLeviRows S ⊆ R) (hgoodm : MeasurableSet (goodLeviRows S))
    (hK : ∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ]
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιm : Measurable ι)
    (hμ₂ι : μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))))
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hFc : Continuous F)
    (hWn : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F (n * g)‖ =
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F g‖)
    (hfin : ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ F ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤) :
    ∀ᵐ r ∂leviHaar.restrict (goodLeviRows S),
      ∫⁻ x, (‖torusProfile F sec r x‖₊ : ℝ≥0∞) ^ 2 ∂ρ.restrict {y | UnitOutside S y} ≠ ⊤ := by
  have hWc : Continuous (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ F) :=
    continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hFc
  have hιt : ∀ y : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((ι (y, 0, 0, 0) : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) = torusElement y :=
    fun y => Units.ext (by rw [hιmat]; rfl)
  have hG : Measurable fun q : MulAction.orbitRel.Quotient
      ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic =>
      ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ F ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) := by
    refine measurable_from_quotient.mpr ?_
    have h : (fun q : MulAction.orbitRel.Quotient
        ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic =>
        ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)) ∘
          Quotient.mk'' =
        fun p : ↥mirabolic => ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F (p : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) :=
      funext fun p => by simp only [Function.comp_apply, nnnorm_whittaker3_out hWn p]
    rw [h]
    exact ((hWc.measurable.comp measurable_subtype_coe).nnnorm.coe_nnreal_ennreal).pow_const 2
  rw [lintegral_quotient_eq S μP c₀ ν hν P₂ sec R μ₂ c hfib hsec ρ ι hιm hμ₂ι hιmat hG] at hfin
  simp only [nnnorm_whittaker3_out hWn, Subgroup.coe_mul, hιt] at hfin
  have hI := ENNReal.lt_top_of_mul_ne_top_right (ENNReal.lt_top_of_mul_ne_top_right hfin hc₀).ne hc0
  have hg : Measurable fun z : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      torusElement z.2 * (sec z.1 : AdelicGL 3 (𝓞 ℚ) ℚ) :=
    (measurable_torusElement.comp measurable_snd).mul (measurable_subtype_coe.comp (hsec.comp measurable_fst))
  have hJ : Measurable fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      (modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ *
        ∫⁻ y, Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞))
            (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ)) *
          ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ))‖₊ : ℝ≥0∞) ^ 2) ∂ρ := by
    refine (measurable_modulus.comp (measurable_subtype_coe.comp hsec)).inv.mul ?_
    refine Measurable.lintegral_prod_right ?_
    exact ((measurable_const.indicator (measurableSet_shellCond S)).comp hg).mul
      ((hWc.measurable.comp hg).nnnorm.coe_nnreal_ennreal.pow_const 2)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hgoodR (ae_lt_top hJ hI.ne), ae_restrict_mem hgoodm]
    with x hx hgood
  have hx' := ENNReal.lt_top_of_mul_ne_top_right hx.ne (ENNReal.inv_ne_zero.mpr (modulus_ne_top _))
  refine ne_top_of_le_ne_top hx'.ne ?_
  rw [← lintegral_indicator (measurableSet_setOf_unitOutside S)]
  refine lintegral_mono fun y => ?_
  by_cases hy : UnitOutside S y
  · rw [Set.indicator_of_mem (show y ∈ {y | UnitOutside S y} from hy),
      Set.indicator_of_mem (show torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ {g | ShellCond S g} from
        shellCond_torusElement_mul hK hgood hy), one_mul]
    exact le_rfl
  · rw [Set.indicator_of_notMem (show y ∉ {y | UnitOutside S y} from hy)]
    exact zero_le

private theorem valued_det_le_one {q : HeightOneSpectrum (𝓞 ℚ)} {M : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)}
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) : Valued.v M.det ≤ 1 := by
  let M' : Matrix (Fin 3) (Fin 3) ↥(q.adicCompletionIntegers ℚ) := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have hM' : M = (q.adicCompletionIntegers ℚ).subtype.mapMatrix M' := by
    ext i j
    rfl
  rw [hM', ← RingHom.map_det]
  exact (M'.det).2

private theorem valued_det_eq_one_of_mem {q : HeightOneSpectrum (𝓞 ℚ)} {k : GL (Fin 3) (q.adicCompletion ℚ)}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q) :
    Valued.v (Matrix.det (k : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ))) = 1 := by
  have h1 : Valued.v (Matrix.det (k : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ))) ≤ 1 := valued_det_le_one hk.1
  have h2 : Valued.v (Matrix.det
      ((k⁻¹ : GL (Fin 3) (q.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ))) ≤ 1 :=
    valued_det_le_one hk.2
  have hmul : Matrix.det (k : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) *
      Matrix.det ((k⁻¹ : GL (Fin 3) (q.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  refine le_antisymm h1 ?_
  have hv := congrArg Valued.v hmul
  rw [map_mul, map_one] at hv
  calc (1 : _) = _ := hv.symm
    _ ≤ _ := mul_le_of_le_one_right' h2

private theorem det_coe_upperUnipotent3 {A : Type*} [CommRing A] (x y z : A) :
    Matrix.det ((upperUnipotent3 x y z : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = 1 := by
  simp [upperUnipotent3, Matrix.det_fin_three]

private theorem unitOutside_of_shellCond_torusElement_mul {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic}
    (hK : ∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    {r : Fin 2 → AdeleRing (𝓞 ℚ) ℚ} (hr : r ∈ goodLeviRows S) {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (h : ShellCond S (torusElement y * (sec r : AdelicGL 3 (𝓞 ℚ) ℚ))) : UnitOutside S y := by
  intro q hq
  obtain ⟨a, b, c, k, hk, hEq⟩ := h q hq
  have hs := hK r hr q hq
  have hT : componentAt3 (𝓞 ℚ) ℚ q (torusElement y) =
      upperUnipotent3 a b c * (k * (componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹) := by
    rw [← mul_assoc, ← hEq, map_mul, mul_inv_cancel_right]
  have hk' : k * (componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q :=
    mul_mem hk (inv_mem hs)
  have hdet : Matrix.det (componentAt3 (𝓞 ℚ) ℚ q (torusElement y) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) =
      Matrix.det ((upperUnipotent3 a b c * (k * (componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹) :
        GL (Fin 3) (q.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) :=
    congrArg (fun g : GL (Fin 3) (q.adicCompletion ℚ) => Matrix.det (g : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)))
      hT
  rw [Units.val_mul, Matrix.det_mul, det_coe_upperUnipotent3, one_mul, val_componentAt3, coe_torusElement,
    kernelMatrix_map, kernelMatrix_det] at hdet
  rw [hdet]
  exact valued_det_eq_one_of_mem hk'

private theorem leviRow_mul_of_leviRow_eq {p : ↥mirabolic} (hp : leviRow p = e₂) (s : ↥mirabolic) :
    leviRow (p * s) = leviRow s := by
  have hb : bottomRow (s : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) = e₃ := s.2
  funext i
  have h0 : ((p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) :
      Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 1 0 = 0 := by
    simpa [leviRow, e₂] using congrFun hp 0
  have h1 : ((p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) :
      Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 1 1 = 1 := by
    simpa [leviRow, e₂] using congrFun hp 1
  have h2 : ((s : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2
      (Fin.castSucc i) = 0 := by
    have := congrFun hb (Fin.castSucc i)
    fin_cases i <;> simpa [bottomRow, e₃] using this
  simp only [leviRow, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2, zero_mul,
    one_mul, mul_zero, zero_add, add_zero]

private theorem whittaker3_eq_zero_of_torusProfile_ae_zero (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (μP : Measure ↥mirabolic) (c₀ : ℝ≥0∞)
    (ν : Measure (MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic))
    (hν : ν = c₀ • Measure.map Quotient.mk''
      (μP.withDensity fun p : ↥mirabolic =>
        HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
            (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
          Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ)))
    (P₂ : Subgroup ↥mirabolic) (hP₂ : ∀ p : ↥mirabolic, p ∈ P₂ ↔ leviRow p = e₂)
    (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ))
    (μ₂ : Measure ↥P₂) [SFinite μ₂] {c : ℝ≥0∞}
    (hfib : μP = c • fibMeasure P₂ sec
      (fun p : ↥mirabolic => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ)) μ₂ leviHaar R)
    (hsec : Measurable sec) (hsecrow : ∀ r ∈ R, leviRow (sec r) = r)
    (hshell : ∀ p : ↥mirabolic, OnShell S p → leviRow p ∈ goodLeviRows S) (hgoodm : MeasurableSet (goodLeviRows S))
    (hK : ∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ]
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιm : Measurable ι)
    (hμ₂ι : μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))))
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hΦ₀ : IsSlabDomain a b Φ₀)
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hFaut : F ∈ automorphicSubmodule ω a b Φ₀) (hFc : Continuous F)
    (hWn : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F (n * g)‖ =
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F g‖)
    {cF : ℝ} (hcF : 0 < cF)
    (hsq : ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ F ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν =
      ENNReal.ofReal (cF * ‖toL2 ω a b Φ₀ ⟨F, hFaut⟩‖ ^ 2))
    (h0 : ∀ᵐ r ∂leviHaar.restrict (goodLeviRows S),
      torusProfile F sec r =ᵐ[ρ.restrict {y | UnitOutside S y}] 0) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ F 1 = 0 := by
  have hWc : Continuous (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ F) :=
    continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hFc
  have hιt : ∀ y : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((ι (y, 0, 0, 0) : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) = torusElement y :=
    fun y => Units.ext (by rw [hιmat]; rfl)
  have hG : Measurable fun q : MulAction.orbitRel.Quotient
      ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic =>
      ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ F ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) := by
    refine measurable_from_quotient.mpr ?_
    have h : (fun q : MulAction.orbitRel.Quotient
        ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic =>
        ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)) ∘
          Quotient.mk'' =
        fun p : ↥mirabolic => ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F (p : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) :=
      funext fun p => by simp only [Function.comp_apply, nnnorm_whittaker3_out hWn p]
    rw [h]
    exact ((hWc.measurable.comp measurable_subtype_coe).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hI := lintegral_quotient_eq S μP c₀ ν hν P₂ sec R μ₂ c hfib hsec ρ ι hιm hμ₂ι hιmat hG
  simp only [nnnorm_whittaker3_out hWn, Subgroup.coe_mul, hιt] at hI
  have hg : Measurable fun z : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      torusElement z.2 * (sec z.1 : AdelicGL 3 (𝓞 ℚ) ℚ) :=
    (measurable_torusElement.comp measurable_snd).mul (measurable_subtype_coe.comp (hsec.comp measurable_fst))
  have hJm : Measurable fun z : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞))
          (torusElement z.2 * (sec z.1 : AdelicGL 3 (𝓞 ℚ) ℚ)) *
        ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F (torusElement z.2 * (sec z.1 : AdelicGL 3 (𝓞 ℚ) ℚ))‖₊ : ℝ≥0∞) ^ 2) :=
    ((measurable_const.indicator (measurableSet_shellCond S)).comp hg).mul
      ((hWc.measurable.comp hg).nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hJ : Measurable fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      (modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ *
        ∫⁻ y, Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞))
            (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ)) *
          ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ))‖₊ : ℝ≥0∞) ^ 2) ∂ρ :=
    (measurable_modulus.comp (measurable_subtype_coe.comp hsec)).inv.mul (Measurable.lintegral_prod_right hJm)
  have hzero : ∀ᵐ x ∂leviHaar.restrict R,
      (modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ *
        ∫⁻ y, Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞))
            (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ)) *
          ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ))‖₊ : ℝ≥0∞) ^ 2) ∂ρ =
        0 := by
    refine (ae_restrict_iff (hJ (measurableSet_singleton 0))).mpr ?_
    filter_upwards [(ae_restrict_iff' hgoodm).mp h0] with x hx hxR
    refine mul_eq_zero_of_right _ ((lintegral_congr_ae ?_).trans lintegral_zero)
    by_cases hgood : x ∈ goodLeviRows S
    · filter_upwards [(ae_restrict_iff' (measurableSet_setOf_unitOutside S)).mp (hx hgood)] with y hy
      by_cases hyC : UnitOutside S y
      · have h0y : whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ)) = 0 := hy hyC
        rw [h0y, nnnorm_zero, ENNReal.coe_zero, zero_pow two_ne_zero, mul_zero]
      · rw [Set.indicator_of_notMem (fun h => hyC (unitOutside_of_shellCond_torusElement_mul hK hgood h)), zero_mul]
    · refine Filter.Eventually.of_forall fun y => ?_
      beta_reduce
      rw [Set.indicator_of_notMem ?_, zero_mul]
      intro hsc
      apply hgood
      have hsc' : OnShell S ((ι (y, 0, 0, 0) : ↥mirabolic) * sec x) := by
        intro q hq
        rw [Subgroup.coe_mul, hιt]
        exact hsc q hq
      have hr := hshell _ hsc'
      rwa [leviRow_mul_of_leviRow_eq ((hP₂ _).mp (ι (y, 0, 0, 0)).2) (sec x), hsecrow x hxR] at hr
  have hR0 := (lintegral_congr_ae hzero).trans lintegral_zero
  rw [hR0, mul_zero, mul_zero, hsq] at hI
  have hle : cF * ‖toL2 ω a b Φ₀ ⟨F, hFaut⟩‖ ^ 2 ≤ cF * 0 := by
    rw [mul_zero]
    exact ENNReal.ofReal_eq_zero.mp hI
  have h0L : toL2 ω a b Φ₀ ⟨F, hFaut⟩ = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp
      (le_antisymm (le_of_mul_le_mul_left hle hcF) (sq_nonneg _)))
  have hF0 : F = 0 := eq_zero_of_toL2_eq_zero_of_continuous ω a b Φ₀ hΦ₀ F hFaut hFc h0L
  subst hF0
  simp only [whittaker3, Pi.zero_apply, zero_mul, integral_zero]

end ProfileBounds
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section PairClause

local notation "𝓦" => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
  NumberField.StandardAddChar.psiQ

attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology secondCountableTopology_adelicGL3

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private def crossProfile (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (f f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) (h : AdelicGL 3 (𝓞 ℚ) ℚ)
    (x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) : ℂ :=
  ∫ y in {y | UnitOutside S y}, (starRingEnd ℂ) (𝓦 f (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ) * h)) *
    𝓦 f' (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ)) ∂ρ

section BochnerUnfolding

attribute [local instance] WhittakerBlock.isHaarMeasure_unipotentHaar3

attribute [local instance] WhittakerBlock.isMulRightInvariant_unipotentHaar3

private theorem measurable_density_mul_indicator_shell (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    Measurable fun p : ↥mirabolic =>
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
        Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) :=
  ((measurable_density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
      WhittakerBlock.unipotentHaar3).comp measurable_subtype_coe).mul
    ((measurable_const.indicator (measurableSet_shellCond S)).comp measurable_subtype_coe)

private theorem measurable_density_mirabolic :
    Measurable fun p : ↥mirabolic =>
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 (p : AdelicGL 3 (𝓞 ℚ) ℚ) :=
  (measurable_density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
    WhittakerBlock.unipotentHaar3).comp measurable_subtype_coe

private theorem upperUnipotent3_swap_mem
    (a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) :
    (upperUnipotent3 a.1 a.2.2 a.2.1 : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ WhittakerBlock.unipotentSubgroup3 :=
  (WhittakerBlock.mem_unipotentSubgroup3_iff _).mpr ⟨_, _, _, rfl⟩

private theorem chart_eq_unipotent_mul_chart_zero (P₂ : Subgroup ↥mirabolic)
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    (y : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) :
    (ι (y, a) : ↥mirabolic) =
      ⟨upperUnipotent3 a.1 a.2.2 a.2.1, unipotentSubgroup3_le_mirabolic (upperUnipotent3_swap_mem a)⟩ *
        (ι (y, 0, 0, 0) : ↥mirabolic) := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, hιmat (y, a), hιmat (y, 0, 0, 0)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Matrix.mul_apply, Fin.sum_univ_three]

private theorem measurable_upperUnipotent3_swap :
    Measurable fun a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      (upperUnipotent3 a.1 a.2.2 a.2.1 : AdelicGL 3 (𝓞 ℚ) ℚ) :=
  (continuous_upperUnipotent3_triple.comp (continuous_id.prodMap continuous_swap)).measurable

private theorem ae_density_unipotent_mul_lt_top (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∀ᵐ a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)
        ∂((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
          (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))),
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        (upperUnipotent3 a.1 a.2.2 a.2.1 * g) < ⊤ :=
  ae_lt_top ((measurable_density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
      WhittakerBlock.unipotentHaar3).comp (measurable_upperUnipotent3_swap.mul_const g))
    (by rw [lintegral_density_upperUnipotent3 g]; exact ENNReal.one_ne_top)

private theorem ae_density_mul_indicator_shell_lt_top (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (μP : Measure ↥mirabolic) (P₂ : Subgroup ↥mirabolic) (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic)
    (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) (μ₂ : Measure ↥P₂) [SFinite μ₂] (c : ℝ≥0∞)
    (hfib : μP = c • fibMeasure P₂ sec
      (fun p : ↥mirabolic => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ)) μ₂ leviHaar R)
    (hsec : Measurable sec) (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιm : Measurable ι)
    (hμ₂ι : μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))))
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1]) :
    ∀ᵐ p : ↥mirabolic ∂μP,
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
        Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) < ⊤ := by

  suffices hdens : ∀ᵐ p : ↥mirabolic ∂μP,
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        (p : AdelicGL 3 (𝓞 ℚ) ℚ) < ⊤ by
    filter_upwards [hdens] with p hp
    refine ENNReal.mul_lt_top hp ?_
    by_cases hs : ShellCond S (p : AdelicGL 3 (𝓞 ℚ) ℚ)
    · rw [Set.indicator_of_mem (show (p : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} from hs)]
      exact ENNReal.one_lt_top
    · rw [Set.indicator_of_notMem (show (p : AdelicGL 3 (𝓞 ℚ) ℚ) ∉ {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} from hs)]
      exact ENNReal.zero_lt_top
  have hset : MeasurableSet {p : ↥mirabolic | HaarQuotient.density WhittakerBlock.unipotentSubgroup3
      WhittakerBlock.unipotentHaar3 (p : AdelicGL 3 (𝓞 ℚ) ℚ) < ⊤} :=
    measurable_density_mirabolic measurableSet_Iio
  have hsetP : MeasurableSet {z : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × ↥P₂ | HaarQuotient.density
      WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((((z.2 : ↥mirabolic) * sec z.1 : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ) < ⊤} :=
    (measurable_fibMap P₂ hsec) hset
  rw [hfib]
  refine Measure.ae_smul_measure ?_ c
  rw [fibMeasure, ae_map_iff (measurable_fibMap P₂ hsec).aemeasurable hset, Measure.ae_prod_iff_ae_ae hsetP]
  refine Filter.Eventually.of_forall fun x => ?_
  have hsetQ : MeasurableSet {p₂ : ↥P₂ | HaarQuotient.density WhittakerBlock.unipotentSubgroup3
      WhittakerBlock.unipotentHaar3 ((((p₂ : ↥mirabolic) * sec x : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ) < ⊤} :=
    (measurable_subtype_coe.mul_const (sec x)) hset
  show ∀ᵐ p₂ : ↥P₂ ∂μ₂, HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
    ((((p₂ : ↥mirabolic) * sec x : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ) < ⊤
  rw [hμ₂ι, ae_map_iff hιm.aemeasurable hsetQ]
  have hset' : MeasurableSet
      {v : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) |
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((((ι v : ↥mirabolic) * sec x : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ) < ⊤} :=
    ((measurable_subtype_coe.comp hιm).mul_const (sec x)) hset
  rw [Measure.ae_prod_iff_ae_ae hset']
  refine Filter.Eventually.of_forall fun y => ?_
  filter_upwards [ae_density_unipotent_mul_lt_top
    ((((ι (y, 0, 0, 0) : ↥mirabolic) * sec x : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ)] with a ha
  show HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
      ((((ι (y, a) : ↥mirabolic) * sec x : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ) < ⊤
  rw [chart_eq_unipotent_mul_chart_zero P₂ ι hιmat y a, mul_assoc, Subgroup.coe_mul]
  exact ha

private theorem integral_density_smul_fibre_eq (P₂ : Subgroup ↥mirabolic) (μ₂ : Measure ↥P₂)
    (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ]
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιm : Measurable ι)
    (hμ₂ι : μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))))
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    {Φ : ↥mirabolic → ℂ} (hΦ : Measurable Φ)
    (hΦinv : ∀ n : ↥mirabolic, (n : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ WhittakerBlock.unipotentSubgroup3 → ∀ p, Φ (n * p) = Φ p)
    (s : ↥mirabolic)
    (hint : Integrable (fun p₂ : ↥P₂ =>
      (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((((p₂ : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal • Φ ((p₂ : ↥mirabolic) * s)) μ₂) :
    ∫ p₂ : ↥P₂, (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((((p₂ : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal • Φ ((p₂ : ↥mirabolic) * s) ∂μ₂ =
      ∫ y, Φ ((ι (y, 0, 0, 0) : ↥mirabolic) * s) ∂ρ := by
  have hΨs : Measurable fun p₂ : ↥P₂ =>
      (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((((p₂ : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal • Φ ((p₂ : ↥mirabolic) * s) :=
    ((measurable_density_mirabolic.comp (measurable_subtype_coe.mul_const s)).ennreal_toReal).smul
      (hΦ.comp (measurable_subtype_coe.mul_const s))
  have hμ₂ι' := hμ₂ι
  subst hμ₂ι'
  have hint' : Integrable
      (fun v : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) =>
      (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((((ι v : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal • Φ ((ι v : ↥mirabolic) * s))
      (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
        ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))) :=
    (integrable_map_measure hΨs.aestronglyMeasurable hιm.aemeasurable).mp hint
  rw [integral_map hιm.aemeasurable hΨs.aestronglyMeasurable, integral_prod _ hint']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ∫ a, (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
      ((((ι (y, a) : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal • Φ ((ι (y, a) : ↥mirabolic) * s)
      ∂((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
        (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) = Φ ((ι (y, 0, 0, 0) : ↥mirabolic) * s)
  have hrw : ∀ a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ),
      (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((((ι (y, a) : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal • Φ ((ι (y, a) : ↥mirabolic) * s) =
      (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        (upperUnipotent3 a.1 a.2.2 a.2.1 *
          ((((ι (y, 0, 0, 0) : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ))).toReal •
        Φ ((ι (y, 0, 0, 0) : ↥mirabolic) * s) := by
    intro a
    rw [chart_eq_unipotent_mul_chart_zero P₂ ι hιmat y a, mul_assoc, hΦinv _ (upperUnipotent3_swap_mem a),
      Subgroup.coe_mul]
  have hfm : AEMeasurable (fun a : AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        (upperUnipotent3 a.1 a.2.2 a.2.1 * ((((ι (y, 0, 0, 0) : ↥mirabolic) * s : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ)))
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
        (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) :=
    ((measurable_density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
      WhittakerBlock.unipotentHaar3).comp (measurable_upperUnipotent3_swap.mul_const _)).aemeasurable
  simp_rw [hrw]
  rw [integral_smul_const]
  rw [integral_toReal hfm (ae_density_unipotent_mul_lt_top _), lintegral_density_upperUnipotent3, ENNReal.toReal_one,
    one_smul]

private theorem integral_density_smul_fibMeasure_eq (P₂ : Subgroup ↥mirabolic)
    (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) (μ₂ : Measure ↥P₂)
    [SFinite μ₂] (hsec : Measurable sec) (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ]
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιm : Measurable ι)
    (hμ₂ι : μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))))
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    {Φ : ↥mirabolic → ℂ} (hΦ : Measurable Φ)
    (hΦinv : ∀ n : ↥mirabolic, (n : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ WhittakerBlock.unipotentSubgroup3 → ∀ p, Φ (n * p) = Φ p)
    (hint : Integrable (fun p : ↥mirabolic =>
        (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
          (p : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal • Φ p)
      (fibMeasure P₂ sec (fun p : ↥mirabolic => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))
        μ₂ leviHaar R)) :
    ∫ p : ↥mirabolic, (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        (p : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal • Φ p
      ∂fibMeasure P₂ sec (fun p : ↥mirabolic => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))
        μ₂ leviHaar R =
      ∫ x in R, ((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal •
        ∫ y, Φ ((ι (y, 0, 0, 0) : ↥mirabolic) * sec x) ∂ρ ∂leviHaar := by
  haveI : SFinite (leviHaar.restrict R) := sFinite_leviHaar_restrict R
  have hΨ : Measurable fun p : ↥mirabolic =>
      (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        (p : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal • Φ p :=
    measurable_density_mirabolic.ennreal_toReal.smul hΦ
  have hw : Measurable fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      (modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ :=
    ((measurable_modulus.comp measurable_subtype_coe).comp hsec).inv
  have hw_ne : ∀ x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ,
      (modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ ≠ 0 :=
    fun x => ENNReal.inv_ne_zero.mpr (modulus_ne_top _)
  have hw_lt : ∀ᵐ x ∂leviHaar.restrict R,
      (modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.inv_lt_top.mpr (modulus_pos _)
  rw [fibMeasure] at hint ⊢
  have hint' : Integrable (fun z : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × ↥P₂ =>
      (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((((z.2 : ↥mirabolic) * sec z.1 : ↥mirabolic)) : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal •
        Φ ((z.2 : ↥mirabolic) * sec z.1))
      (((leviHaar.restrict R).withDensity fun x =>
        (modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).prod μ₂) :=
    (integrable_map_measure hΨ.aestronglyMeasurable (measurable_fibMap P₂ hsec).aemeasurable).mp hint
  rw [integral_map (measurable_fibMap P₂ hsec).aemeasurable hΨ.aestronglyMeasurable, integral_prod _ hint',
    integral_withDensity_eq_integral_toReal_smul₀ hw.aemeasurable hw_lt]

  have hslice := hint'.prod_right_ae
  rw [ae_withDensity_iff hw] at hslice
  refine integral_congr_ae ?_
  filter_upwards [hslice] with x hx
  congr 1
  exact integral_density_smul_fibre_eq P₂ μ₂ ρ ι hιm hμ₂ι hιmat hΦ hΦinv (sec x) (hx (hw_ne x))

private theorem toReal_density_mul_indicator_smul (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : ↥mirabolic) (z : ℂ) :
    (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
        Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞))
          (p : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal • z =
      (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        (p : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal •
        (Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℂ)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) * z) := by
  rw [ENNReal.toReal_mul, mul_smul]
  congr 1
  by_cases hp : ShellCond S p
  · rw [Set.indicator_of_mem (show (p : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} from hp),
      Set.indicator_of_mem (show (p : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} from hp),
      ENNReal.toReal_one, one_smul, one_mul]
  · rw [Set.indicator_of_notMem (show (p : AdelicGL 3 (𝓞 ℚ) ℚ) ∉ {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} from hp),
      Set.indicator_of_notMem (show (p : AdelicGL 3 (𝓞 ℚ) ℚ) ∉ {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} from hp),
      ENNReal.toReal_zero, zero_smul, zero_mul]

private theorem indicator_shell_complex_unipotent_mul (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {n : AdelicGL 3 (𝓞 ℚ) ℚ} (hn : n ∈ WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℂ)) (n * g) =
      Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℂ)) g := by
  by_cases hg : ShellCond S g
  · rw [Set.indicator_of_mem (show n * g ∈ {g | ShellCond S g} from (shellCond_mul_left_iff S n hn g).mpr hg),
      Set.indicator_of_mem (show g ∈ {g | ShellCond S g} from hg)]
  · rw [Set.indicator_of_notMem (show n * g ∉ {g | ShellCond S g} from
        fun h => hg ((shellCond_mul_left_iff S n hn g).mp h)),
      Set.indicator_of_notMem (show g ∉ {g | ShellCond S g} from hg)]

end BochnerUnfolding
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem integral_quotient_eq
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (μP : Measure ↥mirabolic) (c₀ : ℝ≥0∞)
    (ν : Measure (MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic))
    (hν : ν = c₀ • Measure.map Quotient.mk''
      (μP.withDensity fun p : ↥mirabolic =>
        HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
            (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
          Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ)))
    (P₂ : Subgroup ↥mirabolic) (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ))
    (μ₂ : Measure ↥P₂) [SFinite μ₂] (c : ℝ≥0∞)
    (hfib : μP = c • fibMeasure P₂ sec
      (fun p : ↥mirabolic => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ)) μ₂ leviHaar R)
    (hsec : Measurable sec) (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ]
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιm : Measurable ι)
    (hμ₂ι : μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))))
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    {G : MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic → ℂ}
    (hG : Measurable G) (hGi : Integrable G ν) :
    ∫ q, G q ∂ν = c₀.toReal * (c.toReal * ∫ x in R,
      ((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
      ∫ y, Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℂ))
          (((ι (y, 0, 0, 0) : ↥mirabolic) * sec x : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) *
        G (Quotient.mk'' ((ι (y, 0, 0, 0) : ↥mirabolic) * sec x)) ∂ρ ∂leviHaar) := by
  have hmk : Measurable (Quotient.mk'' : ↥mirabolic →
      MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic) :=
    measurable_quotient_mk''
  have hD := measurable_density_mul_indicator_shell S
  have hDfin := ae_density_mul_indicator_shell_lt_top S μP P₂ sec R μ₂ c hfib hsec ρ ι hιm hμ₂ι hιmat
  have hΦ : Measurable fun p : ↥mirabolic =>
      Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℂ)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
        G (Quotient.mk'' p) :=
    ((measurable_const.indicator (measurableSet_shellCond S)).comp measurable_subtype_coe).mul (hG.comp hmk)
  have hΦinv : ∀ n : ↥mirabolic, (n : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ WhittakerBlock.unipotentSubgroup3 → ∀ p : ↥mirabolic,
      Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℂ))
            ((n * p : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * G (Quotient.mk'' (n * p)) =
        Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℂ)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
          G (Quotient.mk'' p) := by
    intro n hn p
    rw [Subgroup.coe_mul, indicator_shell_complex_unipotent_mul S hn, quotientMk_unipotent_mul hn]

  have hGi₁ := hGi
  rw [hν] at hGi₁
  rw [hν, integral_smul_measure, integral_map hmk.aemeasurable hG.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hD.aemeasurable hDfin, hfib, integral_smul_measure]
  simp_rw [toReal_density_mul_indicator_smul S]

  by_cases h₀ : c₀.toReal = 0
  · simp [h₀]
  by_cases h₁ : c.toReal = 0
  · simp [h₁]
  obtain ⟨hc₀, hc₀top⟩ := ENNReal.toReal_ne_zero.mp h₀
  obtain ⟨hc, hctop⟩ := ENNReal.toReal_ne_zero.mp h₁

  have hGi₂ : Integrable (fun p : ↥mirabolic =>
      (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
          (p : AdelicGL 3 (𝓞 ℚ) ℚ)).toReal •
        (Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℂ)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
          G (Quotient.mk'' p)))
      (fibMeasure P₂ sec (fun p : ↥mirabolic => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))
        μ₂ leviHaar R) := by
    have h₂ := (integrable_smul_measure hc₀ hc₀top).mp hGi₁
    have h₃ := (integrable_map_measure hG.aestronglyMeasurable hmk.aemeasurable).mp h₂
    have h₄ := (integrable_withDensity_iff_integrable_smul' hD hDfin).mp h₃
    rw [hfib] at h₄
    refine ((integrable_smul_measure hc hctop).mp h₄).congr (Filter.Eventually.of_forall fun p => ?_)
    exact toReal_density_mul_indicator_smul S p _
  rw [integral_density_smul_fibMeasure_eq P₂ sec R μ₂ hsec ρ ι hιm hμ₂ι hιmat hΦ hΦinv hGi₂]
  simp only [Complex.real_smul]

private theorem norm_psiQ (t : AdeleRing (𝓞 ℚ) ℚ) : ‖NumberField.StandardAddChar.psiQ t‖ = 1 :=
  NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ NumberField.StandardAddChar.isGlobalAddChar_psiQ t

private theorem conj_psiQ (t : AdeleRing (𝓞 ℚ) ℚ) :
    (starRingEnd ℂ) (NumberField.StandardAddChar.psiQ t) = NumberField.StandardAddChar.psiQ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (norm_psiQ t)]

private theorem conj_psiQ_mul_self (w : AdeleRing (𝓞 ℚ) ℚ) :
    (starRingEnd ℂ) (NumberField.StandardAddChar.psiQ w) * NumberField.StandardAddChar.psiQ w = 1 := by
  rw [Complex.conj_mul', norm_psiQ]
  simp

private def columnUnipotent (t : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  upperUnipotent3 0 (t 1) (t 0)

private def leviBlock (p : ↥mirabolic) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  fun i j => ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) (Fin.castSucc i) (Fin.castSucc j)

private theorem coe_mirabolic_two_zero (p : ↥mirabolic) :
    ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 0 = 0 := by
  have hb : bottomRow (p : AdelicGL 3 (𝓞 ℚ) ℚ) = e₃ := p.2
  simpa [bottomRow, e₃] using congrFun hb 0

private theorem coe_mirabolic_two_one (p : ↥mirabolic) :
    ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 1 = 0 := by
  have hb : bottomRow (p : AdelicGL 3 (𝓞 ℚ) ℚ) = e₃ := p.2
  simpa [bottomRow, e₃] using congrFun hb 1

private theorem coe_mirabolic_two_two (p : ↥mirabolic) :
    ((p : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 2 = 1 := by
  have hb : bottomRow (p : AdelicGL 3 (𝓞 ℚ) ℚ) = e₃ := p.2
  simpa [bottomRow, e₃] using congrFun hb 2

private theorem leviBlock_mul (p s : ↥mirabolic) : leviBlock (p * s) = leviBlock p * leviBlock s := by
  have h0 := coe_mirabolic_two_zero s
  have h1 := coe_mirabolic_two_one s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviBlock, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h0, h1]

private theorem leviBlock_one : leviBlock 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviBlock]

private theorem leviBlock_mul_leviBlock_inv (p : ↥mirabolic) : leviBlock p * leviBlock p⁻¹ = 1 := by
  rw [← leviBlock_mul, mul_inv_cancel, leviBlock_one]

private theorem leviRow_mul_eq_vecMul (p s : ↥mirabolic) : leviRow (p * s) = leviRow p ᵥ* leviBlock s := by
  have h0 := coe_mirabolic_two_zero s
  have h1 := coe_mirabolic_two_one s
  funext j
  fin_cases j <;>
    simp [leviRow, leviBlock, Matrix.vecMul, dotProduct, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_two, h0, h1]

private theorem mul_columnUnipotent (m : ↥mirabolic) (t : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) :
    (m : AdelicGL 3 (𝓞 ℚ) ℚ) * columnUnipotent t =
      upperUnipotent3 0 (leviRow m ⬝ᵥ t)
          (((m : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 0 0 * t 0 +
            ((m : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 0 1 * t 1) *
        (m : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  have h0 := coe_mirabolic_two_zero m
  have h1 := coe_mirabolic_two_one m
  have h2 := coe_mirabolic_two_two m
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [columnUnipotent, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, leviRow,
      dotProduct, h0, h1, h2] <;>
    ring

private theorem whittaker3_mul_columnUnipotent {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hFN : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      𝓦 F (upperUnipotent3 x y z * g) = NumberField.StandardAddChar.psiQ (x + y) * 𝓦 F g)
    (m : ↥mirabolic) (t : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) :
    𝓦 F ((m : AdelicGL 3 (𝓞 ℚ) ℚ) * columnUnipotent t) =
      NumberField.StandardAddChar.psiQ (leviRow m ⬝ᵥ t) * 𝓦 F (m : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  rw [mul_columnUnipotent, hFN, zero_add]

private theorem norm_whittaker3_mul_columnUnipotent {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hFN : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      𝓦 F (upperUnipotent3 x y z * g) = NumberField.StandardAddChar.psiQ (x + y) * 𝓦 F g)
    (m : ↥mirabolic) (t : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) :
    ‖𝓦 F ((m : AdelicGL 3 (𝓞 ℚ) ℚ) * columnUnipotent t)‖ = ‖𝓦 F (m : AdelicGL 3 (𝓞 ℚ) ℚ)‖ := by
  rw [whittaker3_mul_columnUnipotent hFN, norm_mul, norm_psiQ, one_mul]

private theorem whittaker3_translateRight (pins : AutomorphicForm.CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ (SlabL2.translateRight h F) g = whittaker3 pins ψ F (g * h) := by
  simp only [whittaker3, SlabL2.translateRight_apply, mul_assoc]

private theorem translateRight_one_eq (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : translateRight 1 F = F :=
  funext fun g => by rw [translateRight_apply, mul_one]

private theorem conj_whittaker3_out_mul_whittaker3_out {F₁ F₂ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF₁ : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      𝓦 F₁ (upperUnipotent3 x y z * g) = NumberField.StandardAddChar.psiQ (x + y) * 𝓦 F₁ g)
    (hF₂ : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      𝓦 F₂ (upperUnipotent3 x y z * g) = NumberField.StandardAddChar.psiQ (x + y) * 𝓦 F₂ g)
    (m : AdelicGL 3 (𝓞 ℚ) ℚ) (p : ↥mirabolic) :
    (starRingEnd ℂ) (𝓦 F₁ ((((Quotient.mk'' p :
          MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic).out :
            ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * m)) *
        𝓦 F₂ (((Quotient.mk'' p :
          MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic).out :
            ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) =
      (starRingEnd ℂ) (𝓦 F₁ ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * m)) * 𝓦 F₂ (p : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine apply_out_mk (H := WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic)
    (h := fun r : ↥mirabolic => (starRingEnd ℂ) (𝓦 F₁ ((r : AdelicGL 3 (𝓞 ℚ) ℚ) * m)) * 𝓦 F₂ (r : AdelicGL 3 (𝓞 ℚ) ℚ))
    (fun n hn q => ?_) p
  obtain ⟨x, y, z, hxyz⟩ :=
    (WhittakerBlock.mem_unipotentSubgroup3_iff _).1 (Subgroup.mem_subgroupOf.mp hn)
  simp only [Subgroup.coe_mul, hxyz, mul_assoc, hF₁, hF₂, map_mul]
  linear_combination ((starRingEnd ℂ) (𝓦 F₁ ((q : AdelicGL 3 (𝓞 ℚ) ℚ) * m)) * 𝓦 F₂ (q : AdelicGL 3 (𝓞 ℚ) ℚ)) *
    conj_psiQ_mul_self (x + y)

private theorem nnnorm_psiQ (w : AdeleRing (𝓞 ℚ) ℚ) : ‖NumberField.StandardAddChar.psiQ w‖₊ = 1 :=
  NNReal.eq (by rw [coe_nnnorm, norm_psiQ, NNReal.coe_one])

private theorem nnnorm_conj_eq (z : ℂ) : ‖(starRingEnd ℂ) z‖₊ = ‖z‖₊ :=
  NNReal.eq (by rw [coe_nnnorm, coe_nnnorm, Complex.norm_conj])

private theorem nnnorm_whittaker3_out_mul {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      𝓦 F (upperUnipotent3 x y z * g) = NumberField.StandardAddChar.psiQ (x + y) * 𝓦 F g)
    (m : AdelicGL 3 (𝓞 ℚ) ℚ) (p : ↥mirabolic) :
    ‖𝓦 F ((((Quotient.mk'' p :
        MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic).out :
          ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * m)‖₊ = ‖𝓦 F ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * m)‖₊ := by
  refine apply_out_mk (H := WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic)
    (h := fun r : ↥mirabolic => ‖𝓦 F ((r : AdelicGL 3 (𝓞 ℚ) ℚ) * m)‖₊) (fun n hn q => ?_) p
  obtain ⟨x, y, z, hxyz⟩ :=
    (WhittakerBlock.mem_unipotentSubgroup3_iff _).1 (Subgroup.mem_subgroupOf.mp hn)
  simp only [Subgroup.coe_mul, hxyz, mul_assoc, hF, nnnorm_mul, nnnorm_psiQ, one_mul]

private theorem measurable_nnnorm_whittaker3_out_mul_sq {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hFc : Continuous F)
    (hF : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      𝓦 F (upperUnipotent3 x y z * g) = NumberField.StandardAddChar.psiQ (x + y) * 𝓦 F g)
    (m : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Measurable fun q : MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic)
        ↥mirabolic =>
      ((‖𝓦 F (((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * m)‖₊ : ℝ≥0∞) ^ 2) := by
  have hW : Continuous (𝓦 F) :=
    continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hFc
  refine measurable_from_quotient.mpr ?_
  have e : (fun q : MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic)
        ↥mirabolic => ((‖𝓦 F (((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * m)‖₊ : ℝ≥0∞) ^ 2)) ∘ Quotient.mk'' =
      fun p : ↥mirabolic => ((‖𝓦 F ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * m)‖₊ : ℝ≥0∞) ^ 2) :=
    funext fun p => by
      simp only [Function.comp_apply]
      rw [nnnorm_whittaker3_out_mul hF m p]
  rw [e]
  exact ((hW.measurable.comp (measurable_subtype_coe.mul_const m)).nnnorm.coe_nnreal_ennreal).pow_const 2

private theorem measurable_conj_whittaker3_out_mul {F₁ F₂ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF₁c : Continuous F₁)
    (hF₂c : Continuous F₂)
    (hF₁ : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      𝓦 F₁ (upperUnipotent3 x y z * g) = NumberField.StandardAddChar.psiQ (x + y) * 𝓦 F₁ g)
    (hF₂ : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      𝓦 F₂ (upperUnipotent3 x y z * g) = NumberField.StandardAddChar.psiQ (x + y) * 𝓦 F₂ g)
    (m : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Measurable fun q : MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic)
        ↥mirabolic =>
      (starRingEnd ℂ) (𝓦 F₁ (((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * m)) *
        𝓦 F₂ ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  have hW₁ : Continuous (𝓦 F₁) :=
    continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hF₁c
  have hW₂ : Continuous (𝓦 F₂) :=
    continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hF₂c
  refine measurable_from_quotient.mpr ?_
  have e : (fun q : MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic)
        ↥mirabolic =>
        (starRingEnd ℂ) (𝓦 F₁ (((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * m)) *
          𝓦 F₂ ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)) ∘ Quotient.mk'' =
      fun p : ↥mirabolic =>
        (starRingEnd ℂ) (𝓦 F₁ ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * m)) * 𝓦 F₂ (p : AdelicGL 3 (𝓞 ℚ) ℚ) :=
    funext fun p => by
      simp only [Function.comp_apply]
      exact conj_whittaker3_out_mul_whittaker3_out hF₁ hF₂ m p
  rw [e]
  exact (Complex.continuous_conj.measurable.comp
      (hW₁.measurable.comp (measurable_subtype_coe.mul_const m))).mul
    (hW₂.measurable.comp measurable_subtype_coe)

private theorem ennreal_mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with hab | hba
  · calc a * b ≤ b * b := mul_le_mul' hab le_rfl
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := mul_le_mul' le_rfl hba
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

private theorem componentAt3_columnUnipotent (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {t : Fin 2 → AdeleRing (𝓞 ℚ) ℚ}
    (ht : ∀ i, ZeroOutside S (t i)) {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ∉ S) :
    componentAt3 (𝓞 ℚ) ℚ q (columnUnipotent t) = 1 := by
  have h0 : evalHom q (t 0) = 0 := ht 0 q hq
  have h1 : evalHom q (t 1) = 0 := ht 1 q hq
  apply Units.ext
  ext i j
  rw [componentAt3_apply]
  fin_cases i <;> fin_cases j <;> simp [columnUnipotent, h0, h1]

private theorem zeroOutside_mulVec (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) {t : Fin 2 → AdeleRing (𝓞 ℚ) ℚ} (ht : ∀ i, ZeroOutside S (t i))
    (i : Fin 2) : ZeroOutside S ((M *ᵥ t) i) := by
  intro q hq
  have h : ∀ j, evalHom q (t j) = 0 := fun j => ht j q hq
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, map_add, map_mul, h, mul_zero, add_zero]

private theorem integral_inv_modulus_mul_integral_indicator_shell_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (P₂ : Subgroup ↥mirabolic) (hP₂ : ∀ p : ↥mirabolic, p ∈ P₂ ↔ leviRow p = e₂)
    (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) (hsec : Measurable sec)
    (hsecrow : ∀ r ∈ R, leviRow (sec r) = r) (hshell : ∀ p : ↥mirabolic, OnShell S p → leviRow p ∈ goodLeviRows S)
    (hgoodR : goodLeviRows S ⊆ R) (hgoodm : MeasurableSet (goodLeviRows S))
    (hK : ∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ]
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    (Q : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ) (hQ : Measurable (Function.uncurry Q)) :
    ∫ x in R, ((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
        ∫ y, Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℂ))
          (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ)) * Q x y ∂ρ ∂leviHaar =
      ∫ x in goodLeviRows S, ((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
        ∫ y in {y | UnitOutside S y}, Q x y ∂ρ ∂leviHaar := by
  have hιt : ∀ y : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((ι (y, 0, 0, 0) : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) = torusElement y :=
    fun y => Units.ext (by rw [hιmat]; rfl)
  have hmod : Measurable fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      (((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal : ℂ) :=
    Complex.continuous_ofReal.measurable.comp
      (measurable_modulus.comp (measurable_subtype_coe.comp hsec)).inv.ennreal_toReal
  have hg : Measurable fun z : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      torusElement z.2 * (sec z.1 : AdelicGL 3 (𝓞 ℚ) ℚ) :=
    (measurable_torusElement.comp measurable_snd).mul (measurable_subtype_coe.comp (hsec.comp measurable_fst))
  have hL : Measurable fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      (((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal : ℂ) *
        ∫ y, Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℂ))
          (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ)) * Q x y ∂ρ := by
    refine hmod.mul (StronglyMeasurable.measurable (StronglyMeasurable.integral_prod_right ?_))
    exact (((measurable_const.indicator (measurableSet_shellCond S)).comp hg).mul hQ).stronglyMeasurable
  have hRm : Measurable fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      (((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal : ℂ) *
        ∫ y in {y | UnitOutside S y}, Q x y ∂ρ :=
    hmod.mul (StronglyMeasurable.measurable (StronglyMeasurable.integral_prod_right hQ.stronglyMeasurable))
  have key : ∫ x in R, (goodLeviRows S).indicator (fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
        (((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal : ℂ) *
          ∫ y in {y | UnitOutside S y}, Q x y ∂ρ) x ∂leviHaar =
      ∫ x in goodLeviRows S, ((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
        ∫ y in {y | UnitOutside S y}, Q x y ∂ρ ∂leviHaar := by
    rw [setIntegral_indicator hgoodm, Set.inter_eq_right.mpr hgoodR]
  rw [← key]
  have hset := hL.stronglyMeasurable.measurableSet_eq_fun (hRm.indicator hgoodm).stronglyMeasurable
  refine integral_congr_ae ((ae_restrict_iff hset).mpr (Filter.Eventually.of_forall fun x hxR => ?_))
  by_cases hgood : x ∈ goodLeviRows S
  · rw [Set.indicator_of_mem hgood, ← integral_indicator (measurableSet_setOf_unitOutside S)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : UnitOutside S y
    · have hsc : torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} :=
        shellCond_torusElement_mul hK hgood hy
      have hy' : y ∈ {y | UnitOutside S y} := hy
      simp only [Set.indicator_of_mem hsc, Set.indicator_of_mem hy', one_mul]
    · have hsc : torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ) ∉ {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} :=
        fun hsc => hy (unitOutside_of_shellCond_torusElement_mul hK hgood hsc)
      have hy' : y ∉ {y | UnitOutside S y} := hy
      simp only [Set.indicator_of_notMem hsc, Set.indicator_of_notMem hy', zero_mul]
  · rw [Set.indicator_of_notMem hgood]
    have h0 : ∀ y : (AdeleRing (𝓞 ℚ) ℚ)ˣ, Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℂ))
        (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ)) * Q x y = 0 := by
      intro y
      rw [Set.indicator_of_notMem ?_, zero_mul]
      intro hsc
      apply hgood
      have hsc' : OnShell S ((ι (y, 0, 0, 0) : ↥mirabolic) * sec x) := by
        intro q hq
        rw [Subgroup.coe_mul, hιt]
        exact hsc q hq
      have hr := hshell _ hsc'
      rwa [leviRow_mul_of_leviRow_eq ((hP₂ _).mp (ι (y, 0, 0, 0)).2) (sec x), hsecrow x hxR] at hr
    simp only [h0, integral_zero, mul_zero]

private theorem crossProfile_tests
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (μP : Measure ↥mirabolic) (c₀ : ℝ≥0∞)
    (ν : Measure (MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic))
    (hν : ν = c₀ • Measure.map Quotient.mk''
      (μP.withDensity fun p : ↥mirabolic =>
        HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
            (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
          Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ)))
    (P₂ : Subgroup ↥mirabolic) (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ))
    (μ₂ : Measure ↥P₂) [SFinite μ₂] (c : ℝ≥0∞)
    (hfib : μP = c • fibMeasure P₂ sec
      (fun p : ↥mirabolic => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ)) μ₂ leviHaar R)
    (hsec : Measurable sec) (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ]
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιm : Measurable ι)
    (hμ₂ι : μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))))
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    (hc₀ : c₀ ≠ 0) (hc₀top : c₀ ≠ ⊤) (hc0 : c ≠ 0) (hctop : c ≠ ⊤) (hP₂ : ∀ p : ↥mirabolic, p ∈ P₂ ↔ leviRow p = e₂)
    (hsecrow : ∀ r ∈ R, leviRow (sec r) = r) (hshell : ∀ p : ↥mirabolic, OnShell S p → leviRow p ∈ goodLeviRows S)
    (hgoodR : goodLeviRows S ⊆ R) (hgoodm : MeasurableSet (goodLeviRows S))
    (hK : ∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) {a b : ℝ}
    {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hΦ₀ : IsSlabDomain a b Φ₀)
    {f f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hfc : Continuous f) (hf'c : Continuous f')
    (hKf : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hKf' : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f')
    (hfcusp : f ∈ cuspFunctions ω a b Φ₀) (hf'cusp : f' ∈ cuspFunctions ω a b Φ₀)
    (hff : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (_ : translateRight g f ∈ automorphicSubmodule ω a b Φ₀),
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
        ∫⁻ q, ((‖𝓦 (translateRight g f) ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤)
    (hf'f' : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (_ : translateRight g f' ∈ automorphicSubmodule ω a b Φ₀),
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
        ∫⁻ q, ((‖𝓦 (translateRight g f') ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤)
    (hvan : ∀ g g' : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
        ∫ q, (starRingEnd ℂ) (𝓦 (translateRight g f) ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)) *
          𝓦 (translateRight g' f') ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν = 0)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (hh : h ∈ mirabolic)
    (hhK : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S → componentAt3 (𝓞 ℚ) ℚ q h ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q) :
    Measurable (fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      ((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
        crossProfile S f f' sec ρ h x) ∧
    Integrable (fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      ((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
        crossProfile S f f' sec ρ h x) (leviHaar.restrict (goodLeviRows S)) ∧
    ∀ g : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ, Measurable g → (∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) →
      (∀ x u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ, (∀ i, IntegralOutside S (u i)) → g (x + u) = g x) →
      ∫ x in goodLeviRows S, g x *
        (((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
          crossProfile S f f' sec ρ h x) ∂leviHaar = 0 := by
  have _ := hKf'

  have hfautm : f ∈ automorphicSubmodule ω a b Φ₀ := ((mem_cuspFunctions_iff ω a b Φ₀ f).mp hfcusp).1
  have hf'autm : f' ∈ automorphicSubmodule ω a b Φ₀ := ((mem_cuspFunctions_iff ω a b Φ₀ f').mp hf'cusp).1
  have hfaut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g :=
    ((mem_automorphicSubmodule_iff ω a b Φ₀ f).1 hfautm).1
  have hf'aut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f' (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f' g :=
    ((mem_automorphicSubmodule_iff ω a b Φ₀ f').1 hf'autm).1
  obtain ⟨hWfe, -⟩ := whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul f hfaut
  obtain ⟨hWf'e, -⟩ := whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul f' hf'aut
  have hWc : Continuous (𝓦 f) :=
    continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hfc
  have hW'c : Continuous (𝓦 f') :=
    continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hf'c
  have hιt : ∀ y : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((ι (y, 0, 0, 0) : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) = torusElement y :=
    fun y => Units.ext (by rw [hιmat]; rfl)
  set m₀ : ↥mirabolic := ⟨h, hh⟩ with hm₀

  obtain ⟨hmem, -, -⟩ :=
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ f hfcusp
  have hkept : ∀ m : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S → componentAt3 (𝓞 ℚ) ℚ q m ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q) →
      ∀ p : AdelicGL 3 (𝓞 ℚ) ℚ, 𝓦 (translateRight (keptOutside S m) f) p = 𝓦 f (p * m) := by
    intro m hm p
    rw [← translateRight_eq_translateRight_keptOutside S hm hfc hKf, whittaker3_translateRight]
  have hkept_triv : ∀ m : AdelicGL 3 (𝓞 ℚ) ℚ, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (keptOutside S m) = 1 := fun m q hq => by
    rw [componentAt3_keptOutside, if_neg hq]
  have hkept_mem : ∀ m : AdelicGL 3 (𝓞 ℚ) ℚ, translateRight (keptOutside S m) f ∈ automorphicSubmodule ω a b Φ₀ :=
    fun m => ((mem_cuspFunctions_iff ω a b Φ₀ _).mp (hmem _)).1

  have hfin_f : ∫⁻ q, ((‖𝓦 f (((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤ := by
    have := hff (keptOutside S h) (hkept_mem h) (hkept_triv h)
    simpa only [hkept h hhK] using this
  have hfin_f' : ∫⁻ q, ((‖𝓦 f' ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤ := by
    have h1 : translateRight 1 f' = f' := translateRight_one_eq f'
    have := hf'f' 1 (by rw [h1]; exact hf'autm) (fun p _ => map_one _)
    simpa only [h1] using this
  have hsq_f : Measurable fun q : MulAction.orbitRel.Quotient
      ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic =>
      ((‖𝓦 f (((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊ : ℝ≥0∞) ^ 2) :=
    measurable_nnnorm_whittaker3_out_mul_sq hfc hWfe h
  have hsq_f' : Measurable fun q : MulAction.orbitRel.Quotient
      ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic =>
      ((‖𝓦 f' ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) := by
    simpa only [mul_one] using measurable_nnnorm_whittaker3_out_mul_sq hf'c hWf'e 1
  have hsum : ∫⁻ q, (((‖𝓦 f (((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊ : ℝ≥0∞) ^ 2) +
      ((‖𝓦 f' ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)) ∂ν < ⊤ := by
    rw [lintegral_add_left hsq_f]
    exact ENNReal.add_lt_top.2 ⟨hfin_f.lt_top, hfin_f'.lt_top⟩

  have hint : ∀ m : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : ↥mirabolic, ‖𝓦 f ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * m)‖₊ = ‖𝓦 f ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊) →
      Integrable (fun q : MulAction.orbitRel.Quotient ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic)
          ↥mirabolic =>
        (starRingEnd ℂ) (𝓦 f (((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * m)) *
          𝓦 f' ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)) ν := by
    intro m hm
    refine ⟨(measurable_conj_whittaker3_out_mul hfc hf'c hWfe hWf'e m).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (lintegral_mono fun q => ?_) hsum
    rw [enorm_eq_nnnorm, nnnorm_mul, nnnorm_conj_eq, hm, ENNReal.coe_mul]
    exact ennreal_mul_le_sq_add_sq _ _

  have hmod : Measurable fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      (((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal : ℂ) :=
    Complex.continuous_ofReal.measurable.comp
      (measurable_modulus.comp (measurable_subtype_coe.comp hsec)).inv.ennreal_toReal
  have hpair : ∀ m : AdelicGL 3 (𝓞 ℚ) ℚ, Measurable fun z : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      (starRingEnd ℂ) (𝓦 f (torusElement z.2 * (sec z.1 : AdelicGL 3 (𝓞 ℚ) ℚ) * m)) *
        𝓦 f' (torusElement z.2 * (sec z.1 : AdelicGL 3 (𝓞 ℚ) ℚ)) := by
    intro m
    have hg : Measurable fun z : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        torusElement z.2 * (sec z.1 : AdelicGL 3 (𝓞 ℚ) ℚ) :=
      (measurable_torusElement.comp measurable_snd).mul (measurable_subtype_coe.comp (hsec.comp measurable_fst))
    exact (Complex.continuous_conj.measurable.comp (hWc.measurable.comp (hg.mul_const m))).mul
      (hW'c.measurable.comp hg)
  have hcross : Measurable fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ => crossProfile S f f' sec ρ h x := by
    simp only [crossProfile]
    exact StronglyMeasurable.measurable (StronglyMeasurable.integral_prod_right (hpair h).stronglyMeasurable)
  have hFm : Measurable fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      ((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
        crossProfile S f f' sec ρ h x :=
    hmod.mul hcross

  have hFi : Integrable (fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      ((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
        crossProfile S f f' sec ρ h x) (leviHaar.restrict (goodLeviRows S)) := by
    have hGm : Measurable fun q : MulAction.orbitRel.Quotient
        ↥(WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic =>
        ‖(starRingEnd ℂ) (𝓦 f (((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * h)) *
          𝓦 f' ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖ₑ :=
      (measurable_conj_whittaker3_out_mul hfc hf'c hWfe hWf'e h).enorm
    have hI := lintegral_quotient_eq S μP c₀ ν hν P₂ sec R μ₂ c hfib hsec ρ ι hιm hμ₂ι hιmat hGm
    simp only [conj_whittaker3_out_mul_whittaker3_out hWfe hWf'e, Subgroup.coe_mul, hιt] at hI
    have hfinite : ∫⁻ q, ‖(starRingEnd ℂ) (𝓦 f (((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * h)) *
        𝓦 f' ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖ₑ ∂ν < ⊤ :=
      lt_of_le_of_lt (lintegral_mono fun q => by
        rw [enorm_eq_nnnorm, nnnorm_mul, nnnorm_conj_eq, ENNReal.coe_mul]
        exact ennreal_mul_le_sq_add_sq _ _) hsum
    rw [hI] at hfinite
    have hJ : ∫⁻ x in R, (modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ *
        ∫⁻ y, Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞))
            (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ)) *
          ‖(starRingEnd ℂ) (𝓦 f (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ) * h)) *
            𝓦 f' (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ))‖ₑ ∂ρ ∂leviHaar < ⊤ := by
      by_contra htop
      rw [not_lt, top_le_iff] at htop
      rw [htop, ENNReal.mul_top hc0, ENNReal.mul_top hc₀] at hfinite
      exact lt_irrefl _ hfinite
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt (lintegral_mono_set hgoodR) hJ)
    refine lintegral_mono_ae ((ae_restrict_iff' hgoodm).2 (Filter.Eventually.of_forall fun x hx => ?_))
    have hshellU : ∀ y : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
        Set.indicator {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} (fun _ => (1 : ℝ≥0∞))
            (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ)) *
          ‖(starRingEnd ℂ) (𝓦 f (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ) * h)) *
            𝓦 f' (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ))‖ₑ =
        Set.indicator {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ | UnitOutside S y} (fun y =>
          ‖(starRingEnd ℂ) (𝓦 f (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ) * h)) *
            𝓦 f' (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ))‖ₑ) y := by
      intro y
      by_cases hy : UnitOutside S y
      · rw [Set.indicator_of_mem (shellCond_torusElement_mul hK hx hy : torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ) ∈
          {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g}), Set.indicator_of_mem (hy : y ∈ {y | UnitOutside S y}), one_mul]
      · rw [Set.indicator_of_notMem (fun hsc => hy (unitOutside_of_shellCond_torusElement_mul hK hx hsc)),
          Set.indicator_of_notMem (hy : y ∉ {y | UnitOutside S y}), zero_mul]
    simp only [hshellU, lintegral_indicator (measurableSet_setOf_unitOutside S)]
    rw [enorm_eq_nnnorm, nnnorm_mul, Complex.nnnorm_real, ENNReal.coe_mul, crossProfile]
    refine mul_le_mul' ?_ (enorm_integral_le_lintegral_enorm _)
    rw [← enorm_eq_nnnorm, Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le

  set D : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ := (goodLeviRows S).indicator fun x =>
    ((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
      crossProfile S f f' sec ρ h x with hD_def
  have hD : Integrable D leviHaar := (integrable_indicator_iff hgoodm).2 hFi
  have hsupp : ∀ z, D z ≠ 0 → ∀ i, IntegralOutsideAll S (z i) := by
    intro z hz i q hq
    have hzg : z ∈ goodLeviRows S := by
      by_contra hzg
      exact hz (Set.indicator_of_notMem hzg _)
    exact (hzg.1 q hq).1 i
  have hcoef₀ : ∀ t' : Fin 2 → AdeleRing (𝓞 ℚ) ℚ, (∀ i, ZeroOutside S (t' i)) →
      ∫ z, NumberField.StandardAddChar.psiQ (-(z ⬝ᵥ t')) * D z ∂leviHaar = 0 := by
    intro t' ht'
    set t : Fin 2 → AdeleRing (𝓞 ℚ) ℚ := leviBlock m₀⁻¹ *ᵥ t' with ht_def
    have ht : ∀ i, ZeroOutside S (t i) := zeroOutside_mulVec S _ ht'
    have hxt : ∀ x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ, (x ᵥ* leviBlock m₀) ⬝ᵥ t = x ⬝ᵥ t' := by
      intro x
      rw [← Matrix.dotProduct_mulVec, ht_def, Matrix.mulVec_mulVec, leviBlock_mul_leviBlock_inv, Matrix.one_mulVec]

    set u : AdelicGL 3 (𝓞 ℚ) ℚ := h * columnUnipotent t with hu_def
    have huK : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S → componentAt3 (𝓞 ℚ) ℚ q u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q := by
      intro q hq
      rw [hu_def, map_mul, componentAt3_columnUnipotent S ht hq, mul_one]
      exact hhK q hq
    have hphase : ∀ p : ↥mirabolic, 𝓦 f ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * u) =
        NumberField.StandardAddChar.psiQ (leviRow (p * m₀) ⬝ᵥ t) * 𝓦 f ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * h) := by
      intro p
      have e : (p : AdelicGL 3 (𝓞 ℚ) ℚ) * u = ((p * m₀ : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * columnUnipotent t := by
        rw [hu_def, Subgroup.coe_mul, hm₀, mul_assoc]
      rw [e, whittaker3_mul_columnUnipotent hWfe, Subgroup.coe_mul]
    have hnorm : ∀ p : ↥mirabolic, ‖𝓦 f ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * u)‖₊ = ‖𝓦 f ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊ := by
      intro p
      rw [hphase, nnnorm_mul, nnnorm_psiQ, one_mul]

    have hvan_u : ∫ q, (starRingEnd ℂ) (𝓦 f (((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) * u)) *
        𝓦 f' ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν = 0 := by
      have := hvan (keptOutside S u) 1 (hkept_triv u) (fun p _ => map_one _)
      simpa only [hkept u huK, translateRight_one_eq] using this
    have hA := integral_quotient_eq S μP c₀ ν hν P₂ sec R μ₂ c hfib hsec ρ ι hιm hμ₂ι hιmat
      (measurable_conj_whittaker3_out_mul hfc hf'c hWfe hWf'e u) (hint u hnorm)
    simp only [conj_whittaker3_out_mul_whittaker3_out hWfe hWf'e, Subgroup.coe_mul, hιt] at hA
    rw [hvan_u, integral_inv_modulus_mul_integral_indicator_shell_eq S P₂ hP₂ sec R hsec hsecrow hshell hgoodR hgoodm
      hK ρ ι hιmat (fun x y => (starRingEnd ℂ) (𝓦 f (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ) * u)) *
        𝓦 f' (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ))) (hpair u)] at hA

    have hgoodint : ∫ x in goodLeviRows S,
        ((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
          ∫ y in {y | UnitOutside S y}, (starRingEnd ℂ) (𝓦 f (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ) * u)) *
            𝓦 f' (torusElement y * (sec x : AdelicGL 3 (𝓞 ℚ) ℚ)) ∂ρ ∂leviHaar =
        ∫ x in goodLeviRows S, NumberField.StandardAddChar.psiQ (-(x ⬝ᵥ t')) *
          (((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
            crossProfile S f f' sec ρ h x) ∂leviHaar := by
      refine setIntegral_congr_fun hgoodm fun x hx => ?_
      have hrow : ∀ y : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
          leviRow ((ι (y, 0, 0, 0) : ↥mirabolic) * (sec x * m₀)) = x ᵥ* leviBlock m₀ := by
        intro y
        rw [leviRow_mul_of_leviRow_eq ((hP₂ _).mp (ι (y, 0, 0, 0)).2) (sec x * m₀), leviRow_mul_eq_vecMul,
          hsecrow x (hgoodR hx)]
      simp only [crossProfile, ← hιt, ← Subgroup.coe_mul, hphase, hrow, hxt, map_mul, conj_psiQ, mul_assoc,
        integral_const_mul]
      ring
    rw [hgoodint] at hA
    have hc₀r : c₀.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hc₀, hc₀top⟩
    have hcr : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hc0, hctop⟩
    have h0 := (mul_eq_zero.1 hA.symm).resolve_left (Complex.ofReal_ne_zero.2 hc₀r)
    have h0' := (mul_eq_zero.1 h0).resolve_left (Complex.ofReal_ne_zero.2 hcr)
    rw [hD_def]
    simp only [← Set.indicator_mul_right _ fun z => NumberField.StandardAddChar.psiQ (-(z ⬝ᵥ t'))]
    rw [integral_indicator hgoodm]
    exact h0'
  have hcoefAll : ∀ t' : Fin 2 → AdeleRing (𝓞 ℚ) ℚ, (∀ i, IntegralOutsideAll S (t' i)) →
      ∫ z, NumberField.StandardAddChar.psiQ (-(z ⬝ᵥ t')) * D z ∂leviHaar = 0 :=
    fun t' ht' => coefficient_eq_zero_of_forall_zeroOutside S 2 leviHaar (fun z => z) D hsupp hcoef₀ t' ht'
  have hcoef : ∀ᵐ t' ∂(Measure.pi fun _ : Fin 2 =>
      (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s}),
      ∫ z, NumberField.StandardAddChar.psiQ (-((fun z => z) z ⬝ᵥ t')) * D z ∂leviHaar = 0 := by
    rw [← Measure.restrict_pi_pi]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_integralOutsideAll S)] with t' ht'
    exact hcoefAll t' fun i => ht' i (Set.mem_univ i)
  have hmain := integral_mul_eq_zero_of_coefficients S 2 leviHaar (fun z => z) measurable_id D hD hsupp hcoef
  refine ⟨hFm, hFi, fun g hg hgb hginv => ?_⟩
  have := hmain g hg hgb hginv
  rw [hD_def] at this
  simp only [← Set.indicator_mul_right _ g] at this
  rwa [integral_indicator hgoodm] at this

section TailCut

open scoped Classical

private def cutRow (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) :
    Fin 2 → AdeleRing (𝓞 ℚ) ℚ :=
  fun i => tailAdele S * u i

private theorem cutRow_add (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (u v : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) :
    cutRow S (u + v) = cutRow S u + cutRow S v :=
  funext fun _ => mul_add _ _ _

private theorem continuous_cutRow (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Continuous (cutRow S) :=
  continuous_pi fun i => continuous_const.mul (continuous_apply i)

private theorem cutRow_eq_self (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ}
    (hu : ∀ i, IntegralOutside S (u i)) : cutRow S u = u := by
  funext i
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing ℚ) * (u i).1 = (u i).1
    rw [zero_mul]
    exact ((hu i).2.2).symm
  · apply FiniteAdeleRing.ext
    intro v
    show (tailAdele S).2 v * (u i).2 v = (u i).2 v
    have ht : (tailAdele S).2 v = if v ∈ S then 0 else 1 := evalHom_tailAdele S v
    rw [ht]
    split_ifs with hv
    · rw [zero_mul]
      exact ((hu i).2.1 v hv).symm
    · exact one_mul _

private def rowBox : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) :=
  Set.pi Set.univ fun _ => AdelicBox.adelicBox ℚ

private theorem measurableSet_rowBox : MeasurableSet rowBox :=
  MeasurableSet.univ_pi fun _ => AdelicBox.measurableSet_adelicBox ℚ

private theorem leviHaar_rowBox_ne_zero : leviHaar rowBox ≠ 0 := by
  rw [rowBox, Measure.pi_pi]
  exact Finset.prod_ne_zero_iff.2 fun _ _ => (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'

private theorem leviHaar_rowBox_ne_top : leviHaar rowBox ≠ ⊤ := by
  rw [rowBox, Measure.pi_pi]
  exact ENNReal.prod_ne_top fun _ _ => (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne

private theorem integralOutside_cutRow (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ}
    (hu : u ∈ rowBox) (i : Fin 2) : IntegralOutside S (cutRow S u i) := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, ?_⟩
  · show evalHom q (tailAdele S * u i) ∈ _
    rw [map_mul, evalHom_tailAdele, if_neg hq, one_mul]
    exact (Set.mem_univ_pi.1 hu i).2 q
  · show evalHom q (tailAdele S * u i) = 0
    rw [map_mul, evalHom_tailAdele, if_pos hq, zero_mul]
  · show AdelicLevel.adeleArch (𝓞 ℚ) ℚ (tailAdele S * u i) = 0
    rw [map_mul]
    exact mul_eq_zero_of_left rfl _

private theorem add_mem_rowBox {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {u u₀ : Fin 2 → AdeleRing (𝓞 ℚ) ℚ}
    (hu : u ∈ rowBox) (hu₀ : ∀ i, IntegralOutside S (u₀ i)) : u + u₀ ∈ rowBox :=
  Set.mem_univ_pi.2 fun i => by
  obtain ⟨h1, h2⟩ := Set.mem_univ_pi.1 hu i
  refine ⟨?_, fun v => ?_⟩
  · show (u i).1 + (u₀ i).1 ∈ _
    rw [show (u₀ i).1 = 0 from (hu₀ i).2.2, add_zero]
    exact h1
  · show (u i).2 v + (u₀ i).2 v ∈ _
    refine add_mem (h2 v) ?_
    by_cases hv : v ∈ S
    · rw [show (u₀ i).2 v = 0 from (hu₀ i).2.1 v hv]
      exact zero_mem _
    · exact (hu₀ i).1 v hv

private theorem add_mem_rowBox_iff {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {u₀ : Fin 2 → AdeleRing (𝓞 ℚ) ℚ}
    (hu₀ : ∀ i, IntegralOutside S (u₀ i)) (u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) : u + u₀ ∈ rowBox ↔ u ∈ rowBox :=
  ⟨fun h => by
    have h' := add_mem_rowBox (u₀ := -u₀) h fun i => integralOutside_neg S (hu₀ i)
    rwa [add_neg_cancel_right] at h', fun h => add_mem_rowBox h hu₀⟩

end TailCut
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem ae_restrict_eq_zero_of_forall_integral_mul_eq_zero (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hgood : MeasurableSet (goodLeviRows S)) (F : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (hFm : Measurable F)
    (hFi : Integrable F (leviHaar.restrict (goodLeviRows S)))
    (hcov : ∀ x u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ, (∀ i, IntegralOutside S (u i)) → x ∈ goodLeviRows S →
      x + u ∈ goodLeviRows S → ∃ t : ℝ, 0 < t ∧ F (x + u) = (t : ℂ) * F x)
    (htest : ∀ g : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ, Measurable g → (∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) →
      (∀ x u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ, (∀ i, IntegralOutside S (u i)) → g (x + u) = g x) →
      ∫ x in goodLeviRows S, g x * F x ∂leviHaar = 0) :
    F =ᵐ[leviHaar.restrict (goodLeviRows S)] 0 := by
  classical
  have hB : MeasurableSet rowBox := measurableSet_rowBox
  haveI : IsFiniteMeasure (leviHaar.restrict rowBox) := isFiniteMeasure_restrict.2 leviHaar_rowBox_ne_top
  have hGm : Measurable ((goodLeviRows S).indicator F) := hFm.indicator hgood
  have hGi : Integrable ((goodLeviRows S).indicator F) leviHaar := (integrable_indicator_iff hgood).2 hFi
  have hcm : Measurable (cutRow S) := (continuous_cutRow S).measurable

  have hHm : Measurable fun p : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) =>
      (goodLeviRows S).indicator F (p.1 + cutRow S p.2) :=
    hGm.comp (measurable_fst.add (hcm.comp measurable_snd))
  have hHi : Integrable (fun p : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) =>
      (goodLeviRows S).indicator F (p.1 + cutRow S p.2)) (leviHaar.prod (leviHaar.restrict rowBox)) := by
    refine (integrable_prod_iff' hHm.aestronglyMeasurable).2
      ⟨ae_of_all _ fun u => hGi.comp_add_right (cutRow S u), ?_⟩
    show Integrable (fun u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      ∫ x, ‖(goodLeviRows S).indicator F (x + cutRow S u)‖ ∂leviHaar) (leviHaar.restrict rowBox)
    have h2 : (fun u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ => ∫ x, ‖(goodLeviRows S).indicator F (x + cutRow S u)‖ ∂leviHaar) =
        fun _ => ∫ x, ‖(goodLeviRows S).indicator F x‖ ∂leviHaar :=
      funext fun u => integral_add_right_eq_self (fun x => ‖(goodLeviRows S).indicator F x‖) (cutRow S u)
    rw [h2]
    exact integrable_const _

  set A : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ :=
    fun x => ∫ u in rowBox, (goodLeviRows S).indicator F (x + cutRow S u) ∂leviHaar with hA
  have hAi : Integrable A leviHaar := hHi.integral_prod_left
  have hAmeas : Measurable A :=
    (hHm.stronglyMeasurable.integral_prod_right' (ν := leviHaar.restrict rowBox)).measurable
  have hHae : ∀ᵐ x ∂leviHaar,
      Integrable (fun u => (goodLeviRows S).indicator F (x + cutRow S u)) (leviHaar.restrict rowBox) :=
    hHi.prod_right_ae
  have hAinv : ∀ x u₀ : Fin 2 → AdeleRing (𝓞 ℚ) ℚ, (∀ i, IntegralOutside S (u₀ i)) → A (x + u₀) = A x := by
    intro x u₀ hu₀
    show ∫ u in rowBox, (goodLeviRows S).indicator F (x + u₀ + cutRow S u) ∂leviHaar =
      ∫ u in rowBox, (goodLeviRows S).indicator F (x + cutRow S u) ∂leviHaar
    have h1 : (fun u => (goodLeviRows S).indicator F (x + u₀ + cutRow S u)) =
        fun u => (goodLeviRows S).indicator F (x + cutRow S (u + u₀)) := by
      funext u
      rw [cutRow_add, cutRow_eq_self S hu₀, add_assoc, add_comm u₀]
    rw [h1, ← integral_indicator hB, ← integral_indicator hB]
    have h2 : (fun u => rowBox.indicator (fun u => (goodLeviRows S).indicator F (x + cutRow S (u + u₀))) u) =
        fun u => rowBox.indicator (fun u => (goodLeviRows S).indicator F (x + cutRow S u)) (u + u₀) := by
      funext u
      by_cases hu : u ∈ rowBox
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem ((add_mem_rowBox_iff hu₀ u).2 hu)]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (fun h => hu ((add_mem_rowBox_iff hu₀ u).1 h))]
    rw [h2]
    exact integral_add_right_eq_self _ u₀

  have hint : ∀ g : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ, Measurable g → (∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) →
      (∀ x u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ, (∀ i, IntegralOutside S (u i)) → g (x + u) = g x) →
        ∫ x, g x * A x ∂leviHaar = 0 := by
    rintro g hg ⟨C, hC⟩ hginv
    have hgGi : Integrable (Function.uncurry fun x u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
        g x * (goodLeviRows S).indicator F (x + cutRow S u)) (leviHaar.prod (leviHaar.restrict rowBox)) :=
      hHi.bdd_mul (hg.comp measurable_fst).aestronglyMeasurable (ae_of_all _ fun p => hC p.1)
    have h0 : ∫ x, g x * (goodLeviRows S).indicator F x ∂leviHaar = 0 := by
      rw [show (fun x => g x * (goodLeviRows S).indicator F x) =
          fun x => (goodLeviRows S).indicator (fun x => g x * F x) x from
        funext fun x => (Set.indicator_mul_right _ g F).symm, integral_indicator hgood]
      exact htest g hg ⟨C, hC⟩ hginv
    calc ∫ x, g x * A x ∂leviHaar
        = ∫ x, ∫ u in rowBox, g x * (goodLeviRows S).indicator F (x + cutRow S u) ∂leviHaar ∂leviHaar :=
          integral_congr_ae (ae_of_all _ fun x => (integral_const_mul (g x) _).symm)
      _ = ∫ u in rowBox, ∫ x, g x * (goodLeviRows S).indicator F (x + cutRow S u) ∂leviHaar ∂leviHaar :=
          integral_integral_swap hgGi
      _ = ∫ u in rowBox, ∫ x, g x * (goodLeviRows S).indicator F x ∂leviHaar ∂leviHaar := by
          refine setIntegral_congr_fun hB fun u hu => ?_
          have hcu : ∀ i, IntegralOutside S (cutRow S u i) := integralOutside_cutRow S hu
          calc ∫ x, g x * (goodLeviRows S).indicator F (x + cutRow S u) ∂leviHaar
              = ∫ x, (fun y => g (y - cutRow S u) * (goodLeviRows S).indicator F y) (x + cutRow S u) ∂leviHaar :=
                integral_congr_ae (ae_of_all _ fun x => by simp only [add_sub_cancel_right])
            _ = ∫ y, g (y - cutRow S u) * (goodLeviRows S).indicator F y ∂leviHaar :=
                integral_add_right_eq_self (fun y => g (y - cutRow S u) * (goodLeviRows S).indicator F y) (cutRow S u)
            _ = ∫ y, g y * (goodLeviRows S).indicator F y ∂leviHaar :=
                integral_congr_ae (ae_of_all _ fun y => by
                  show g (y - cutRow S u) * (goodLeviRows S).indicator F y = g y * (goodLeviRows S).indicator F y
                  rw [← hginv (y - cutRow S u) (cutRow S u) hcu, sub_add_cancel])
      _ = 0 := by rw [setIntegral_const, h0, smul_zero]

  have hA0 : A =ᵐ[leviHaar] 0 := by
    have hbm : Measurable fun x => (starRingEnd ℂ) (A x) * (((‖A x‖)⁻¹ : ℝ) : ℂ) :=
      (Complex.continuous_conj.measurable.comp hAmeas).mul (Complex.measurable_ofReal.comp hAmeas.norm.inv)
    have hbb : ∀ x, ‖(starRingEnd ℂ) (A x) * (((‖A x‖)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := fun x => by
      rw [norm_mul, RCLike.norm_conj, Complex.norm_real, norm_inv, norm_norm]
      exact mul_inv_le_one
    have hid : ∀ x, (starRingEnd ℂ) (A x) * (((‖A x‖)⁻¹ : ℝ) : ℂ) * A x = ((‖A x‖ : ℝ) : ℂ) := fun x => by
      rcases eq_or_ne (A x) 0 with h0 | h0
      · rw [h0, mul_zero, norm_zero, Complex.ofReal_zero]
      · rw [mul_comm, ← mul_assoc, Complex.mul_conj', Complex.ofReal_inv, sq, mul_assoc,
          mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 h0)), mul_one]
    have h := hint _ hbm ⟨1, hbb⟩ fun x u hu => by simp only [hAinv x u hu]
    simp only [hid] at h
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h
    have hn : (fun x => ‖A x‖) =ᵐ[leviHaar] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg (A x)) hAi.norm).1 h
    filter_upwards [hn] with x hx
    exact norm_eq_zero.1 hx

  set m : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞ :=
    fun x => leviHaar.restrict rowBox {u | x + cutRow S u ∈ goodLeviRows S} with hm
  have hmm : Measurable m :=
    measurable_measure_prodMk_left (ν := leviHaar.restrict rowBox)
      (hgood.preimage (measurable_fst.add (hcm.comp measurable_snd)))
  have hminv : ∀ x u₀ : Fin 2 → AdeleRing (𝓞 ℚ) ℚ, (∀ i, IntegralOutside S (u₀ i)) → m (x + u₀) = m x := by
    intro x u₀ hu₀
    show leviHaar.restrict rowBox {u | x + u₀ + cutRow S u ∈ goodLeviRows S} =
      leviHaar.restrict rowBox {u | x + cutRow S u ∈ goodLeviRows S}
    have hset : {u | x + u₀ + cutRow S u ∈ goodLeviRows S} =
        (fun u => u + u₀) ⁻¹' {u | x + cutRow S u ∈ goodLeviRows S} := by
      ext u
      show x + u₀ + cutRow S u ∈ goodLeviRows S ↔ x + cutRow S (u + u₀) ∈ goodLeviRows S
      rw [cutRow_add, cutRow_eq_self S hu₀, add_assoc, add_comm u₀]
    have hBpre : (fun u => u + u₀) ⁻¹' rowBox = rowBox := Set.ext fun u => add_mem_rowBox_iff hu₀ u
    rw [hset, Measure.restrict_apply' hB, Measure.restrict_apply' hB]
    conv_lhs => rw [← hBpre, ← Set.preimage_inter]
    exact measure_preimage_add_right _ _ _

  have hN : MeasurableSet {x | m x = 0} := hmm (measurableSet_singleton 0)
  have hNinv : ∀ x u₀ : Fin 2 → AdeleRing (𝓞 ℚ) ℚ, (∀ i, IntegralOutside S (u₀ i)) →
      (x + u₀ ∈ {x | m x = 0} ↔ x ∈ {x | m x = 0}) :=
    fun x u₀ hu₀ => by
      show m (x + u₀) = 0 ↔ m x = 0
      rw [hminv x u₀ hu₀]
  have hmx : ∀ x, m x = ∫⁻ u in rowBox, (goodLeviRows S).indicator 1 (x + cutRow S u) ∂leviHaar := fun x => by
    show leviHaar.restrict rowBox {u | x + cutRow S u ∈ goodLeviRows S} = _
    have hs : MeasurableSet {u | x + cutRow S u ∈ goodLeviRows S} := hgood.preimage (hcm.const_add x)
    rw [← lintegral_indicator_one hs]
    refine lintegral_congr fun u => ?_
    by_cases h : x + cutRow S u ∈ goodLeviRows S
    · simp only [Set.indicator_of_mem h, Set.indicator_of_mem (show u ∈ {u | x + cutRow S u ∈ goodLeviRows S} from h),
        Pi.one_apply]
    · simp only [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show u ∉ {u | x + cutRow S u ∈ goodLeviRows S} from h)]
  have hNull : leviHaar ({x | m x = 0} ∩ goodLeviRows S) = 0 := by
    have hIm : Measurable (Function.uncurry fun x u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
        {x | m x = 0}.indicator (1 : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞) x *
          (goodLeviRows S).indicator 1 (x + cutRow S u)) :=
      ((measurable_one.indicator hN).comp measurable_fst).mul
        ((measurable_one.indicator hgood).comp (measurable_fst.add (hcm.comp measurable_snd)))
    have h1 : ∫⁻ x, ∫⁻ u in rowBox, {x | m x = 0}.indicator (1 : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞) x *
        (goodLeviRows S).indicator 1 (x + cutRow S u) ∂leviHaar ∂leviHaar = 0 := by
      have h : ∀ x, ∫⁻ u in rowBox, {x | m x = 0}.indicator (1 : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞) x *
          (goodLeviRows S).indicator 1 (x + cutRow S u) ∂leviHaar = 0 := fun x => by
        have hmeas : Measurable fun u =>
            (goodLeviRows S).indicator (1 : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞) (x + cutRow S u) :=
          (measurable_one.indicator hgood).comp (hcm.const_add x)
        rw [lintegral_const_mul _ hmeas, ← hmx x]
        by_cases hx : m x = 0
        · rw [hx, mul_zero]
        · rw [Set.indicator_of_notMem (show x ∉ {x | m x = 0} from hx), zero_mul]
      rw [lintegral_congr h, lintegral_zero]
    have h2 : ∫⁻ x, ∫⁻ u in rowBox, {x | m x = 0}.indicator (1 : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞) x *
        (goodLeviRows S).indicator 1 (x + cutRow S u) ∂leviHaar ∂leviHaar =
        leviHaar ({x | m x = 0} ∩ goodLeviRows S) * leviHaar rowBox := by
      rw [lintegral_lintegral_swap (μ := leviHaar) (ν := leviHaar.restrict rowBox) hIm.aemeasurable]
      have hinner : ∀ u ∈ rowBox, ∫⁻ x, {x | m x = 0}.indicator (1 : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞) x *
          (goodLeviRows S).indicator 1 (x + cutRow S u) ∂leviHaar = leviHaar ({x | m x = 0} ∩ goodLeviRows S) := by
        intro u hu
        have hcu : ∀ i, IntegralOutside S (cutRow S u i) := integralOutside_cutRow S hu
        calc ∫⁻ x, {x | m x = 0}.indicator (1 : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞) x *
              (goodLeviRows S).indicator 1 (x + cutRow S u) ∂leviHaar
            = ∫⁻ x, (fun y => {x | m x = 0}.indicator (1 : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞) (y - cutRow S u) *
                (goodLeviRows S).indicator 1 y) (x + cutRow S u) ∂leviHaar :=
              lintegral_congr fun x => by simp only [add_sub_cancel_right]
          _ = ∫⁻ y, {x | m x = 0}.indicator (1 : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞) (y - cutRow S u) *
                (goodLeviRows S).indicator 1 y ∂leviHaar :=
              lintegral_add_right_eq_self (fun y => {x | m x = 0}.indicator (1 : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞)
                (y - cutRow S u) * (goodLeviRows S).indicator 1 y) (cutRow S u)
          _ = ∫⁻ y, ({x | m x = 0} ∩ goodLeviRows S).indicator 1 y ∂leviHaar := by
              refine lintegral_congr fun y => ?_
              have hmem : y - cutRow S u ∈ {x | m x = 0} ↔ y ∈ {x | m x = 0} := by
                have h := hNinv (y - cutRow S u) (cutRow S u) hcu
                rw [sub_add_cancel] at h
                exact h.symm
              rw [Set.inter_indicator_one, Pi.mul_apply]
              congr 1
              by_cases hy : y ∈ {x | m x = 0}
              · simp only [Set.indicator_of_mem hy, Set.indicator_of_mem (hmem.2 hy), Pi.one_apply]
              · simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hmem.1 h))]
          _ = leviHaar ({x | m x = 0} ∩ goodLeviRows S) := lintegral_indicator_one (hN.inter hgood)
      rw [setLIntegral_congr_fun hB hinner, setLIntegral_const]
    rw [h1] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_right leviHaar_rowBox_ne_zero

  have hslice : ∀ x, x ∈ goodLeviRows S → F x ≠ 0 → A x = 0 →
      Integrable (fun u => (goodLeviRows S).indicator F (x + cutRow S u)) (leviHaar.restrict rowBox) → m x = 0 := by
    intro x hx hFx hAx hIx
    have hval : ∀ u ∈ rowBox, x + cutRow S u ∈ goodLeviRows S → ∃ t : ℝ, 0 < t ∧
        (goodLeviRows S).indicator F (x + cutRow S u) = (t : ℂ) * F x := fun u hu hgu => by
      obtain ⟨t, ht, hteq⟩ := hcov x (cutRow S u) (integralOutside_cutRow S hu) hx hgu
      exact ⟨t, ht, by rw [Set.indicator_of_mem hgu, hteq]⟩
    have hre : ∀ u ∈ rowBox, (goodLeviRows S).indicator F (x + cutRow S u) =
        ((((goodLeviRows S).indicator F (x + cutRow S u) / F x).re : ℝ) : ℂ) * F x := fun u hu => by
      by_cases hgu : x + cutRow S u ∈ goodLeviRows S
      · obtain ⟨t, -, hteq⟩ := hval u hu hgu
        rw [hteq, mul_div_assoc, div_self hFx, mul_one, Complex.ofReal_re]
      · rw [Set.indicator_of_notMem hgu, zero_div, Complex.zero_re, Complex.ofReal_zero, zero_mul]
    have hnonneg : ∀ u ∈ rowBox, 0 ≤ ((goodLeviRows S).indicator F (x + cutRow S u) / F x).re := fun u hu => by
      by_cases hgu : x + cutRow S u ∈ goodLeviRows S
      · obtain ⟨t, ht, hteq⟩ := hval u hu hgu
        rw [hteq, mul_div_assoc, div_self hFx, mul_one, Complex.ofReal_re]
        exact ht.le
      · simp only [Set.indicator_of_notMem hgu, zero_div, Complex.zero_re, le_refl]
    have hpos : ∀ u ∈ rowBox, x + cutRow S u ∈ goodLeviRows S →
        0 < ((goodLeviRows S).indicator F (x + cutRow S u) / F x).re := fun u hu hgu => by
      obtain ⟨t, ht, hteq⟩ := hval u hu hgu
      rw [hteq, mul_div_assoc, div_self hFx, mul_one, Complex.ofReal_re]
      exact ht
    have hσi : Integrable (fun u => ((goodLeviRows S).indicator F (x + cutRow S u) / F x).re)
        (leviHaar.restrict rowBox) :=
      (hIx.div_const (F x)).re
    have hAeq : A x = ((∫ u in rowBox, ((goodLeviRows S).indicator F (x + cutRow S u) / F x).re ∂leviHaar : ℝ) : ℂ) *
        F x := by
      show ∫ u in rowBox, (goodLeviRows S).indicator F (x + cutRow S u) ∂leviHaar = _
      rw [← integral_complex_ofReal, ← integral_mul_const]
      exact setIntegral_congr_fun hB hre
    have hσ0 : ∫ u in rowBox, ((goodLeviRows S).indicator F (x + cutRow S u) / F x).re ∂leviHaar = 0 := by
      have h := hAx
      rw [hAeq] at h
      exact Complex.ofReal_eq_zero.1 ((mul_eq_zero.1 h).resolve_right hFx)
    have hae : (fun u => ((goodLeviRows S).indicator F (x + cutRow S u) / F x).re) =ᵐ[leviHaar.restrict rowBox] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae ((ae_restrict_iff' hB).2 (ae_of_all _ hnonneg)) hσi).1 hσ0
    show leviHaar.restrict rowBox {u | x + cutRow S u ∈ goodLeviRows S} = 0
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hae, ae_restrict_mem hB] with u hu huB hgu
    exact (hpos u huB hgu).ne' hu

  rw [Filter.EventuallyEq, ae_restrict_iff' hgood]
  filter_upwards [hA0, hHae, measure_eq_zero_iff_ae_notMem.1 hNull] with x hAx hIx hxN hx
  by_contra hFx
  exact hxN ⟨hslice x hx hFx hAx hIx, hx⟩
section CovarianceLayer

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

local notation "GL₃" => AdelicGL 3 (𝓞 ℚ) ℚ

local notation "M₃" => Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)

private theorem conj_psiQ_mul_mul_psiQ_mul (s : 𝔸) (z z' : ℂ) :
    (starRingEnd ℂ) (NumberField.StandardAddChar.psiQ s * z) * (NumberField.StandardAddChar.psiQ s * z') =
      (starRingEnd ℂ) z * z' := by
  rw [map_mul, mul_mul_mul_comm, Complex.conj_mul', norm_psiQ, Complex.ofReal_one, one_pow, one_mul]

private theorem integralOutside_tailAdele (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : IntegralOutside S (tailAdele S) :=
  ⟨fun q hq => by
    rw [evalHom_tailAdele, if_neg hq]
    exact one_mem _, fun q hq => by rw [evalHom_tailAdele, if_pos hq], rfl⟩

open scoped Classical in

private theorem evalHom_one_sub_tailAdele (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (q : HeightOneSpectrum (𝓞 ℚ)) :
    evalHom q (1 - tailAdele S) = if q ∈ S then 1 else 0 := by
  rw [map_sub, map_one, evalHom_tailAdele]
  split_ifs
  · exact sub_zero _
  · exact sub_self _

private theorem adeleArch_one_sub_tailAdele (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ (1 - tailAdele S) = 1 := by
  rw [map_sub, map_one, show AdelicLevel.adeleArch (𝓞 ℚ) ℚ (tailAdele S) = 0 from rfl, sub_zero]

private theorem one_sub_tailAdele_mul_self (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    (1 - tailAdele S) * (1 - tailAdele S) = 1 - tailAdele S := by
  have h : tailAdele S * tailAdele S = tailAdele S :=
    congrFun (cutRow_eq_self S (u := fun _ => tailAdele S) fun _ => integralOutside_tailAdele S) 0
  rw [mul_sub, mul_one, sub_mul, one_mul, h, sub_self, sub_zero]

private theorem mul_one_sub_tailAdele {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {u : Fin 2 → 𝔸}
    (hu : ∀ i, IntegralOutside S (u i)) (i : Fin 2) : u i * (1 - tailAdele S) = 0 := by
  have h : tailAdele S * u i = u i := congrFun (cutRow_eq_self S hu) i
  rw [mul_sub, mul_one, mul_comm, h, sub_self]

private theorem mirabolic_apply_two (Q : ↥mirabolic) (j : Fin 3) :
    ((Q : GL₃) : M₃) 2 j = if j = 2 then 1 else 0 := by
  have hb : bottomRow (Q : GL₃) = e₃ := Q.2
  exact congrFun hb j

private theorem middle_row_mul_inv {P P' : ↥mirabolic} {x u : Fin 2 → 𝔸} (hP : leviRow P = x)
    (hP' : leviRow P' = x + u) {ε : 𝔸} (hu : ∀ i, u i * ε = 0) :
    (((P' * P⁻¹ : ↥mirabolic) : GL₃) : M₃) 1 0 * ε = 0 ∧
      ((((P' * P⁻¹ : ↥mirabolic) : GL₃) : M₃) 1 1 - 1) * ε = 0 := by
  set N : M₃ := (((P⁻¹ : ↥mirabolic) : GL₃) : M₃)
  have hPN : ((P : GL₃) : M₃) * N = 1 := by
    have h := congrArg (fun Q : ↥mirabolic => ((Q : GL₃) : M₃)) (mul_inv_cancel P)
    simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] using h
  have h10 := congrFun (congrFun hPN 1) 0
  have h11 := congrFun (congrFun hPN 1) 1
  rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_ne (by decide : (1 : Fin 3) ≠ 0)] at h10
  rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_eq] at h11
  have hx0 : ((P : GL₃) : M₃) 1 0 = x 0 := congrFun hP 0
  have hx1 : ((P : GL₃) : M₃) 1 1 = x 1 := congrFun hP 1
  have hx0' : ((P' : GL₃) : M₃) 1 0 = x 0 + u 0 := congrFun hP' 0
  have hx1' : ((P' : GL₃) : M₃) 1 1 = x 1 + u 1 := congrFun hP' 1
  have hN20 : N 2 0 = 0 := mirabolic_apply_two P⁻¹ 0
  have hN21 : N 2 1 = 0 := mirabolic_apply_two P⁻¹ 1
  have hM : (((P' * P⁻¹ : ↥mirabolic) : GL₃) : M₃) = ((P' : GL₃) : M₃) * N := by
    rw [Subgroup.coe_mul, Units.val_mul]
  rw [hM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three]
  exact ⟨by linear_combination ε * h10 + (N 0 0 * ε) * hx0' + (N 1 0 * ε) * hx1' - (N 0 0 * ε) * hx0
      - (N 1 0 * ε) * hx1 + N 0 0 * hu 0 + N 1 0 * hu 1 + ((((P' : GL₃) : M₃) 1 2 -
        ((P : GL₃) : M₃) 1 2) * ε) * hN20,
    by linear_combination ε * h11 + (N 0 1 * ε) * hx0' + (N 1 1 * ε) * hx1' - (N 0 1 * ε) * hx0
      - (N 1 1 * ε) * hx1 + N 0 1 * hu 0 + N 1 1 * hu 1 + ((((P' : GL₃) : M₃) 1 2 -
        ((P : GL₃) : M₃) 1 2) * ε) * hN21⟩

private theorem torusElement_mul_upperUnipotent3 (y : 𝔸ˣ) (b e c : 𝔸) :
    torusElement y * upperUnipotent3 b e c = upperUnipotent3 ((y : 𝔸) * b) e ((y : 𝔸) * c) * torusElement y := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_torusElement,
    show ((upperUnipotent3 b e c : GL₃) : M₃) = kernelMatrix 1 b c e from rfl,
    show ((upperUnipotent3 ((y : 𝔸) * b) e ((y : 𝔸) * c) : GL₃) : M₃) =
      kernelMatrix 1 ((y : 𝔸) * b) ((y : 𝔸) * c) e from rfl,
    kernelMatrix_mul, kernelMatrix_mul]
  simp only [mul_one, one_mul, zero_add, add_zero, zero_mul, mul_zero]

private theorem coe_upperUnipotent3_mul_torusElement (a : 𝔸ˣ) (b e c : 𝔸) :
    ((upperUnipotent3 b e c * torusElement a : GL₃) : M₃) = kernelMatrix (a : 𝔸) b c e := by
  rw [Units.val_mul, coe_torusElement, show ((upperUnipotent3 b e c : GL₃) : M₃) = kernelMatrix 1 b c e from rfl,
    kernelMatrix_mul]
  simp only [one_mul, mul_zero, add_zero, zero_add]

private theorem map_kernelMatrix_cut_eq {B : Type} [CommRing B] (φ : 𝔸 →+* B) {ε : 𝔸} (hε : φ ε = 1)
    (M : ↥mirabolic) (h10 : ((M : GL₃) : M₃) 1 0 * ε = 0)
    (h11 : (((M : GL₃) : M₃) 1 1 - 1) * ε = 0) :
    (kernelMatrix (1 + (((M : GL₃) : M₃) 0 0 - 1) * ε) (((M : GL₃) : M₃) 0 1 * ε)
        (((M : GL₃) : M₃) 0 2 * ε) (((M : GL₃) : M₃) 1 2 * ε)).map φ =
      ((M : GL₃) : M₃).map φ := by
  have hφ10 : φ (((M : GL₃) : M₃) 1 0) = 0 := by
    have h := congrArg φ h10
    rwa [map_mul, hε, mul_one, map_zero] at h
  have hφ11 : φ (((M : GL₃) : M₃) 1 1) = 1 := by
    have h := congrArg φ h11
    rwa [map_mul, hε, mul_one, map_sub, map_one, map_zero, sub_eq_zero] at h
  rw [kernelMatrix_map, eq_kernelMatrix_of_rows (((M : GL₃) : M₃).map φ) (by rw [Matrix.map_apply, hφ10])
    (by rw [Matrix.map_apply, hφ11])
    (by rw [Matrix.map_apply, mirabolic_apply_two, if_neg (by decide : (0 : Fin 3) ≠ 2), map_zero])
    (by rw [Matrix.map_apply, mirabolic_apply_two, if_neg (by decide : (1 : Fin 3) ≠ 2), map_zero])
    (by rw [Matrix.map_apply, mirabolic_apply_two, if_pos rfl, map_one])]
  simp only [Matrix.map_apply, map_add, map_mul, map_sub, map_one, hε, mul_one, add_sub_cancel]

private theorem exists_decomposition_of_goodLeviRows (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {sec : (Fin 2 → 𝔸) → ↥mirabolic} {R : Set (Fin 2 → 𝔸)} (hsecrow : ∀ r ∈ R, leviRow (sec r) = r)
    (hgoodR : goodLeviRows S ⊆ R)
    (hK : ∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (sec r : GL₃) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    {x u : Fin 2 → 𝔸} (hu : ∀ i, IntegralOutside S (u i)) (hx : x ∈ goodLeviRows S)
    (hxu : x + u ∈ goodLeviRows S) :
    ∃ (a : 𝔸ˣ) (b e c : 𝔸) (κ : GL₃), UnitOutside S a ∧ archComponent3 (𝓞 ℚ) ℚ κ = 1 ∧
      (∀ q ∈ S, componentAt3 (𝓞 ℚ) ℚ q κ = 1) ∧
      (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S → componentAt3 (𝓞 ℚ) ℚ q κ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q) ∧
      (sec (x + u) : GL₃) = upperUnipotent3 b e c * torusElement a * (sec x : GL₃) * κ := by
  set ε : 𝔸 := 1 - tailAdele S with hεdef
  have hεu : ∀ i, u i * ε = 0 := mul_one_sub_tailAdele hu
  have hεu' : ∀ i, (-u) i * ε = 0 := fun i => by rw [Pi.neg_apply, neg_mul, hεu i, neg_zero]
  have hεε : ε * ε = ε := one_sub_tailAdele_mul_self S
  set P : ↥mirabolic := sec x
  set P' : ↥mirabolic := sec (x + u)
  have hP : leviRow P = x := hsecrow x (hgoodR hx)
  have hP' : leviRow P' = x + u := hsecrow (x + u) (hgoodR hxu)
  obtain ⟨hM10, hM11⟩ := middle_row_mul_inv hP hP' hεu
  obtain ⟨hM'10, -⟩ := middle_row_mul_inv hP' (show leviRow P = x + u + -u by rw [add_neg_cancel_right, hP]) hεu'
  set M : ↥mirabolic := P' * P⁻¹ with hMdef
  set M' : ↥mirabolic := P * P'⁻¹ with hM'def
  have hMM' : ((M : GL₃) : M₃) * ((M' : GL₃) : M₃) = 1 := by
    have h : M * M' = 1 := by
      rw [hMdef, hM'def]
      group
    have h' := congrArg (fun Q : ↥mirabolic => ((Q : GL₃) : M₃)) h
    simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] using h'
  have h00 := congrFun (congrFun hMM' 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_eq] at h00
  have hM'20 : ((M' : GL₃) : M₃) 2 0 = 0 := mirabolic_apply_two M' 0

  set a₀ : 𝔸 := 1 + (((M : GL₃) : M₃) 0 0 - 1) * ε with ha₀
  set a₀' : 𝔸 := 1 + (((M' : GL₃) : M₃) 0 0 - 1) * ε with ha₀'
  have haa : a₀ * a₀' = 1 := by
    rw [ha₀, ha₀']
    linear_combination (((M : GL₃) : M₃) 0 0 - 1) * ((((M' : GL₃) : M₃) 0 0 - 1)) * hεε + ε * h00
      - ((M : GL₃) : M₃) 0 1 * hM'10 - (ε * ((M : GL₃) : M₃) 0 2) * hM'20
  set a : 𝔸ˣ := Units.mkOfMulEqOne a₀ a₀' haa
  have hav : (a : 𝔸) = a₀ := Units.val_mkOfMulEqOne haa
  set b : 𝔸 := ((M : GL₃) : M₃) 0 1 * ε with hb
  set c : 𝔸 := ((M : GL₃) : M₃) 0 2 * ε with hc
  set e : 𝔸 := ((M : GL₃) : M₃) 1 2 * ε with he
  set n₀ : GL₃ := upperUnipotent3 b e c * torusElement a with hn₀def
  have hn₀ : (n₀ : M₃) = kernelMatrix a₀ b c e := by rw [hn₀def, coe_upperUnipotent3_mul_torusElement, hav]

  have hn₀out : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S → componentAt3 (𝓞 ℚ) ℚ q n₀ = 1 := by
    intro q hq
    have hε : evalHom q ε = 0 := by rw [hεdef, evalHom_one_sub_tailAdele, if_neg hq]
    apply Units.ext
    rw [val_componentAt3, hn₀, kernelMatrix_map, Units.val_one, ha₀, hb, hc, he]
    simp only [map_add, map_mul, map_sub, map_one, hε, mul_zero, add_zero]
    exact kernelMatrix_one_zero
  have hn₀in : ∀ q ∈ S, componentAt3 (𝓞 ℚ) ℚ q n₀ = componentAt3 (𝓞 ℚ) ℚ q (M : GL₃) := by
    intro q hq
    have hε : evalHom q ε = 1 := by rw [hεdef, evalHom_one_sub_tailAdele, if_pos hq]
    apply Units.ext
    rw [val_componentAt3, val_componentAt3, hn₀, ha₀, hb, hc, he]
    exact map_kernelMatrix_cut_eq (evalHom q) hε M hM10 hM11
  have hn₀arch : archComponent3 (𝓞 ℚ) ℚ n₀ = archComponent3 (𝓞 ℚ) ℚ (M : GL₃) := by
    have hε : AdelicLevel.adeleArch (𝓞 ℚ) ℚ ε = 1 := by rw [hεdef, adeleArch_one_sub_tailAdele]
    apply Units.ext
    rw [coe_archComponent3, coe_archComponent3, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hn₀, ha₀, hb, hc,
      he]
    exact map_kernelMatrix_cut_eq (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) hε M hM10 hM11
  have hMcoe : (M : GL₃) = (P' : GL₃) * (P : GL₃)⁻¹ := by rw [hMdef, Subgroup.coe_mul, Subgroup.coe_inv]

  refine ⟨a, b, e, c, (P : GL₃)⁻¹ * n₀⁻¹ * (P' : GL₃), fun q hq => ?_, ?_, fun q hq => ?_, fun q hq => ?_, ?_⟩
  · rw [hav, ha₀, map_add, map_mul, map_sub, map_one, show evalHom q ε = 0 by
      rw [hεdef, evalHom_one_sub_tailAdele, if_neg hq], mul_zero, add_zero, map_one]
  · rw [map_mul, map_mul, map_inv, map_inv, hn₀arch, hMcoe, map_mul, map_inv]
    group
  · rw [map_mul, map_mul, map_inv, map_inv, hn₀in q hq, hMcoe, map_mul, map_inv]
    group
  · rw [map_mul, map_mul, map_inv, map_inv, hn₀out q hq, inv_one, mul_one]
    exact mul_mem (inv_mem (hK x hx q hq)) (hK (x + u) hxu q hq)
  · rw [hn₀def]
    group

private theorem unitOutside_mul_iff {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {a : 𝔸ˣ} (ha : UnitOutside S a)
    (y : 𝔸ˣ) : UnitOutside S (y * a) ↔ UnitOutside S y := by
  refine forall₂_congr fun q hq => ?_
  rw [Units.val_mul, map_mul, map_mul, ha q hq, mul_one]

private theorem setIntegral_unitOutside_comp_mul {S : Finset (HeightOneSpectrum (𝓞 ℚ))} (ρ : Measure 𝔸ˣ)
    (w : 𝔸ˣ → ℝ≥0∞)
    (hdil : ∀ y, ∀ F : 𝔸ˣ → ℝ≥0∞, Measurable F → ∫⁻ x, F (x * y) ∂ρ = w y * ∫⁻ x, F x ∂ρ)
    {G : 𝔸ˣ → ℂ} (hG : Measurable G) {a : 𝔸ˣ} (ha : UnitOutside S a) :
    ∫ y in {y | UnitOutside S y}, G (y * a) ∂ρ = (w a).toReal * ∫ y in {y | UnitOutside S y}, G y ∂ρ := by
  haveI : MeasurableMul 𝔸ˣ := measurableMul_units
  have hUm : MeasurableSet {y : 𝔸ˣ | UnitOutside S y} := measurableSet_setOf_unitOutside S
  have hmap : Measure.map (fun y => y * a) ρ = w a • ρ := Measure.ext fun s hs => by
    rw [Measure.map_apply (measurable_mul_const a) hs, Measure.smul_apply, smul_eq_mul, ← lintegral_indicator_one hs,
      ← hdil a _ (measurable_one.indicator hs), ← lintegral_indicator_one (measurable_mul_const a hs)]
    rfl
  calc ∫ y in {y | UnitOutside S y}, G (y * a) ∂ρ
      = ∫ y, {y | UnitOutside S y}.indicator G (y * a) ∂ρ := by
        rw [← integral_indicator hUm]
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show {y | UnitOutside S y}.indicator (fun y => G (y * a)) y = {y | UnitOutside S y}.indicator G (y * a)
        by_cases hy : UnitOutside S y
        · rw [Set.indicator_of_mem (show y ∈ {y | UnitOutside S y} from hy),
            Set.indicator_of_mem (show y * a ∈ {y | UnitOutside S y} from (unitOutside_mul_iff ha y).2 hy)]
        · rw [Set.indicator_of_notMem (show y ∉ {y | UnitOutside S y} from hy),
            Set.indicator_of_notMem (show y * a ∉ {y | UnitOutside S y} from
              fun h => hy ((unitOutside_mul_iff ha y).1 h))]
    _ = ∫ z, {y | UnitOutside S y}.indicator G z ∂(Measure.map (fun y => y * a) ρ) :=
        (integral_map (measurable_mul_const a).aemeasurable (hG.indicator hUm).aestronglyMeasurable).symm
    _ = (w a).toReal * ∫ y in {y | UnitOutside S y}, G y ∂ρ := by
        rw [hmap, integral_smul_measure, integral_indicator hUm]
        exact Complex.real_smul

end CovarianceLayer
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem crossProfile_covariance (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ))
    (hsecrow : ∀ r ∈ R, leviRow (sec r) = r) (hgoodR : goodLeviRows S ⊆ R)
    (hK : ∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) (w : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ≥0∞) (hw : ∀ y, w y ≠ 0 ∧ w y ≠ ⊤)
    (hdil : ∀ y, ∀ F : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ≥0∞, Measurable F → ∫⁻ x, F (x * y) ∂ρ = w y * ∫⁻ x, F x ∂ρ)
    {f f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hfc : Continuous f) (hf'c : Continuous f')
    (hKf : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hKf' : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f')
    (hfN : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      𝓦 f (upperUnipotent3 x y z * g) = NumberField.StandardAddChar.psiQ (x + y) * 𝓦 f g)
    (hf'N : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      𝓦 f' (upperUnipotent3 x y z * g) = NumberField.StandardAddChar.psiQ (x + y) * 𝓦 f' g)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hhK : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S → componentAt3 (𝓞 ℚ) ℚ q h ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (x u : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) (hu : ∀ i, IntegralOutside S (u i)) (hx : x ∈ goodLeviRows S)
    (hxu : x + u ∈ goodLeviRows S) :
    ∃ t : ℝ, 0 < t ∧ ((modulus (sec (x + u) : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
        crossProfile S f f' sec ρ h (x + u) =
      (t : ℂ) * (((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal *
        crossProfile S f f' sec ρ h x) := by
  obtain ⟨a, b, e, c, κ, haS, hκarch, hκS, hκK, hdec⟩ :=
    exists_decomposition_of_goodLeviRows S hsecrow hgoodR hK hu hx hxu
  set p : AdelicGL 3 (𝓞 ℚ) ℚ := (sec x : AdelicGL 3 (𝓞 ℚ) ℚ)
  set κ' : AdelicGL 3 (𝓞 ℚ) ℚ := h⁻¹ * κ * h with hκ'
  have hκ'arch : archComponent3 (𝓞 ℚ) ℚ κ' = 1 := by
    rw [hκ', map_mul, map_mul, map_inv, hκarch, mul_one, inv_mul_cancel]
  have hκ'S : ∀ q ∈ S, componentAt3 (𝓞 ℚ) ℚ q κ' = 1 := fun q hq => by
    rw [hκ', map_mul, map_mul, map_inv, hκS q hq, mul_one, inv_mul_cancel]
  have hκ'K : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q κ' ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q := fun q hq => by
    rw [hκ', map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (inv_mem (hhK q hq)) (hκK q hq)) (hhK q hq)
  have hκh : κ * h = h * κ' := by
    rw [hκ']
    group

  have hpt : ∀ y : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      (starRingEnd ℂ) (𝓦 f (torusElement y * (sec (x + u) : AdelicGL 3 (𝓞 ℚ) ℚ) * h)) *
          𝓦 f' (torusElement y * (sec (x + u) : AdelicGL 3 (𝓞 ℚ) ℚ)) =
        (starRingEnd ℂ) (𝓦 f (torusElement (y * a) * p * h)) * 𝓦 f' (torusElement (y * a) * p) := by
    intro y
    have hyn := torusElement_mul_upperUnipotent3 y b e c
    have h1 : torusElement y * (sec (x + u) : AdelicGL 3 (𝓞 ℚ) ℚ) * h =
        upperUnipotent3 ((y : AdeleRing (𝓞 ℚ) ℚ) * b) e ((y : AdeleRing (𝓞 ℚ) ℚ) * c) *
          (torusElement (y * a) * p * h * κ') := by
      rw [hdec, torusElement_mul, show torusElement y * (upperUnipotent3 b e c * torusElement a * p * κ) * h =
        torusElement y * upperUnipotent3 b e c * (torusElement a * p * (κ * h)) by simp only [mul_assoc], hyn, hκh]
      simp only [mul_assoc]
    have h2 : torusElement y * (sec (x + u) : AdelicGL 3 (𝓞 ℚ) ℚ) =
        upperUnipotent3 ((y : AdeleRing (𝓞 ℚ) ℚ) * b) e ((y : AdeleRing (𝓞 ℚ) ℚ) * c) *
          (torusElement (y * a) * p * κ) := by
      rw [hdec, torusElement_mul, show torusElement y * (upperUnipotent3 b e c * torusElement a * p * κ) =
        torusElement y * upperUnipotent3 b e c * (torusElement a * p * κ) by simp only [mul_assoc], hyn]
      simp only [mul_assoc]
    rw [h1, h2, hfN, hf'N, whittaker3_mul_eq_of_components S hfc hKf hκ'arch hκ'S hκ'K,
      whittaker3_mul_eq_of_components S hf'c hKf' hκarch hκS hκK, conj_psiQ_mul_mul_psiQ_mul]
  have hGm : Measurable fun y : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      (starRingEnd ℂ) (𝓦 f (torusElement y * p * h)) * 𝓦 f' (torusElement y * p) :=
    (Complex.continuous_conj.measurable.comp
      ((continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hfc).measurable.comp
        ((measurable_torusElement.mul_const p).mul_const h))).mul
      ((continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hf'c).measurable.comp
        (measurable_torusElement.mul_const p))
  have hcp : crossProfile S f f' sec ρ h (x + u) = (w a).toReal * crossProfile S f f' sec ρ h x := by
    unfold crossProfile
    simp_rw [hpt]
    exact setIntegral_unitOutside_comp_mul ρ w hdil hGm haS

  have hmod : modulus (sec (x + u) : AdelicGL 3 (𝓞 ℚ) ℚ) =
      modulus (upperUnipotent3 b e c * torusElement a) * modulus p * modulus κ := by
    rw [hdec, modulus_mul, modulus_mul]
  refine ⟨((modulus (upperUnipotent3 b e c * torusElement a))⁻¹ * (modulus κ)⁻¹ * w a).toReal, ?_, ?_⟩
  · exact ENNReal.toReal_pos
      (mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.2 (modulus_ne_top _)) (ENNReal.inv_ne_zero.2 (modulus_ne_top _)))
        (hw a).1)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (modulus_ne_zero _))
        (ENNReal.inv_ne_top.2 (modulus_ne_zero _))) (hw a).2)
  · rw [hcp, hmod,
      ENNReal.mul_inv (Or.inl (mul_ne_zero (modulus_ne_zero _) (modulus_ne_zero _)))
        (Or.inl (ENNReal.mul_ne_top (modulus_ne_top _) (modulus_ne_top _))),
      ENNReal.mul_inv (Or.inl (modulus_ne_zero _)) (Or.inl (modulus_ne_top _))]
    simp only [ENNReal.toReal_mul]
    push_cast
    ring

section TransferLayer

section RightInvariantComparison

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

end RightInvariantComparison
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem upperUnipotent3_mul_kernelMatrix (a x y z : AdeleRing (𝓞 ℚ) ℚ) :
    ((upperUnipotent3 x z y : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) *
        kernelMatrix a 0 0 0 =
      kernelMatrix a x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kernelMatrix, Matrix.mul_apply, Fin.sum_univ_three]

private theorem kernelMatrix_mul_literal (a x y z a' x' y' z' : AdeleRing (𝓞 ℚ) ℚ) :
    kernelMatrix a x y z * !![a', x', y'; 0, 1, z'; 0, 0, 1] =
      kernelMatrix (a * a') (x + a * x') (y + (a * y' + x * z')) (z' + z) :=
  kernelMatrix_mul a x y z a' x' y' z'

private theorem coe_chartElement_eq {P₂ : Subgroup ↥mirabolic}
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    (v : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) :
    ((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) = upperUnipotent3 v.2.1 v.2.2.2 v.2.2.1 * torusElement v.1 := by
  apply Units.ext
  simp only [Units.val_mul, hιmat, coe_torusElement, upperUnipotent3_mul_kernelMatrix]
  rfl

private theorem torusElement_mul_chartElement {P₂ : Subgroup ↥mirabolic}
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (v : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) :
    torusElement x * ((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) =
      upperUnipotent3 ((x : AdeleRing (𝓞 ℚ) ℚ) * v.2.1) v.2.2.2 ((x : AdeleRing (𝓞 ℚ) ℚ) * v.2.2.1) *
        torusElement (x * v.1) := by
  apply Units.ext
  simp only [Units.val_mul, hιmat, coe_torusElement, upperUnipotent3_mul_kernelMatrix, kernelMatrix_mul_literal]
  simp

private theorem componentAt3_upperUnipotent3_mem {q : HeightOneSpectrum (𝓞 ℚ)} {x y z : AdeleRing (𝓞 ℚ) ℚ}
    (hx : evalHom q x ∈ q.adicCompletionIntegers ℚ) (hy : evalHom q y ∈ q.adicCompletionIntegers ℚ)
    (hz : evalHom q z ∈ q.adicCompletionIntegers ℚ) :
    componentAt3 (𝓞 ℚ) ℚ q (upperUnipotent3 x y z) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q := by
  have hinv : (((upperUnipotent3 x y z : AdelicGL 3 (𝓞 ℚ) ℚ)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
      Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl
  refine mem_localMaximalCompact3_of_forall (fun i j => ?_) (fun i j => ?_)
  · rw [val_componentAt3, upperUnipotent3_coe, Matrix.map_apply]
    fin_cases i <;> fin_cases j <;> simp <;> first | exact hx | exact hy | exact hz
  · rw [val_componentAt3_inv, hinv, Matrix.map_apply]
    fin_cases i <;> fin_cases j <;> simp <;> first | exact hx | exact hy | exact sub_mem (mul_mem hx hy) hz

private theorem componentAt3_chartElement_mem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {P₂ : Subgroup ↥mirabolic}
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    {v : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))}
    (hy : UnitOutside S v.1) (hs : IntegralOutsideAll S v.2.1) (ha₂ : IntegralOutsideAll S v.2.2.1)
    (ha₃ : IntegralOutsideAll S v.2.2.2) {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ∉ S) :
    componentAt3 (𝓞 ℚ) ℚ q ((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q := by
  rw [coe_chartElement_eq ι hιmat v, map_mul]
  exact mul_mem (componentAt3_upperUnipotent3_mem (hs q hq) (ha₃ q hq) (ha₂ q hq))
    (componentAt3_torusElement_mem (hy q hq))

private def transportElement {P₂ : Subgroup ↥mirabolic} (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic)
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (r' r : Fin 2 → AdeleRing (𝓞 ℚ) ℚ)
    (v : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) : ↥mirabolic :=
  (sec r')⁻¹ * (ι v : ↥mirabolic) * sec r

private theorem componentAt3_transportElement_mem (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {P₂ : Subgroup ↥mirabolic} {sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic}
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    (hK : ∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    {r' r : Fin 2 → AdeleRing (𝓞 ℚ) ℚ} (hr' : r' ∈ goodLeviRows S) (hr : r ∈ goodLeviRows S)
    {v : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))}
    (hy : UnitOutside S v.1) (hs : IntegralOutsideAll S v.2.1) (ha₂ : IntegralOutsideAll S v.2.2.1)
    (ha₃ : IntegralOutsideAll S v.2.2.2) (q : HeightOneSpectrum (𝓞 ℚ)) (hq : q ∉ S) :
    componentAt3 (𝓞 ℚ) ℚ q (transportElement sec ι r' r v : AdelicGL 3 (𝓞 ℚ) ℚ) ∈
      localMaximalCompact3 (𝓞 ℚ) ℚ q := by
  simp only [transportElement, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  exact mul_mem (mul_mem (inv_mem (hK r' hr' q hq)) (componentAt3_chartElement_mem S ι hιmat hy hs ha₂ ha₃ hq))
    (hK r hr q hq)

private theorem psiQ_ne_zero (t : AdeleRing (𝓞 ℚ) ℚ) : NumberField.StandardAddChar.psiQ t ≠ 0 := fun h => by
  simpa [h] using norm_psiQ t

private theorem crossProfile_transportElement (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {P₂ : Subgroup ↥mirabolic}
    (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    {f f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hfN : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      𝓦 f (upperUnipotent3 x y z * g) = NumberField.StandardAddChar.psiQ (x + y) * 𝓦 f g)
    (r r' : Fin 2 → AdeleRing (𝓞 ℚ) ℚ)
    (v : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) :
    crossProfile S f f' sec ρ (transportElement sec ι r' r v : AdelicGL 3 (𝓞 ℚ) ℚ) r' =
      NumberField.StandardAddChar.psiQ (-v.2.2.2) *
        ∫ x, NumberField.StandardAddChar.psiQ (-((x : AdeleRing (𝓞 ℚ) ℚ) * v.2.1)) *
          ((starRingEnd ℂ) (torusProfile f sec r (x * v.1)) * torusProfile f' sec r' x)
            ∂ρ.restrict {y | UnitOutside S y} := by
  unfold crossProfile
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext x
  have e : torusElement x * (sec r' : AdelicGL 3 (𝓞 ℚ) ℚ) * (transportElement sec ι r' r v : AdelicGL 3 (𝓞 ℚ) ℚ) =
      upperUnipotent3 ((x : AdeleRing (𝓞 ℚ) ℚ) * v.2.1) v.2.2.2 ((x : AdeleRing (𝓞 ℚ) ℚ) * v.2.2.1) *
        (torusElement (x * v.1) * (sec r : AdelicGL 3 (𝓞 ℚ) ℚ)) := by
    rw [← mul_assoc, ← torusElement_mul_chartElement ι hιmat x v]
    simp only [transportElement, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, hfN, map_mul, conj_psiQ, neg_add, AddChar.map_add_eq_mul]
  unfold torusProfile
  ring

private theorem restrict_setOf_integralOutsideAll_ne_zero (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s} ≠ 0 := by
  intro h0
  have hU : IsOpen (Prod.snd ⁻¹' AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ : Set (AdeleRing (𝓞 ℚ) ℚ)) :=
    (AdelicLevel.isOpen_integralFiniteAdeles (𝓞 ℚ) ℚ).preimage continuous_snd
  have hsub : (Prod.snd ⁻¹' AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ : Set (AdeleRing (𝓞 ℚ) ℚ)) ⊆
      {s | IntegralOutsideAll S s} :=
    fun s hs q _ => hs q
  have hpos : 0 < NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ
      (Prod.snd ⁻¹' AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ) :=
    hU.measure_pos _ ⟨0, AdelicLevel.zero_mem_integralFiniteAdeles⟩
  have h1 := congrArg (fun m : Measure (AdeleRing (𝓞 ℚ) ℚ) => m Set.univ) h0
  simp only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] at h1
  exact hpos.ne' (measure_mono_null hsub h1)

private theorem measurable_crossProfile_prod (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {f f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hfc : Continuous f) (hf'c : Continuous f')
    {sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic} (hsec : Measurable sec) (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    [SFinite ρ] :
    Measurable fun p : ↥mirabolic × (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) =>
      crossProfile S f f' sec ρ (p.1 : AdelicGL 3 (𝓞 ℚ) ℚ) p.2 := by
  have hW := (continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hfc).measurable
  have hW' := (continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hf'c).measurable
  have hbase : Measurable fun q : (↥mirabolic × (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) × (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      torusElement q.2 * (sec q.1.2 : AdelicGL 3 (𝓞 ℚ) ℚ) :=
    (measurable_torusElement.comp measurable_snd).mul
      (measurable_subtype_coe.comp (hsec.comp (measurable_snd.comp measurable_fst)))
  have hleft : Measurable fun q : (↥mirabolic × (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) × (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      torusElement q.2 * (sec q.1.2 : AdelicGL 3 (𝓞 ℚ) ℚ) * (q.1.1 : AdelicGL 3 (𝓞 ℚ) ℚ) :=
    hbase.mul (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst))
  have hF : Measurable fun q : (↥mirabolic × (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) × (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      (starRingEnd ℂ) (𝓦 f (torusElement q.2 * (sec q.1.2 : AdelicGL 3 (𝓞 ℚ) ℚ) * (q.1.1 : AdelicGL 3 (𝓞 ℚ) ℚ))) *
        𝓦 f' (torusElement q.2 * (sec q.1.2 : AdelicGL 3 (𝓞 ℚ) ℚ)) :=
    (Complex.continuous_conj.measurable.comp (hW.comp hleft)).mul (hW'.comp hbase)
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := ρ.restrict {y | UnitOutside S y})).measurable

private theorem measure_preimage_mul_left_eq_zero (μP : Measure ↥mirabolic) [μP.IsMulRightInvariant]
    [μP.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μP] (g : ↥mirabolic) {B : Set ↥mirabolic}
    (hB : MeasurableSet B) (h0 : μP B = 0) : μP ((fun p : ↥mirabolic => g * p) ⁻¹' B) = 0 := by
  haveI : IsFiniteMeasureOnCompacts (Measure.map (fun p : ↥mirabolic => g * p) μP) := by
    have h := Measure.IsFiniteMeasureOnCompacts.map μP (Homeomorph.mulLeft g)
    rwa [Homeomorph.coe_mulLeft] at h
  obtain ⟨c, -, hc⟩ :=
    exists_eq_smul_of_isMulRightInvariant_of_isOpenPosMeasure (Measure.map (fun p : ↥mirabolic => g * p) μP) μP
  have h1 : Measure.map (fun p : ↥mirabolic => g * p) μP B = 0 := by
    rw [hc, Measure.smul_apply, h0, smul_zero]
  rwa [Measure.map_apply (measurable_const_mul g) hB] at h1

private theorem ae_measure_preimage_chartElement_mul_sec_eq_zero
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (μP : Measure ↥mirabolic) (P₂ : Subgroup ↥mirabolic)
    (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ))
    (μ₂ : Measure ↥P₂) [SFinite μ₂] (c : ℝ≥0∞) (hc0 : c ≠ 0)
    (hfib : μP = c • fibMeasure P₂ sec
      (fun p : ↥mirabolic => modulus (p : AdelicGL 3 (𝓞 ℚ) ℚ)) μ₂ leviHaar R)
    (hsec : Measurable sec) (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιm : Measurable ι)
    (hμ₂ι : μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))))
    (hgoodR : goodLeviRows S ⊆ R) {B : Set ↥mirabolic} (hB : MeasurableSet B) (h0 : μP B = 0) :
    ∀ᵐ r ∂leviHaar.restrict (goodLeviRows S),
      (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
          ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))))
        ((fun v => (ι v : ↥mirabolic) * sec r) ⁻¹' B) = 0 := by
  have hδ : Measurable fun p : ↥mirabolic => modulus (p : AdelicGL 3 (𝓞 ℚ) ℚ) :=
    measurable_modulus.comp measurable_subtype_coe
  have hind : Measurable (B.indicator (1 : ↥mirabolic → ℝ≥0∞)) := measurable_one.indicator hB

  have hfib0 : fibMeasure P₂ sec
      (fun p : ↥mirabolic => modulus (p : AdelicGL 3 (𝓞 ℚ) ℚ)) μ₂ leviHaar R B = 0 := by
    rw [hfib, Measure.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left hc0
  rw [← lintegral_indicator_one hB, lintegral_fibMeasure P₂ hsec hδ μ₂ leviHaar R hind] at hfib0

  have hw : Measurable fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      (modulus (sec x : AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ :=
    (measurable_modulus.comp (measurable_subtype_coe.comp hsec)).inv
  have hmeas : Measurable fun x : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
      (modulus (sec x : AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹ *
        ∫⁻ p : ↥P₂, B.indicator (1 : ↥mirabolic → ℝ≥0∞) ((p : ↥mirabolic) * sec x) ∂μ₂ :=
    hw.mul (measurable_fibreIntegral P₂ hsec μ₂ hind)
  have hae := (lintegral_eq_zero_iff hmeas).mp hfib0
  have hae' := ae_restrict_of_ae_restrict_of_subset hgoodR hae
  filter_upwards [hae'] with r hr
  have hslice : ∫⁻ p : ↥P₂, B.indicator (1 : ↥mirabolic → ℝ≥0∞) ((p : ↥mirabolic) * sec r) ∂μ₂ = 0 :=
    (mul_eq_zero.mp hr).resolve_left (ENNReal.inv_ne_zero.mpr (modulus_ne_top _))
  have hpre : MeasurableSet ((fun p : ↥P₂ => (p : ↥mirabolic) * sec r) ⁻¹' B) :=
    hB.preimage (measurable_subtype_coe.mul_const _)
  have hslice' : μ₂ ((fun p : ↥P₂ => (p : ↥mirabolic) * sec r) ⁻¹' B) = 0 := by
    rw [← lintegral_indicator_one hpre, ← hslice]
    congr 1

  rw [hμ₂ι, Measure.map_apply hιm hpre] at hslice'
  exact hslice'

private theorem ae_crossProfile_transportElement_eq_zero
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (μP : Measure ↥mirabolic)
    [μP.IsMulRightInvariant] [μP.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μP]
    (P₂ : Subgroup ↥mirabolic) (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ))
    (μ₂ : Measure ↥P₂) [SFinite μ₂] (c : ℝ≥0∞) (hc0 : c ≠ 0)
    (hfib : μP = c • fibMeasure P₂ sec
      (fun p : ↥mirabolic => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ)) μ₂ leviHaar R)
    (hsec : Measurable sec) (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ]
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιm : Measurable ι)
    (hμ₂ι : μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))))
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    (hgoodR : goodLeviRows S ⊆ R) (hgoodm : MeasurableSet (goodLeviRows S))
    (hK : ∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    {f f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hfc : Continuous f) (hf'c : Continuous f')
    (hzero : ∀ h : AdelicGL 3 (𝓞 ℚ) ℚ, h ∈ mirabolic →
      (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S → componentAt3 (𝓞 ℚ) ℚ q h ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q) →
        crossProfile S f f' sec ρ h =ᵐ[leviHaar.restrict (goodLeviRows S)] 0) :
    ∀ᵐ r ∂leviHaar.restrict (goodLeviRows S), ∀ᵐ r' ∂leviHaar.restrict (goodLeviRows S),
      ∀ᵐ y ∂ρ.restrict {y | UnitOutside S y},
        ∀ᵐ s ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s},
          ∀ᵐ a₂ ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s},
            ∀ᵐ a₃ ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s},
              crossProfile S f f' sec ρ (transportElement sec ι r' r (y, s, a₂, a₃) : AdelicGL 3 (𝓞 ℚ) ℚ) r' = 0 := by

  set good : Measure (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) := leviHaar.restrict (goodLeviRows S) with hgood_def
  set HI : Measure (AdeleRing (𝓞 ℚ) ℚ) :=
    (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s} with hHI_def
  set box : Measure ((AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) :=
    (ρ.restrict {y | UnitOutside S y}).prod (HI.prod (HI.prod HI)) with hbox_def
  haveI : SFinite good := sFinite_leviHaar_restrict _
  haveI : SFinite box := by
    rw [hbox_def, hHI_def]
    infer_instance
  have hI : MeasurableSet {s : AdeleRing (𝓞 ℚ) ℚ | IntegralOutsideAll S s} := measurableSet_integralOutsideAll S
  have hUm : MeasurableSet {y : (AdeleRing (𝓞 ℚ) ℚ)ˣ | UnitOutside S y} := measurableSet_setOf_unitOutside S
  have hbox_full : box = (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))).restrict
        ({y | UnitOutside S y} ×ˢ ({s | IntegralOutsideAll S s} ×ˢ
          ({s | IntegralOutsideAll S s} ×ˢ {s | IntegralOutsideAll S s}))) := by
    rw [hbox_def, hHI_def, Measure.prod_restrict, Measure.prod_restrict, Measure.prod_restrict]

  set Kset : Set ↥mirabolic := {h | ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
    componentAt3 (𝓞 ℚ) ℚ q (h : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q} with hKset_def
  set mK : Measure ↥mirabolic := μP.restrict Kset with hmK_def
  haveI : SFinite mK := by
    rw [hmK_def]
    infer_instance

  set F : ↥mirabolic × (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ :=
    fun p => crossProfile S f f' sec ρ (p.1 : AdelicGL 3 (𝓞 ℚ) ℚ) p.2 with hF_def
  have hFm : Measurable F := measurable_crossProfile_prod S hfc hf'c hsec ρ
  have hE : MeasurableSet (F ⁻¹' {0}ᶜ) := hFm (measurableSet_singleton (0 : ℂ)).compl
  have hE0 : MeasurableSet (F ⁻¹' {0}) := hFm (measurableSet_singleton (0 : ℂ))

  have hA : ∀ᵐ h ∂mK, good (Prod.mk h ⁻¹' (F ⁻¹' {0}ᶜ)) = 0 := by
    have hg : Measurable fun h : ↥mirabolic => good (Prod.mk h ⁻¹' (F ⁻¹' {0}ᶜ)) :=
      measurable_measure_prodMk_left hE
    have hset : MeasurableSet {h : ↥mirabolic | ¬ good (Prod.mk h ⁻¹' (F ⁻¹' {0}ᶜ)) = 0} :=
      hg (measurableSet_singleton (0 : ℝ≥0∞)).compl
    rw [ae_iff, hmK_def, Measure.restrict_apply hset]
    have hempty : {h : ↥mirabolic | ¬ good (Prod.mk h ⁻¹' (F ⁻¹' {0}ᶜ)) = 0} ∩ Kset = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun h ⟨hne, hhK⟩ => hne ?_
      have hz := hzero (h : AdelicGL 3 (𝓞 ℚ) ℚ) h.2 hhK
      exact ae_iff.mp hz
    rw [hempty, measure_empty]

  have hB : ∀ᵐ x ∂good, ∀ᵐ h ∂mK, F (h, x) = 0 := by
    have hA' : ∀ᵐ h ∂mK, ∀ᵐ x ∂good, F (h, x) = 0 := by
      filter_upwards [hA] with h hh
      exact ae_iff.mpr hh
    exact (Measure.ae_ae_comm (p := fun h x => F (h, x) = 0) hE0).mp hA'

  set W : ((Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) ×
      ((AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) → ℂ :=
    fun zv => F (transportElement sec ι zv.1.2 zv.1.1 zv.2, zv.1.2) with hW_def
  have hWm : Measurable W := by
    have hT : Measurable fun zv : ((Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) ×
        ((AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) =>
          transportElement sec ι zv.1.2 zv.1.1 zv.2 := by
      unfold transportElement
      exact ((hsec.comp (measurable_snd.comp measurable_fst)).inv.mul
        (measurable_subtype_coe.comp (hιm.comp measurable_snd))).mul (hsec.comp (measurable_fst.comp measurable_fst))
    exact hFm.comp (hT.prodMk (measurable_snd.comp measurable_fst))
  have hWbad : MeasurableSet (W ⁻¹' {0}ᶜ) := hWm (measurableSet_singleton (0 : ℂ)).compl
  have hC : ∀ᵐ x ∂good, ∀ᵐ r ∂good, box (Prod.mk (r, x) ⁻¹' (W ⁻¹' {0}ᶜ)) = 0 := by
    filter_upwards [hB, ae_restrict_mem hgoodm] with x hx hxgood

    have hnull : μP ({h : ↥mirabolic | ¬ F (h, x) = 0} ∩ Kset) = 0 := by
      have hset : MeasurableSet {h : ↥mirabolic | ¬ F (h, x) = 0} := hE.preimage measurable_prodMk_right
      have h1 := ae_iff.mp hx
      rwa [hmK_def, Measure.restrict_apply hset] at h1
    obtain ⟨B', hsubB', hB'm, hB'0⟩ := exists_measurable_superset_of_null hnull
    have hB''m : MeasurableSet ((fun p : ↥mirabolic => (sec x)⁻¹ * p) ⁻¹' B') := hB'm.preimage (measurable_const_mul _)
    have hB''0 : μP ((fun p : ↥mirabolic => (sec x)⁻¹ * p) ⁻¹' B') = 0 :=
      measure_preimage_mul_left_eq_zero μP (sec x)⁻¹ hB'm hB'0
    filter_upwards [ae_measure_preimage_chartElement_mul_sec_eq_zero S μP P₂ sec R μ₂ c hc0 hfib hsec ρ ι hιm hμ₂ι
      hgoodR hB''m hB''0, ae_restrict_mem hgoodm] with r hr hrgood

    have hWr : MeasurableSet (Prod.mk (r, x) ⁻¹' (W ⁻¹' {0}ᶜ)) := hWbad.preimage measurable_prodMk_left
    rw [hbox_full, Measure.restrict_apply hWr]
    refine measure_mono_null (fun v ⟨hvbad, hvbox⟩ => ?_) hr
    obtain ⟨hvy, hvs, hva₂, hva₃⟩ := hvbox
    have hmemK : transportElement sec ι x r v ∈ Kset := fun q hq =>
      componentAt3_transportElement_mem S ι hιmat hK hxgood hrgood hvy hvs hva₂ hva₃ q hq
    have hin : transportElement sec ι x r v ∈ B' := hsubB' ⟨hvbad, hmemK⟩
    show (sec x)⁻¹ * ((ι v : ↥mirabolic) * sec r) ∈ B'
    rwa [← mul_assoc]

  have hWslice : MeasurableSet {z : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) × (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) |
      box (Prod.mk z ⁻¹' (W ⁻¹' {0}ᶜ)) = 0} :=
    measurable_measure_prodMk_left hWbad (measurableSet_singleton (0 : ℝ≥0∞))
  have hD : ∀ᵐ r ∂good, ∀ᵐ x ∂good, box (Prod.mk (r, x) ⁻¹' (W ⁻¹' {0}ᶜ)) = 0 :=
    (Measure.ae_ae_comm (p := fun r x => box (Prod.mk (r, x) ⁻¹' (W ⁻¹' {0}ᶜ)) = 0) hWslice).mpr hC

  filter_upwards [hD] with r hr
  filter_upwards [hr] with x hx
  have hae : ∀ᵐ v ∂box, W ((r, x), v) = 0 := by
    rw [ae_iff]
    exact hx
  rw [hbox_def] at hae
  have h1 := Measure.ae_ae_of_ae_prod hae
  filter_upwards [h1] with y hy
  have h2 := Measure.ae_ae_of_ae_prod hy
  filter_upwards [h2] with s hs
  have h3 := Measure.ae_ae_of_ae_prod hs
  filter_upwards [h3] with a₂ ha₂
  filter_upwards [ha₂] with a₃ ha₃
  exact ha₃

end TransferLayer
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem ae_integral_conj_torusProfile_mul_eq_zero
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (μP : Measure ↥mirabolic)
    [μP.IsMulRightInvariant] [μP.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μP]
    (P₂ : Subgroup ↥mirabolic) (sec : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ↥mirabolic) (R : Set (Fin 2 → AdeleRing (𝓞 ℚ) ℚ))
    (μ₂ : Measure ↥P₂) [SFinite μ₂] (c : ℝ≥0∞) (hc0 : c ≠ 0)
    (hfib : μP = c • fibMeasure P₂ sec
      (fun p : ↥mirabolic => modulus (p : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ)) μ₂ leviHaar R)
    (hsec : Measurable sec) (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [SFinite ρ]
    (ι : (AdeleRing (𝓞 ℚ) ℚ)ˣ × (AdeleRing (𝓞 ℚ) ℚ × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)) → ↥P₂)
    (hιm : Measurable ι)
    (hμ₂ι : μ₂ = Measure.map ι (ρ.prod ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))))
    (hιmat : ∀ v, (((ι v : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![(v.1 : AdeleRing (𝓞 ℚ) ℚ), v.2.1, v.2.2.1; 0, 1, v.2.2.2; 0, 0, 1])
    (hgoodR : goodLeviRows S ⊆ R) (hgoodm : MeasurableSet (goodLeviRows S))
    (hK : ∀ r ∈ goodLeviRows S, ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S →
      componentAt3 (𝓞 ℚ) ℚ q (sec r : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (hchartι : ∀ v, mirabolicChart (ι v : ↥mirabolic) = v)
    {f f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hfc : Continuous f) (hf'c : Continuous f')
    (hfN : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      𝓦 f (upperUnipotent3 x y z * g) = NumberField.StandardAddChar.psiQ (x + y) * 𝓦 f g)
    (hzero : ∀ h : AdelicGL 3 (𝓞 ℚ) ℚ, h ∈ mirabolic →
      (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S → componentAt3 (𝓞 ℚ) ℚ q h ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q) →
        crossProfile S f f' sec ρ h =ᵐ[leviHaar.restrict (goodLeviRows S)] 0) :
    ∀ᵐ r ∂leviHaar.restrict (goodLeviRows S), ∀ᵐ r' ∂leviHaar.restrict (goodLeviRows S),
      ∀ᵐ y ∂ρ.restrict {y | UnitOutside S y},
        ∀ᵐ s ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s},
          ∫ x, NumberField.StandardAddChar.psiQ (-((x : AdeleRing (𝓞 ℚ) ℚ) * s)) *
            ((starRingEnd ℂ) (torusProfile f sec r (x * y)) * torusProfile f' sec r' x)
              ∂ρ.restrict {y | UnitOutside S y} = 0 := by
  have hT := ae_crossProfile_transportElement_eq_zero S μP P₂ sec R μ₂ c hc0 hfib hsec ρ ι hιm hμ₂ι hιmat hgoodR
    hgoodm hK hfc hf'c hzero
  have _ := hchartι
  haveI : (MeasureTheory.ae
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s})).NeBot :=
    MeasureTheory.ae_neBot.mpr (restrict_setOf_integralOutsideAll_ne_zero S)
  filter_upwards [hT] with r hr
  filter_upwards [hr] with r' hr'
  filter_upwards [hr'] with y hy
  filter_upwards [hy] with s hs
  obtain ⟨a₂, ha₂⟩ := hs.exists
  obtain ⟨a₃, ha₃⟩ := ha₂.exists
  rw [crossProfile_transportElement S sec ρ ι hιmat hfN r r' (y, s, a₂, a₃)] at ha₃
  exact (mul_eq_zero.mp ha₃).resolve_left (psiQ_ne_zero _)

end PairClause
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

private theorem exists_row_profiles
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (f f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hfcusp : f ∈ cuspFunctions ω a b Φ₀) (hf'cusp : f' ∈ cuspFunctions ω a b Φ₀)
    (hKf : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hKf' : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f')
    (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hP : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      g ∈ P ↔ (fun j => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) =
        (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
    (μP : Measure ↥P) (hμP : μP.IsMulRightInvariant) (hμPo : μP.IsOpenPosMeasure)
    (hμPc : IsFiniteMeasureOnCompacts μP) (c₀ : ℝ≥0∞) (hc₀ : c₀ ≠ 0) (hc₀top : c₀ ≠ ⊤)
    (hν : ν = c₀ •
      (Measure.map Quotient.mk''
        (μP.withDensity fun p : ↥P =>
          HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
              (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
            {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
                ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
                  k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
                    componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k}.indicator (fun _ => (1 : ℝ≥0∞))
              (p : AdelicGL 3 (𝓞 ℚ) ℚ)) :
        Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P)))
    (hvan :
      ∀ g g' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
        ∫ q, (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (translateRight g f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)) *
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (translateRight g' f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν = 0)
    (hff :
      ∃ c : ℝ, 0 < c ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f ∈ automorphicSubmodule ω a b Φ₀)
            (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' f ∈ automorphicSubmodule ω a b Φ₀),
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
          ∫ q, (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)) *
              whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g' f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν =
        c * ⟪toL2 ω a b Φ₀ ⟨translateRight g f, hg⟩, toL2 ω a b Φ₀ ⟨translateRight g' f, hg'⟩⟫_ℂ) ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f ∈ automorphicSubmodule ω a b Φ₀),
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
          ∂ν = ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight g f, hg⟩‖ ^ 2)))
    (hf'f' :
      ∃ c : ℝ, 0 < c ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f' ∈ automorphicSubmodule ω a b Φ₀)
            (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' f' ∈ automorphicSubmodule ω a b Φ₀),
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
          ∫ q, (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)) *
              whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g' f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν =
        c * ⟪toL2 ω a b Φ₀ ⟨translateRight g f', hg⟩, toL2 ω a b Φ₀ ⟨translateRight g' f', hg'⟩⟫_ℂ) ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f' ∈ automorphicSubmodule ω a b Φ₀),
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
          ∂ν = ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight g f', hg⟩‖ ^ 2))) :
    ∃ (m : Measure (Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) (ρ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) (w : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ≥0∞)
      (k l : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ),
      SFinite m ∧ SFinite ρ ∧ ρ {y | ¬ UnitOutside S y} = 0 ∧
      (∀ y, UnitOutside S y → w y ≠ 0 ∧ w y ≠ ⊤) ∧
      (∀ y, UnitOutside S y → ∀ F : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ≥0∞, Measurable F →
        ∫⁻ x, F (x * y) ∂ρ = w y * ∫⁻ x, F x ∂ρ) ∧
      (∀ᵐ r ∂m, Measurable (k r) ∧ ∫⁻ x, (‖k r x‖₊ : ℝ≥0∞) ^ 2 ∂ρ ≠ ⊤ ∧
        ∀ x u, UnitOutsideTrivialInside S u → k r (x * u) = k r x) ∧
      (∀ᵐ r ∂m, Measurable (l r) ∧ ∫⁻ x, (‖l r x‖₊ : ℝ≥0∞) ^ 2 ∂ρ ≠ ⊤ ∧
        ∀ x u, UnitOutsideTrivialInside S u → l r (x * u) = l r x) ∧
      (∀ᵐ r ∂m, ∀ᵐ r' ∂m,
        ∀ᵐ y ∂ρ, ∀ᵐ s ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict {s | IntegralOutsideAll S s},
          ∫ x, NumberField.StandardAddChar.psiQ (-((x : AdeleRing (𝓞 ℚ) ℚ) * s)) *
            ((starRingEnd ℂ) (k r (x * y)) * l r' x) ∂ρ = 0) ∧
      ((∀ᵐ r ∂m, k r =ᵐ[ρ] 0) →
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ f 1 = 0) ∧
      ((∀ᵐ r ∂m, l r =ᵐ[ρ] 0) →
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ f' 1 = 0) := by
  classical
  haveI : μP.IsMulRightInvariant := hμP
  haveI : μP.IsOpenPosMeasure := hμPo
  haveI : IsFiniteMeasureOnCompacts μP := hμPc
  obtain rfl : P = mirabolic := eq_mirabolic_of_forall_mem_iff P hP
  obtain ⟨P₂, sec, R, μ₂, c, ⟨hc0, hctop, hfib⟩, hP₂, hsec, hsecrow, hshell, hgoodR,
    ⟨ρ, w, hρsf, hw, hdil, hchart, ι, hιm, hμ₂ι, hchartι, hιmat⟩, hμ₂sf, hK, hgoodm⟩ := exists_levi_fibration S μP
  haveI : SFinite ρ := hρsf
  haveI : SFinite μ₂ := hμ₂sf
  have hU := measurableSet_setOf_unitOutside S
  have hfc : Continuous f := ((mem_cuspFunctions_iff ω a b Φ₀ f).mp hfcusp).2.1
  have hf'c : Continuous f' := ((mem_cuspFunctions_iff ω a b Φ₀ f').mp hf'cusp).2.1
  have hfautm : f ∈ automorphicSubmodule ω a b Φ₀ := ((mem_cuspFunctions_iff ω a b Φ₀ f).mp hfcusp).1
  have hf'autm : f' ∈ automorphicSubmodule ω a b Φ₀ := ((mem_cuspFunctions_iff ω a b Φ₀ f').mp hf'cusp).1
  have hfaut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g :=
    ((mem_automorphicSubmodule_iff ω a b Φ₀ f).1 hfautm).1
  have hf'aut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f' (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f' g :=
    ((mem_automorphicSubmodule_iff ω a b Φ₀ f').1 hf'autm).1
  obtain ⟨hWfe, hWfn⟩ := whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul f hfaut
  obtain ⟨hWf'e, hWf'n⟩ := whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul f' hf'aut
  have h1f : translateRight 1 f = f := funext fun x => congrArg f (mul_one x)
  have h1f' : translateRight 1 f' = f' := funext fun x => congrArg f' (mul_one x)
  have hg1 : translateRight 1 f ∈ automorphicSubmodule ω a b Φ₀ := by
    rw [h1f]
    exact hfautm
  have hg1' : translateRight 1 f' ∈ automorphicSubmodule ω a b Φ₀ := by
    rw [h1f']
    exact hf'autm
  obtain ⟨cf, hcf, -, hsqf1⟩ := hff
  obtain ⟨cf', hcf', -, hsqf1'⟩ := hf'f'
  have hWf1 : ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ f ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν =
        ENNReal.ofReal (cf * ‖toL2 ω a b Φ₀ ⟨f, hfautm⟩‖ ^ 2) := by
    have h := hsqf1 1 hg1 (fun p _ => map_one _)
    rw [show (⟨translateRight 1 f, hg1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = ⟨f, hfautm⟩ from Subtype.ext h1f] at h
    rw [h1f] at h
    exact h
  have hWf1' : ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ f' ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν =
        ENNReal.ofReal (cf' * ‖toL2 ω a b Φ₀ ⟨f', hf'autm⟩‖ ^ 2) := by
    have h := hsqf1' 1 hg1' (fun p _ => map_one _)
    rw [show (⟨translateRight 1 f', hg1'⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = ⟨f', hf'autm⟩ from Subtype.ext h1f']
      at h
    rw [h1f'] at h
    exact h
  have hfinf : ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ f ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤ := by
    rw [hWf1]
    exact ENNReal.ofReal_ne_top
  have hfinf' : ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ f' ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤ := by
    rw [hWf1']
    exact ENNReal.ofReal_ne_top
  have hsqf : ∀ᵐ r ∂leviHaar.restrict (goodLeviRows S),
      ∫⁻ x, (‖torusProfile f sec r x‖₊ : ℝ≥0∞) ^ 2 ∂ρ.restrict {y | UnitOutside S y} ≠ ⊤ :=
    lintegral_sq_torusProfile_ne_top S μP hc₀ ν hν P₂ sec R μ₂ hc0 hfib hsec hgoodR hgoodm hK ρ ι hιm hμ₂ι hιmat hfc
      hWfn hfinf
  have hsqf' : ∀ᵐ r ∂leviHaar.restrict (goodLeviRows S),
      ∫⁻ x, (‖torusProfile f' sec r x‖₊ : ℝ≥0∞) ^ 2 ∂ρ.restrict {y | UnitOutside S y} ≠ ⊤ :=
    lintegral_sq_torusProfile_ne_top S μP hc₀ ν hν P₂ sec R μ₂ hc0 hfib hsec hgoodR hgoodm hK ρ ι hιm hμ₂ι hιmat hf'c
      hWf'n hfinf'
  refine ⟨leviHaar.restrict (goodLeviRows S), ρ.restrict {y | UnitOutside S y}, w, torusProfile f sec,
    torusProfile f' sec, sFinite_leviHaar_restrict _, inferInstance, ?_, fun y _ => hw y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.restrict_apply' hU]
    have he : ({y : (AdeleRing (𝓞 ℚ) ℚ)ˣ | ¬ UnitOutside S y} ∩ {y | UnitOutside S y}) = ∅ :=
      Set.ext fun y => ⟨fun hy => hy.1 hy.2, fun hy => hy.elim⟩
    rw [he, measure_empty]
  · intro y hy F hF
    have hmem : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ, x * y ∈ {y | UnitOutside S y} ↔ x ∈ {y | UnitOutside S y} := by
      intro x
      simp only [Set.mem_setOf_eq, UnitOutside, Units.val_mul, map_mul]
      exact forall₂_congr fun q hq => by rw [hy q hq, mul_one]
    have hind : (fun x => {y | UnitOutside S y}.indicator (fun x => F (x * y)) x) =
        fun x => {y | UnitOutside S y}.indicator F (x * y) := by
      funext x
      by_cases hx : x ∈ {y | UnitOutside S y}
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem x).mpr hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hmem x).mp h))]
    rw [← lintegral_indicator hU, ← lintegral_indicator hU, hind]
    exact hdil y _ (hF.indicator hU)
  · filter_upwards [hsqf, ae_restrict_mem hgoodm] with r hr hgood
    exact ⟨measurable_torusProfile hfc sec r, hr, fun x u hu => torusProfile_mul_eq S hfc hKf hK hgood x u hu⟩
  · filter_upwards [hsqf', ae_restrict_mem hgoodm] with r hr hgood
    exact ⟨measurable_torusProfile hf'c sec r, hr, fun x u hu => torusProfile_mul_eq S hf'c hKf' hK hgood x u hu⟩
  · have hffF : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (_ : translateRight g f ∈ automorphicSubmodule ω a b Φ₀),
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
          ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f) ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ :
              ℝ≥0∞) ^ 2) ∂ν ≠ ⊤ := fun g hg hg1 => by
      rw [hsqf1 g hg hg1]
      exact ENNReal.ofReal_ne_top
    have hf'f'F : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (_ : translateRight g f' ∈ automorphicSubmodule ω a b Φ₀),
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
          ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f') ((q.out : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ :
              ℝ≥0∞) ^ 2) ∂ν ≠ ⊤ := fun g hg hg1 => by
      rw [hsqf1' g hg hg1]
      exact ENNReal.ofReal_ne_top
    refine ae_integral_conj_torusProfile_mul_eq_zero S μP P₂ sec R μ₂ c hc0 hfib hsec ρ ι hιm hμ₂ι hιmat hgoodR hgoodm
      hK hchartι hfc hf'c hWfe fun h hh hhK => ?_
    obtain ⟨hFm, hFi, htests⟩ := crossProfile_tests S μP c₀ ν hν P₂ sec R μ₂ c hfib hsec ρ ι hιm hμ₂ι hιmat hc₀ hc₀top
      hc0 hctop hP₂ hsecrow hshell hgoodR hgoodm hK hω hΦ₀ hfc hf'c hKf hKf' hfcusp hf'cusp hffF hf'f'F hvan h hh hhK
    have hcov := crossProfile_covariance S sec R hsecrow hgoodR hK ρ w hw hdil hfc hf'c hKf hKf' hWfe hWf'e h hhK
    filter_upwards [ae_restrict_eq_zero_of_forall_integral_mul_eq_zero S hgoodm _ hFm hFi hcov htests] with x hx
    have hm : ((modulus (sec x : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ))⁻¹).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr
        ⟨ENNReal.inv_ne_zero.mpr (modulus_ne_top _), ENNReal.inv_ne_top.mpr (modulus_ne_zero _)⟩
    exact (mul_eq_zero.mp hx).resolve_left (Complex.ofReal_ne_zero.mpr hm)
  · intro h0
    exact whittaker3_eq_zero_of_torusProfile_ae_zero S μP c₀ ν hν P₂ hP₂ sec R μ₂ hfib hsec hsecrow hshell hgoodm hK ρ
      ι hιm hμ₂ι hιmat hΦ₀ hfautm hfc hWfn hcf hWf1 h0
  · intro h0
    exact whittaker3_eq_zero_of_torusProfile_ae_zero S μP c₀ ν hν P₂ hP₂ sec R μ₂ hfib hsec hsecrow hshell hgoodm hK ρ
      ι hιm hμ₂ι hιmat hΦ₀ hf'autm hf'c hWf'n hcf' hWf1' h0

end Transport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end MirabolicLeviFibration
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end RowTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section PairVanishing

noncomputable section

namespace MirabolicLeviFibration

section Parameters

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end Parameters
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end RowSets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section CosetDensity

section Translate

end Translate
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end CosetDensity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section UniquenessPrinciple

section UniquenessHead

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open Filter Topology Set

open scoped NNReal Classical

attribute [local instance] archBorel

attribute [local instance] archBorelSpace

attribute [local instance] localBorel

attribute [local instance] localBorelSpace

attribute [local instance] countable_primes

attribute [local instance] properCompletion archSecondCountable

attribute [local instance] secondCountableAdeles NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

attribute [local instance] borelRows

attribute [local instance] haarRows

attribute [local instance] localSecondCountable

attribute [local instance] archRowsSecondCountable localRowsSecondCountable

attribute [local instance] secondCountableCoords

attribute [local instance] archRowsBorel localRowsBorel

attribute [local instance] borelCoords

attribute [local instance] locallyCompactCoords

attribute [local instance] sigmaCompactCoords

attribute [local instance] coordsHaar_isAddHaarMeasure

attribute [local instance] sigmaFinite_coordsHaar

end UniquenessHead
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end UniquenessPrinciple
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section TorusStage

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end TorusStage
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section Transport

attribute [local instance] NumberField.AdelicHaar.adeleBorel

end Transport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

section WhittakerPairVanishing

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private theorem ae_or_ae_of_ae_ae {X : Type} [MeasurableSpace X] {m : Measure X} {A B : X → Prop}
    (h : ∀ᵐ r ∂m, ∀ᵐ r' ∂m, A r ∨ B r') : (∀ᵐ r ∂m, A r) ∨ (∀ᵐ r' ∂m, B r') := by
  by_cases hB : ∀ᵐ r' ∂m, B r'
  · exact Or.inr hB
  · refine Or.inl (h.mono fun r hr => ?_)
    by_contra ha
    exact hB (hr.mono fun r' hr' => hr'.resolve_left ha)

private theorem trivialOutside_mul (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {g h : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1)
    (hh : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p h = 1) :
    ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (g * h) = 1 := fun p hp => by
  rw [map_mul, hg p hp, hh p hp, one_mul]

private theorem isRightInvariant_translateRight {p : HeightOneSpectrum (𝓞 ℚ)} {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : componentAt3 (𝓞 ℚ) ℚ p h = 1) :
    IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) (translateRight h F) := by
  intro x u hu
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hu
  simp only [translateRight_apply]
  rw [mul_assoc, ← commute_localToAdelic3 hh k, ← mul_assoc]
  exact hF (x * h) _ (Subgroup.mem_map_of_mem (localToAdelic3 p) hk)

private theorem whittaker3_translateRight_one (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    whittaker3 pins ψ (translateRight h F) 1 = whittaker3 pins ψ F h := by
  rw [whittaker3_translateRight, one_mul]

private theorem conj_whittaker3_mul_whittaker3_eq_zero_of_row_profiles
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (f f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hfcusp : f ∈ cuspFunctions ω a b Φ₀) (hf'cusp : f' ∈ cuspFunctions ω a b Φ₀)
    (hKf : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hKf' : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f')
    (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hP : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      g ∈ P ↔ (fun j => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) =
        (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
    (μP : Measure ↥P) (hμP : μP.IsMulRightInvariant) (hμPo : μP.IsOpenPosMeasure)
    (hμPc : IsFiniteMeasureOnCompacts μP) (c₀ : ℝ≥0∞) (hc₀ : c₀ ≠ 0) (hc₀top : c₀ ≠ ⊤)
    (hν : ν = c₀ •
      (Measure.map Quotient.mk''
        (μP.withDensity fun p : ↥P =>
          HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
              (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
            {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
                ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
                  k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
                    componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k}.indicator (fun _ => (1 : ℝ≥0∞))
              (p : AdelicGL 3 (𝓞 ℚ) ℚ)) :
        Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P)))
    (hvan :
      ∀ g g' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
        ∫ q, (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (translateRight g f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)) *
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (translateRight g' f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν = 0)
    (hff :
      ∃ c : ℝ, 0 < c ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f ∈ automorphicSubmodule ω a b Φ₀)
            (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' f ∈ automorphicSubmodule ω a b Φ₀),
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
          ∫ q, (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)) *
              whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g' f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν =
        c * ⟪toL2 ω a b Φ₀ ⟨translateRight g f, hg⟩, toL2 ω a b Φ₀ ⟨translateRight g' f, hg'⟩⟫_ℂ) ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f ∈ automorphicSubmodule ω a b Φ₀),
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
          ∂ν = ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight g f, hg⟩‖ ^ 2)))
    (hf'f' :
      ∃ c : ℝ, 0 < c ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f' ∈ automorphicSubmodule ω a b Φ₀)
            (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' f' ∈ automorphicSubmodule ω a b Φ₀),
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
          ∫ q, (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)) *
              whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g' f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν =
        c * ⟪toL2 ω a b Φ₀ ⟨translateRight g f', hg⟩, toL2 ω a b Φ₀ ⟨translateRight g' f', hg'⟩⟫_ℂ) ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f' ∈ automorphicSubmodule ω a b Φ₀),
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
          ∂ν = ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight g f', hg⟩‖ ^ 2))) :
    ∀ g g' : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
        (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ f g) *
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ f' g' = 0 := by
  intro g g' hg hg'
  obtain ⟨hmem, -⟩ :=
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ f hfcusp
  obtain ⟨hmem', -⟩ :=
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ f' hf'cusp
  obtain ⟨m, ρ, w, k, l, -, hρs, hρ, hw, hshift, hk, hl, hpair, hclosek, hclosel⟩ :=
    exists_row_profiles S ω hω a b Φ₀ hΦ₀ (translateRight g f) (translateRight g' f') (hmem g) (hmem' g')
      (fun p hp => isRightInvariant_translateRight (hKf p hp) (hg p hp))
      (fun p hp => isRightInvariant_translateRight (hKf' p hp) (hg' p hp)) P hP ν μP hμP hμPo hμPc c₀ hc₀ hc₀top hν
      (by
        intro h h' hh hh'
        simp only [← translateRight_mul]
        exact hvan _ _ (trivialOutside_mul S hh hg) (trivialOutside_mul S hh' hg'))
      (by
        obtain ⟨c, hc, h₁, h₂⟩ := hff
        refine ⟨c, hc, fun h hh h' hh' hS hS' => ?_, fun h hh hS => ?_⟩
        · simpa only [translateRight_mul] using
            h₁ (h * g) (by rw [translateRight_mul]; exact hh) (h' * g) (by rw [translateRight_mul]; exact hh')
              (trivialOutside_mul S hS hg) (trivialOutside_mul S hS' hg)
        · simpa only [translateRight_mul] using
            h₂ (h * g) (by rw [translateRight_mul]; exact hh) (trivialOutside_mul S hS hg))
      (by
        obtain ⟨c, hc, h₁, h₂⟩ := hf'f'
        refine ⟨c, hc, fun h hh h' hh' hS hS' => ?_, fun h hh hS => ?_⟩
        · simpa only [translateRight_mul] using
            h₁ (h * g') (by rw [translateRight_mul]; exact hh) (h' * g') (by rw [translateRight_mul]; exact hh')
              (trivialOutside_mul S hS hg') (trivialOutside_mul S hS' hg')
        · simpa only [translateRight_mul] using
            h₂ (h * g') (by rw [translateRight_mul]; exact hh) (trivialOutside_mul S hS hg'))
  haveI := hρs
  have hdisj : ∀ᵐ r ∂m, ∀ᵐ r' ∂m, k r =ᵐ[ρ] 0 ∨ l r' =ᵐ[ρ] 0 := by
    filter_upwards [hk, hpair] with r hkr hpr
    filter_upwards [hl, hpr] with r' hlr' hvr'
    exact profile_eq_zero_or_eq_zero S ρ hρ w hw hshift (k r) (l r') hkr.1 hlr'.1 hkr.2.1 hlr'.2.1 hkr.2.2
      hlr'.2.2 hvr'
  rcases ae_or_ae_of_ae_ae hdisj with h | h
  · rw [← whittaker3_translateRight_one _ _ g f, hclosek h, map_zero, zero_mul]
  · rw [← whittaker3_translateRight_one _ _ g' f', hclosel h, mul_zero]

end WhittakerPairVanishing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end MirabolicLeviFibration
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (f f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hfcusp : f ∈ cuspFunctions ω a b Φ₀) (hf'cusp : f' ∈ cuspFunctions ω a b Φ₀)
    (hKf : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hKf' : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f')
    (hHf :
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen1 p)) f (lam1 p)) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen2 p)) f (lam2 p)))
    (hHf' :
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen1 p)) f' (lam1 p)) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen2 p)) f' (lam2 p)))
    (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hP : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      g ∈ P ↔ (fun j => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) =
        (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
    (μP : Measure ↥P) (hμP : μP.IsMulRightInvariant) (hμPo : μP.IsOpenPosMeasure)
    (hμPc : IsFiniteMeasureOnCompacts μP) (c₀ : ℝ≥0∞) (hc₀ : c₀ ≠ 0) (hc₀top : c₀ ≠ ⊤)
    (hν : ν = c₀ •
      (Measure.map Quotient.mk''
        (μP.withDensity fun p : ↥P =>
          HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
              (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
            {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
                ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
                  k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
                    componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k}.indicator (fun _ => (1 : ℝ≥0∞))
              (p : AdelicGL 3 (𝓞 ℚ) ℚ)) :
        Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P)))
    (hvan :
      ∀ g g' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
        ∫ q, (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (translateRight g f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)) *
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (translateRight g' f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν = 0)
    (hff :
      ∃ c : ℝ, 0 < c ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f ∈ automorphicSubmodule ω a b Φ₀)
            (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' f ∈ automorphicSubmodule ω a b Φ₀),
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
          ∫ q, (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)) *
              whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g' f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν =
        c * ⟪toL2 ω a b Φ₀ ⟨translateRight g f, hg⟩, toL2 ω a b Φ₀ ⟨translateRight g' f, hg'⟩⟫_ℂ) ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f ∈ automorphicSubmodule ω a b Φ₀),
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
          ∂ν = ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight g f, hg⟩‖ ^ 2)))
    (hf'f' :
      ∃ c : ℝ, 0 < c ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f' ∈ automorphicSubmodule ω a b Φ₀)
            (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' f' ∈ automorphicSubmodule ω a b Φ₀),
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
          ∫ q, (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)) *
              whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g' f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν =
        c * ⟪toL2 ω a b Φ₀ ⟨translateRight g f', hg⟩, toL2 ω a b Φ₀ ⟨translateRight g' f', hg'⟩⟫_ℂ) ∧
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f' ∈ automorphicSubmodule ω a b Φ₀),
          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight g f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
          ∂ν = ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight g f', hg⟩‖ ^ 2))) :
    ∀ g g' : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
        (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ f g) *
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ f' g' = 0 := by
  have _ := lam1
  have _ := lam2
  have _ := hHf
  have _ := hHf'
  exact MirabolicLeviFibration.conj_whittaker3_mul_whittaker3_eq_zero_of_row_profiles S ω hω a b Φ₀ hΦ₀ f f' hfcusp
    hf'cusp hKf hKf' P hP ν μP hμP hμPo hμPc c₀ hc₀ hc₀top hν hvan hff hf'f'

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end PairVanishing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero.MirabolicLeviFibration"

end S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero (solution)
