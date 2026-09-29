-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/9c813736-eed0-5387-be4c-e63391c47764

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_whittakerBlock_one_eq_lintegral_and_eq_smul_map_withDensity_haar
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.fnTwist3_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support"
p2m_attr_erase "simp" "RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction.SlabL2
open LanglandsTunnell.CubicInduction
open scoped ENNReal InnerProductSpace
attribute [local instance] NumberField.AdelicHaar.glBorel

section RowFurniture

noncomputable section

namespace Fibration

section Furniture

private def e₃ : Fin 3 → AdeleRing (𝓞 ℚ) ℚ := fun j => if j = 2 then 1 else 0

end Furniture

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private abbrev evalHom (q : HeightOneSpectrum (𝓞 ℚ)) : AdeleRing (𝓞 ℚ) ℚ →+* q.adicCompletion ℚ :=
  (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ q).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private def PrimitiveAt (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  (∀ j, evalHom p (x j) ∈ p.adicCompletionIntegers ℚ) ∧ ∃ j, Valued.v (evalHom p (x j)) = 1

private def NonzeroAt (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  ∃ j, evalHom p (x j) ≠ 0

private def NonzeroArch (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  ∃ j, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j) ≠ 0

private def explicitRows (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  {x | (∀ p, p ∉ S → PrimitiveAt p x) ∧ (∀ p ∈ S, NonzeroAt p x) ∧ NonzeroArch x}

private abbrev rowHaar : Measure (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

end RowSets

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

private def glOf (A B : Matrix (Fin 3) (Fin 3) R) (h : A * B = 1) : GL (Fin 3) R :=
  ⟨A, B, h, mul_eq_one_comm.mp h⟩

end Generation

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

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

end RowAction

end JacobianUnimodular

end JacobianAndModulus

section CosetDensity

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

end Block

section Translate

private theorem whittaker3_translateRight (pins : AutomorphicForm.CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ (SlabL2.translateRight h F) g = whittaker3 pins ψ F (g * h) := by
  simp only [whittaker3, SlabL2.translateRight_apply, mul_assoc]

end Translate

end CosetDensity

section ShellCondition

section Shell

private def ShellCond (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
    ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
      k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k

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

private theorem continuous_evalHom (q : HeightOneSpectrum (𝓞 ℚ)) : Continuous (evalHom q) :=
  (AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ q).comp continuous_snd

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

end Shell

end ShellCondition

section SectionAndRowSets

section SectionHeads

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

open scoped RestrictedProduct

open Topology

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

private theorem arch_add_apply (a b : 𝔸) (w : InfinitePlace ℚ) : (a + b).1 w = a.1 w + b.1 w := rfl

private theorem arch_zero_apply (w : InfinitePlace ℚ) : (0 : 𝔸).1 w = 0 := rfl

private theorem fin_add_apply (a b : 𝔸) (p : HeightOneSpectrum (𝓞 ℚ)) : (a + b).2 p = a.2 p + b.2 p := rfl

private theorem adeleArch_eq (a : 𝔸) : AdelicLevel.adeleArch (𝓞 ℚ) ℚ a = a.1 := rfl

private def rowAt (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) : Fin 3 → p.adicCompletion ℚ := fun j => (x j).2 p

private def rowArch (w : InfinitePlace ℚ) (x : Fin 3 → 𝔸) : Fin 3 → w.Completion := fun j => (x j).1 w

private theorem rowAt_apply (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) (j : Fin 3) : rowAt p x j = (x j).2 p := rfl

private theorem rowArch_apply (w : InfinitePlace ℚ) (x : Fin 3 → 𝔸) (j : Fin 3) : rowArch w x j = (x j).1 w := rfl

private theorem mem_explicitRows {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {x : Fin 3 → 𝔸} :
    x ∈ explicitRows S ↔ (∀ p, p ∉ S → PrimitiveAt p x) ∧ (∀ p ∈ S, NonzeroAt p x) ∧ NonzeroArch x :=
  Iff.rfl

private theorem primitiveAt_iff (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) :
    PrimitiveAt p x ↔ (∀ j, Valued.v (rowAt p x j) ≤ 1) ∧ ∃ j, Valued.v (rowAt p x j) = 1 :=
  Iff.rfl

private theorem nonzeroAt_iff (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) : NonzeroAt p x ↔ ∃ j, rowAt p x j ≠ 0 :=
  Iff.rfl

private theorem nonzeroArch_of_rowArch {x : Fin 3 → 𝔸} {w : InfinitePlace ℚ} (h : ∃ j, rowArch w x j ≠ 0) :
    NonzeroArch x := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun h0 => hj (by rw [rowArch_apply, ← adeleArch_eq, h0]; rfl)⟩

private theorem val_componentAt3 (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (componentAt3 (𝓞 ℚ) ℚ p g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      (g : Matrix (Fin 3) (Fin 3) 𝔸).map (evalHom p) := rfl

private theorem val_componentAt3_inv (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (((componentAt3 (𝓞 ℚ) ℚ p g)⁻¹ : Matrix.GeneralLinearGroup (Fin 3) (p.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      ((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸).map (evalHom p) := rfl

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

private theorem measurableSet_rowArch_ne_zero (w : InfinitePlace ℚ) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → 𝔸 | rowArch w x j ≠ 0} := by
  have h : IsOpen {y : w.Completion | y ≠ 0} := isOpen_ne
  exact (h.preimage (continuous_rowArch w j)).measurableSet

private theorem rowAt_e₃ (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) : rowAt p e₃ j = if j = 2 then 1 else 0 := by
  fin_cases j <;> rfl

private theorem rowArch_e₃ (w : InfinitePlace ℚ) (j : Fin 3) : rowArch w e₃ j = if j = 2 then 1 else 0 := by
  fin_cases j <;> rfl

private theorem valued_rowAt_e₃_two (p : HeightOneSpectrum (𝓞 ℚ)) : Valued.v (rowAt p e₃ 2) = 1 := by
  rw [rowAt_e₃, if_pos rfl]
  exact map_one _

private theorem rowArch_e₃_two_ne_zero (w : InfinitePlace ℚ) : rowArch w e₃ 2 ≠ 0 := by
  rw [rowArch_e₃, if_pos rfl]
  exact one_ne_zero

private theorem primitiveAt_e₃ (p : HeightOneSpectrum (𝓞 ℚ)) : PrimitiveAt p e₃ := by
  refine (primitiveAt_iff p e₃).mpr ⟨fun j => ?_, 2, valued_rowAt_e₃_two p⟩
  rw [rowAt_e₃]
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

private theorem e₃_two_fin (v : HeightOneSpectrum (𝓞 ℚ)) : (e₃ 2).2 v = 1 := rfl

private theorem valued_e₃_fin_le_one (j : Fin 3) (v : HeightOneSpectrum (𝓞 ℚ)) : Valued.v ((e₃ j).2 v) ≤ 1 :=
  ((primitiveAt_iff v e₃).mp (primitiveAt_e₃ v)).1 j

private def goodRows (W : Fin 3 → Set (InfiniteAdeleRing ℚ)) (N : ℕ) : Set (Fin 3 → 𝔸) :=
  {x | (∀ j, (x j).1 ∈ W j ∧ x j ∈ finBox N (e₃ j)) ∧ rowArch default x 2 ≠ 0}

private theorem mem_goodRows {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 3 → 𝔸} :
    x ∈ goodRows W N ↔ (∀ j, (x j).1 ∈ W j ∧ x j ∈ finBox N (e₃ j)) ∧ rowArch default x 2 ≠ 0 :=
  Iff.rfl

private theorem measurableSet_goodRows {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} (hW : ∀ j, IsOpen (W j)) (N : ℕ) :
    MeasurableSet (goodRows W N) := by
  have : goodRows W N = (⋂ j, (fun x : Fin 3 → 𝔸 => x j) ⁻¹' ((fun b : 𝔸 => b.1) ⁻¹' W j ∩ finBox N (e₃ j))) ∩
      {x | rowArch default x 2 ≠ 0} := by
    ext x
    simp only [goodRows, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  refine (MeasurableSet.iInter fun j => measurable_pi_apply j ?_).inter (measurableSet_rowArch_ne_zero default 2)
  have hWj : IsOpen ((fun b : 𝔸 => b.1) ⁻¹' W j) := (hW j).preimage continuous_fst
  exact hWj.measurableSet.inter (measurableSet_finBox N (e₃ j))

private theorem goodRows_mem_nhds {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} (hW : ∀ j, IsOpen (W j))
    (hW₃ : ∀ j, (e₃ j).1 ∈ W j) {N : ℕ} (hN : N ≠ 0) : goodRows W N ∈ nhds e₃ := by
  have hj : ∀ j : Fin 3, (fun x : Fin 3 → 𝔸 => x j) ⁻¹' (Prod.fst ⁻¹' W j ∩ finBox N (e₃ j)) ∈ nhds e₃ := fun j =>
    (continuous_apply j).continuousAt.preimage_mem_nhds
      (Filter.inter_mem (continuous_fst.continuousAt.preimage_mem_nhds ((hW j).mem_nhds (hW₃ j)))
        (finBox_mem_nhds hN (e₃ j)))
  have harch : {x : Fin 3 → 𝔸 | rowArch default x 2 ≠ 0} ∈ nhds e₃ :=
    (continuous_rowArch default 2).continuousAt.eventually_ne (rowArch_e₃_two_ne_zero default)
  filter_upwards [Filter.iInter_mem.mpr hj, harch] with x hx hx'
  exact mem_goodRows.mpr ⟨fun j => Set.mem_iInter.mp hx j, hx'⟩

private theorem goodRows_subset_pi {W K : Fin 3 → Set (InfiniteAdeleRing ℚ)} (hWK : ∀ j, W j ⊆ K j) (N : ℕ) :
    goodRows W N ⊆ Set.univ.pi fun j => K j ×ˢ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro x hx j _
  obtain ⟨hx, -⟩ := mem_goodRows.mp hx
  refine Set.mem_prod.mpr ⟨hWK j (hx j).1, fun v => ?_⟩
  have h : (x j).2 v = (x j - e₃ j).2 v + (e₃ j).2 v := by rw [← fin_add_apply, sub_add_cancel]
  rw [h]
  refine add_mem ?_ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (valued_e₃_fin_le_one j v))
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (((hx j).2 v).trans (levelRadius_le_one N v))

private theorem measure_goodRows_ne_top {W K : Fin 3 → Set (InfiniteAdeleRing ℚ)} (hK : ∀ j, IsCompact (K j))
    (hWK : ∀ j, W j ⊆ K j) (N : ℕ) : rowHaar (goodRows W N) ≠ ⊤ :=
  ((measure_mono (goodRows_subset_pi hWK N)).trans_lt (IsFiniteMeasureOnCompacts.lt_top_of_isCompact
    (isCompact_univ_pi fun j => (hK j).prod (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 ℚ) ℚ)))).ne

private theorem valued_rowAt_le_one_of_mem_goodRows {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 3 → 𝔸}
    (hx : x ∈ goodRows W N) (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) : Valued.v (rowAt v x j) ≤ 1 := by
  have h : rowAt v x j = (x j - e₃ j).2 v + (e₃ j).2 v := by rw [rowAt_apply, ← fin_add_apply, sub_add_cancel]
  rw [h]
  exact Valuation.map_add_le _ (((mem_goodRows.mp hx).1 j).2 v |>.trans (levelRadius_le_one N v))
    (valued_e₃_fin_le_one j v)

private theorem valued_rowAt_two_of_mem_goodRows {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 3 → 𝔸}
    (hx : x ∈ goodRows W N) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : residueChar v ∣ N) : Valued.v (rowAt v x 2) = 1 := by
  have h : rowAt v x 2 = 1 + (x 2 - e₃ 2).2 v := by
    rw [rowAt_apply, add_comm, ← e₃_two_fin v, ← fin_add_apply, sub_add_cancel]
  rw [h]
  exact Valuation.map_one_add_of_lt _ (((mem_goodRows.mp hx).1 2).2 v |>.trans_lt (levelRadius_lt_one hv))

private theorem primitiveAt_of_mem_goodRows {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 3 → 𝔸}
    (hx : x ∈ goodRows W N) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : residueChar v ∣ N) : PrimitiveAt v x :=
  (primitiveAt_iff v x).mpr ⟨valued_rowAt_le_one_of_mem_goodRows hx v, 2, valued_rowAt_two_of_mem_goodRows hx hv⟩

private theorem nonzeroAt_of_mem_goodRows {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 3 → 𝔸}
    (hx : x ∈ goodRows W N) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : residueChar v ∣ N) : NonzeroAt v x :=
  (nonzeroAt_iff v x).mpr ⟨2, fun h => by
    have h1 := valued_rowAt_two_of_mem_goodRows hx hv
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

private abbrev shiftRow (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) (r : v.adicCompletion ℚ) : Fin 3 → 𝔸 :=
  Pi.single j (singleAt v r)

private theorem shiftRow_apply_fst (v : HeightOneSpectrum (𝓞 ℚ)) (j i : Fin 3) (r : v.adicCompletion ℚ)
    (w : InfinitePlace ℚ) : (shiftRow v j r i).1 w = 0 := by
  by_cases h : i = j
  · rw [h]
    simp only [shiftRow, Pi.single_eq_same, singleAt_arch]
  · simp only [shiftRow, Pi.single_eq_of_ne h, arch_zero_apply]

private theorem rowArch_add_shiftRow (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) (r : v.adicCompletion ℚ)
    (x : Fin 3 → 𝔸) (w : InfinitePlace ℚ) (i : Fin 3) : rowArch w (x + shiftRow v j r) i = rowArch w x i := by
  rw [rowArch_apply, rowArch_apply, Pi.add_apply, arch_add_apply, shiftRow_apply_fst, add_zero]

private theorem rowAt_add_shiftRow_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) (j i : Fin 3) (h : i ≠ j)
    (r : v.adicCompletion ℚ) (x : Fin 3 → 𝔸) : rowAt v (x + shiftRow v j r) i = rowAt v x i := by
  simp only [rowAt_apply, Pi.add_apply, shiftRow, Pi.single_eq_of_ne h, add_zero]

private theorem rowAt_shiftRow_add (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) (r : v.adicCompletion ℚ) (x : Fin 3 → 𝔸) :
    rowAt v (shiftRow v j r + x) j = r + rowAt v x j := by
  simp only [rowAt_apply, Pi.add_apply, shiftRow, Pi.single_eq_same, fin_add_apply, singleAt_fin_self]

private theorem add_shiftRow_mem_goodRows_iff {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ}
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : levelRadius N v = 1) (j : Fin 3) {r : v.adicCompletion ℚ} (hr : Valued.v r ≤ 1)
    (x : Fin 3 → 𝔸) : x + shiftRow v j r ∈ goodRows W N ↔ x ∈ goodRows W N := by
  simp only [mem_goodRows, rowArch_add_shiftRow]
  refine and_congr (forall_congr' fun i => ?_) Iff.rfl
  by_cases h : i = j
  · rw [h]
    simp only [Pi.add_apply, shiftRow, Pi.single_eq_same]
    rw [fst_add_singleAt, add_singleAt_mem_finBox_iff hv hr]
  · simp only [Pi.add_apply, shiftRow, Pi.single_eq_of_ne h, add_zero]

private theorem measurableSet_valued_rowAt_lt_one (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → 𝔸 | Valued.v (rowAt v x j) < 1} := by
  have : {x : Fin 3 → 𝔸 | Valued.v (rowAt v x j) < 1} =
      {x | Valued.v (rowAt v x j) ≤ 1} \ {x | Valued.v (rowAt v x j) = 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_diff, lt_iff_le_and_ne]
  rw [this]
  exact (measurableSet_valued_rowAt_le_one v j).diff (measurableSet_valued_rowAt_eq_one v j)

private theorem residueChar_mul_measure_le {Q : Set (Fin 3 → 𝔸)} (hQ : MeasurableSet Q) (v : HeightOneSpectrum (𝓞 ℚ))
    (j : Fin 3) (hstab : ∀ r : v.adicCompletion ℚ, Valued.v r ≤ 1 → ∀ x, x + shiftRow v j r ∈ Q ↔ x ∈ Q) :
    (residueChar v : ℝ≥0∞) * rowHaar (Q ∩ {x | Valued.v (rowAt v x j) < 1}) ≤ rowHaar Q := by
  have hDm : MeasurableSet (Q ∩ {x | Valued.v (rowAt v x j) < 1}) := hQ.inter (measurableSet_valued_rowAt_lt_one v j)
  let T : ℕ → Set (Fin 3 → 𝔸) := fun k =>
    (fun x => shiftRow v j (k : v.adicCompletion ℚ) + x) ⁻¹' (Q ∩ {x | Valued.v (rowAt v x j) < 1})
  have hTm : ∀ k, MeasurableSet (T k) := fun k => measurable_const_add _ hDm
  have hTμ : ∀ k, rowHaar (T k) = rowHaar (Q ∩ {x | Valued.v (rowAt v x j) < 1}) := fun k => measure_preimage_add _ _ _
  have hTQ : ∀ k, T k ⊆ Q := fun k x hx => by
    have hx' : shiftRow v j (k : v.adicCompletion ℚ) + x ∈ Q := hx.1
    rw [add_comm] at hx'
    exact (hstab _ (valued_natCast_le_one v k) x).mp hx'
  have hdisj : ∀ k l : ℕ, k < l → l < residueChar v → Disjoint (T k) (T l) := fun k l hkl hl => by
    refine Set.disjoint_left.mpr fun x hk hl' => ?_
    have h1 : Valued.v ((k : v.adicCompletion ℚ) + rowAt v x j) < 1 := by
      have h := hk.2
      rwa [Set.mem_setOf_eq, rowAt_shiftRow_add] at h
    have h2 : Valued.v ((l : v.adicCompletion ℚ) + rowAt v x j) < 1 := by
      have h := hl'.2
      rwa [Set.mem_setOf_eq, rowAt_shiftRow_add] at h
    have h3 : Valued.v ((l - k : ℕ) : v.adicCompletion ℚ) = 1 :=
      valued_natCast_eq_one (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hkl) (by omega))
    have h4 : ((l - k : ℕ) : v.adicCompletion ℚ) =
        ((l : v.adicCompletion ℚ) + rowAt v x j) - ((k : v.adicCompletion ℚ) + rowAt v x j) := by
      rw [Nat.cast_sub hkl.le]
      ring
    rw [h4] at h3
    have h5 := Valuation.map_sub_lt _ h2 h1
    rw [h3] at h5
    exact lt_irrefl _ h5
  have hunion : rowHaar (⋃ k ∈ Finset.range (residueChar v), T k) =
      (residueChar v : ℝ≥0∞) * rowHaar (Q ∩ {x | Valued.v (rowAt v x j) < 1}) := by
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

private theorem measure_badRows_le {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} (hW : ∀ j, IsOpen (W j)) {N : ℕ}
    (h2 : 2 ∣ N) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ residueChar v ∣ N) :
    rowHaar ((goodRows W N ∩ {x | Valued.v (rowAt v x 1) < 1}) ∩ {x | Valued.v (rowAt v x 0) < 1}) ≤
      rowHaar (goodRows W N) * tailTerm (residueChar v) := by
  have hrad : levelRadius N v = 1 := levelRadius_eq_one hv
  have hq0 : (residueChar v : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (residueChar_prime v).ne_zero
  have hqq0 : (residueChar v : ℝ≥0∞) * residueChar v ≠ 0 := mul_ne_zero hq0 hq0
  have hqqt : (residueChar v : ℝ≥0∞) * residueChar v ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)
  have hstep1 := residueChar_mul_measure_le (measurableSet_goodRows hW N) v 1 fun r hr x =>
    add_shiftRow_mem_goodRows_iff hrad 1 hr x
  have hstep0 := residueChar_mul_measure_le
    ((measurableSet_goodRows hW N).inter (measurableSet_valued_rowAt_lt_one v 1)) v 0 fun r hr x => by
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, add_shiftRow_mem_goodRows_iff hrad 0 hr x,
        rowAt_add_shiftRow_of_ne v 0 1 (by decide) r x]
  have hboth : (residueChar v : ℝ≥0∞) * residueChar v *
      rowHaar ((goodRows W N ∩ {x | Valued.v (rowAt v x 1) < 1}) ∩ {x | Valued.v (rowAt v x 0) < 1}) ≤
        rowHaar (goodRows W N) := by
    rw [mul_assoc]
    exact (mul_le_mul' le_rfl hstep0).trans hstep1
  rw [tailTerm_residueChar h2 hv, ← div_eq_mul_inv]
  rw [mul_comm] at hboth
  exact (ENNReal.le_div_iff_mul_le (Or.inl hqq0) (Or.inl hqqt)).mpr hboth

private theorem pos_rowHaar_inter_explicitRows (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {O : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ)} (hO : O ∈ nhds e₃) : 0 < rowHaar (O ∩ explicitRows S) := by
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
  have hQO : goodRows W M ⊆ O := fun x hx => hIt fun j _ =>
    hsub j (x j) ((mem_goodRows.mp hx).1 j).1 (finBox_antitone (hNM j) _ ((mem_goodRows.mp hx).1 j).2)
  refine lt_of_lt_of_le ?_ (measure_mono (Set.inter_subset_inter_left _ hQO))
  have hQpos : 0 < rowHaar (goodRows W M) := Measure.measure_pos_of_nonempty_interior (μ := rowHaar)
    ⟨e₃, mem_interior_iff_mem_nhds.mpr (goodRows_mem_nhds hWo hW₃ hM0)⟩
  have hQtop : rowHaar (goodRows W M) ≠ ⊤ := measure_goodRows_ne_top hK hWK M
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  let E : {v : HeightOneSpectrum (𝓞 ℚ) // ¬ residueChar v ∣ M} → Set (Fin 3 → 𝔸) := fun v =>
    (goodRows W M ∩ {x | Valued.v (rowAt v.1 x 1) < 1}) ∩ {x | Valued.v (rowAt v.1 x 0) < 1}
  have hcover : goodRows W M ⊆ (goodRows W M ∩ explicitRows S) ∪ ⋃ v, E v := by
    intro x hx
    by_cases hxS : x ∈ explicitRows S
    · exact Or.inl ⟨hx, hxS⟩
    · have hprim : ¬ ∀ v, v ∉ S → PrimitiveAt v x := fun h =>
        hxS (mem_explicitRows.mpr ⟨h, fun v hv => nonzeroAt_of_mem_goodRows hx (hSM v hv),
          nonzeroArch_of_rowArch ⟨2, (mem_goodRows.mp hx).2⟩⟩)
      simp only [not_forall] at hprim
      obtain ⟨v, -, hvbad⟩ := hprim
      have hvM : ¬ residueChar v ∣ M := fun hdvd => hvbad (primitiveAt_of_mem_goodRows hx hdvd)
      have hle := valued_rowAt_le_one_of_mem_goodRows hx v
      refine Or.inr (Set.mem_iUnion.mpr ⟨⟨v, hvM⟩, ⟨hx, ?_⟩, ?_⟩)
      · exact lt_of_le_of_ne (hle 1) fun h1 => hvbad ((primitiveAt_iff v x).mpr ⟨hle, 1, h1⟩)
      · exact lt_of_le_of_ne (hle 0) fun h1 => hvbad ((primitiveAt_iff v x).mpr ⟨hle, 0, h1⟩)
  have hE : ∀ v, rowHaar (E v) ≤ rowHaar (goodRows W M) * tailTerm (residueChar v.1) := fun v =>
    measure_badRows_le hWo h2M v.2
  have hinj : Function.Injective fun v : {v : HeightOneSpectrum (𝓞 ℚ) // ¬ residueChar v ∣ M} => residueChar v.1 :=
    residueChar_injective.comp Subtype.val_injective
  have hsum : ∑' v, rowHaar (E v) ≤ rowHaar (goodRows W M) * ENNReal.ofReal (2 / 3) :=
    calc ∑' v, rowHaar (E v)
      _ ≤ ∑' v : {v : HeightOneSpectrum (𝓞 ℚ) // ¬ residueChar v ∣ M},
            rowHaar (goodRows W M) * tailTerm (residueChar v.1) :=
          ENNReal.tsum_le_tsum hE
      _ = rowHaar (goodRows W M) *
            ∑' v : {v : HeightOneSpectrum (𝓞 ℚ) // ¬ residueChar v ∣ M}, tailTerm (residueChar v.1) :=
          ENNReal.tsum_mul_left
      _ ≤ rowHaar (goodRows W M) * ∑' i, tailTerm i :=
          mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hinj tailTerm)
      _ ≤ rowHaar (goodRows W M) * ENNReal.ofReal (2 / 3) := mul_le_mul' le_rfl tsum_tailTerm_le
  have hlt : rowHaar (goodRows W M) * ENNReal.ofReal (2 / 3) < rowHaar (goodRows W M) := by
    calc rowHaar (goodRows W M) * ENNReal.ofReal (2 / 3)
      _ = ENNReal.ofReal (2 / 3) * rowHaar (goodRows W M) := mul_comm _ _
      _ < 1 * rowHaar (goodRows W M) :=
          ENNReal.mul_lt_mul_left hQpos.ne' hQtop (ENNReal.ofReal_lt_one.mpr (by norm_num))
      _ = rowHaar (goodRows W M) := one_mul _
  refine lt_irrefl _ (hlt.trans_le ?_)
  calc rowHaar (goodRows W M) ≤ rowHaar ((goodRows W M ∩ explicitRows S) ∪ ⋃ v, E v) := measure_mono hcover
    _ ≤ rowHaar (goodRows W M ∩ explicitRows S) + rowHaar (⋃ v, E v) := measure_union_le _ _
    _ = rowHaar (⋃ v, E v) := by rw [h0, zero_add]
    _ ≤ ∑' v, rowHaar (E v) := measure_iUnion_le _
    _ ≤ rowHaar (goodRows W M) * ENNReal.ofReal (2 / 3) := hsum

end SectionHeads

end SectionAndRowSets

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

end Determination

private def archCoord : InfiniteAdeleRing ℚ → mixedEmbedding.mixedSpace ℚ :=
  InfiniteAdeleRing.ringEquiv_mixedSpace ℚ

private abbrev archBorel : MeasurableSpace (InfiniteAdeleRing ℚ) := borel _

attribute [local instance] archBorel

private theorem archBorelSpace : BorelSpace (InfiniteAdeleRing ℚ) := ⟨rfl⟩

attribute [local instance] archBorelSpace

private theorem archSecondCountable [∀ w : InfinitePlace ℚ, ProperSpace w.Completion] :
    SecondCountableTopology (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace ℚ) → w.Completion))

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

private abbrev localBorel (p : HeightOneSpectrum (𝓞 ℚ)) : MeasurableSpace (p.adicCompletion ℚ) := borel _

attribute [local instance] localBorel

private theorem localBorelSpace (p : HeightOneSpectrum (𝓞 ℚ)) : BorelSpace (p.adicCompletion ℚ) := ⟨rfl⟩

attribute [local instance] localBorelSpace

private def localCompactOpens (p : HeightOneSpectrum (𝓞 ℚ)) : Set (Set (p.adicCompletion ℚ)) :=
  {V | IsCompact V ∧ IsOpen V}

private theorem isCompact_localIntegers (p : HeightOneSpectrum (𝓞 ℚ))
    [CompactSpace (p.adicCompletionIntegers ℚ)] :
    IsCompact (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
  haveI : CompactSpace ((p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) :=
    inferInstanceAs (CompactSpace (p.adicCompletionIntegers ℚ))
  exact isCompact_iff_compactSpace.2 this

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
    ext i j
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

private abbrev Coords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Type :=
  (Fin 3 → InfiniteAdeleRing ℚ) × ∀ k : Fin 3 × {p // p ∈ S}, k.2.1.adicCompletion ℚ

private def coordsOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : Coords S :=
  (fun j => AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j), fun k => evalHom k.2.1 (x k.1))

private theorem continuous_coordsOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Continuous (coordsOf S) := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun k => ?_)
  · exact (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ).comp (continuous_apply j)
  · exact (continuous_evalHom k.2.1).comp (continuous_apply k.1)

private def rowOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : Coords S) : Fin 3 → AdeleRing (𝓞 ℚ) ℚ :=
  fun j => (y.1 j, ∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (y.2 (j, p)))

private theorem adeleArch_rowOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : Coords S) (j : Fin 3) :
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ (rowOf S y j) = y.1 j :=
  rfl

private theorem evalHom_rowOf_of_mem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : Coords S) (j : Fin 3)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ S) : evalHom p (rowOf S y j) = y.2 (j, ⟨p, hp⟩) := by
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p (∑ q ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ q.1 (y.2 (j, q))) = _
  rw [map_sum]
  simp only [AdelicLevel.finAdeleEval_apply]
  rw [Finset.sum_eq_single (⟨p, hp⟩ : {p // p ∈ S})]
  · exact StandardAddChar.finAdeleSingleAt_apply_self ℚ p _
  · intro q _ hq
    exact StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hq (Subtype.ext h.symm)
  · intro h
    exact absurd (Finset.mem_attach _ _) h

private theorem evalHom_rowOf_of_notMem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : Coords S) (j : Fin 3)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S) : evalHom p (rowOf S y j) = 0 := by
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p (∑ q ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ q.1 (y.2 (j, q))) = 0
  rw [map_sum]
  simp only [AdelicLevel.finAdeleEval_apply]
  exact Finset.sum_eq_zero fun q _ =>
    StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hp (by rw [h]; exact q.2)

private theorem continuous_rowOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Continuous (rowOf S) := by
  refine continuous_pi fun j => Continuous.prodMk ((continuous_apply j).comp continuous_fst) ?_
  exact continuous_finsetSum _ fun p _ =>
    (StandardAddChar.continuous_finAdeleSingleAt ℚ p.1).comp ((continuous_apply (j, p)).comp continuous_snd)

private theorem coordsOf_add_rowOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ)
    (t : Coords S) : coordsOf S (x + rowOf S t) = coordsOf S x + t := by
  refine Prod.ext (funext fun j => ?_) (funext fun k => ?_)
  · show AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j + rowOf S t j) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j) + t.1 j
    rw [map_add, adeleArch_rowOf]
  · show evalHom k.2.1 (x k.1 + rowOf S t k.1) = evalHom k.2.1 (x k.1) + t.2 k
    rw [map_add, evalHom_rowOf_of_mem S t k.1 k.2.2]

private theorem evalHom_add_rowOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ)
    (t : Coords S) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S) (j : Fin 3) :
    evalHom p ((x + rowOf S t) j) = evalHom p (x j) := by
  show evalHom p (x j + rowOf S t j) = evalHom p (x j)
  rw [map_add, evalHom_rowOf_of_notMem S t j hp, add_zero]

private def intOff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  {x | ∀ p, p ∉ S → ∀ j, evalHom p (x j) ∈ p.adicCompletionIntegers ℚ}

private theorem add_rowOf_mem_intOff_iff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ)
    (t : Coords S) : x + rowOf S t ∈ intOff S ↔ x ∈ intOff S :=
  forall₂_congr fun p hp => forall_congr' fun j => by rw [evalHom_add_rowOf S x t hp j]

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

private theorem measurable_coordsOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Measurable (coordsOf S) :=
  (continuous_coordsOf S).measurable

private theorem continuous_rowEval (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    Continuous fun x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ => evalHom p (x j) :=
  (continuous_evalHom p).comp (continuous_apply j)

private theorem measurableSet_rowEval_integral (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | evalHom p (x j) ∈ p.adicCompletionIntegers ℚ} := by
  have h : IsClosed {y : p.adicCompletion ℚ | Valued.v y ≤ 1} := by
    simpa using AdelicLevel.isClosed_setOf_valued_le p (1 : p.adicCompletion ℚ) one_ne_zero
  exact (h.preimage (continuous_rowEval p j)).measurableSet

private theorem measurableSet_intOff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : MeasurableSet (intOff S) := by
  have h : intOff S = ⋂ p, ⋂ (_ : p ∉ S), ⋂ j,
      {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | evalHom p (x j) ∈ p.adicCompletionIntegers ℚ} := by
    ext x
    simp only [intOff, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h]
  exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun j =>
    measurableSet_rowEval_integral p j

private theorem rowOf_add (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a b : Coords S) :
    rowOf S (a + b) = rowOf S a + rowOf S b := by
  funext j
  refine Prod.ext rfl ?_
  show (∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (a.2 (j, p) + b.2 (j, p))) =
    (∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (a.2 (j, p))) +
      ∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (b.2 (j, p))
  simp only [map_add, Finset.sum_add_distrib]

private theorem rowOf_zero (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : rowOf S 0 = 0 := by
  funext j
  refine Prod.ext rfl ?_
  show (∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 ((0 : Coords S).2 (j, p))) = 0
  simp only [Prod.snd_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero]

private theorem rowOf_neg_add (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a : Coords S) :
    rowOf S (-a) + rowOf S a = 0 := by
  rw [← rowOf_add, neg_add_cancel, rowOf_zero]

private def integralPillar : Set (AdeleRing (𝓞 ℚ) ℚ) :=
  ({0} : Set (InfiniteAdeleRing ℚ)) ×ˢ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ

private theorem isCompact_integralPillar : IsCompact integralPillar :=
  isCompact_singleton.prod (AdelicBox.isCompact_integralFiniteAdeles (K := ℚ))

open scoped Pointwise in

private theorem exists_isCompact_superset (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {K : Set (Coords S)}
    (hK : IsCompact K) :
    ∃ L : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ), IsCompact L ∧ coordsOf S ⁻¹' K ∩ intOff S ⊆ L := by
  refine ⟨(univ.pi fun _ : Fin 3 => integralPillar) + rowOf S '' K,
    (isCompact_univ_pi fun _ => isCompact_integralPillar).add (hK.image (continuous_rowOf S)), ?_⟩
  rintro x ⟨hxK, hxZ⟩
  have hw : x + rowOf S (-(coordsOf S x)) ∈ intOff S := (add_rowOf_mem_intOff_iff S x _).2 hxZ
  have hc : coordsOf S (x + rowOf S (-(coordsOf S x))) = 0 := by
    rw [coordsOf_add_rowOf, add_neg_cancel]
  refine Set.mem_add.2 ⟨x + rowOf S (-(coordsOf S x)), ?_, rowOf S (coordsOf S x), ⟨coordsOf S x, hxK, rfl⟩, ?_⟩
  · refine mem_univ_pi.2 fun j => ⟨?_, fun p => ?_⟩
    · exact congrFun (congrArg Prod.fst hc) j
    · by_cases hp : p ∈ S
      · have h0 : evalHom p ((x + rowOf S (-(coordsOf S x))) j) = 0 :=
          congrFun (congrArg Prod.snd hc) (j, ⟨p, hp⟩)
        show evalHom p ((x + rowOf S (-(coordsOf S x))) j) ∈ p.adicCompletionIntegers ℚ
        rw [h0]
        exact zero_mem _
      · exact hw p hp j
  · show x + rowOf S (-(coordsOf S x)) + rowOf S (coordsOf S x) = x
    rw [add_assoc, rowOf_neg_add, add_zero]

private def coordsHaar (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Measure (Coords S) :=
  Measure.addHaarMeasure (Classical.arbitrary _)

private theorem coordsHaar_isAddHaarMeasure (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    (coordsHaar S).IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_addHaarMeasure _

attribute [local instance] coordsHaar_isAddHaarMeasure

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

private def rowTest (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : ℂ :=
  ∏ i, testFactorC S (φ i) (fun v => V (i, v)) (x i)

private theorem rowTest_eq_ofReal (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    rowTest S φ V x = (((∏ i, testFactor S (φ i) (fun v => V (i, v)) (x i) : ℝ≥0) : ℝ) : ℂ) := by
  simp only [rowTest, testFactorC, NNReal.coe_prod, Complex.ofReal_prod]

private theorem rowTest_real (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    0 ≤ (rowTest S φ V x).re ∧ (rowTest S φ V x).im = 0 := by
  rw [rowTest_eq_ofReal, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨NNReal.coe_nonneg _, rfl⟩

private theorem nnnorm_rowTest (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    ‖rowTest S φ V x‖₊ = ∏ i, testFactor S (φ i) (fun v => V (i, v)) (x i) := by
  rw [rowTest_eq_ofReal, Complex.nnnorm_real, NNReal.nnnorm_eq]

private theorem re_rowTest (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    (rowTest S φ V x).re = ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ) := by
  rw [nnnorm_rowTest, rowTest_eq_ofReal, Complex.ofReal_re]

private theorem prod_ite_integral_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    (∏ i : Fin 3, (if ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → (x i).2 v ∈ v.adicCompletionIntegers ℚ then (1 : ℝ≥0)
      else 0)) = (intOff S).indicator (fun _ => (1 : ℝ≥0)) x := by
  by_cases hx : x ∈ intOff S
  · rw [indicator_of_mem hx]
    exact Finset.prod_eq_one fun i _ => if_pos fun v hv => hx v hv i
  · rw [indicator_of_notMem hx]
    have hnot : ¬ ∀ i : Fin 3, ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → (x i).2 v ∈ v.adicCompletionIntegers ℚ :=
      fun h => hx fun v hv i => h i v hv
    obtain ⟨i, hi⟩ := not_forall.1 hnot
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private theorem nnnorm_rowTest_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ≥0∞) =
      boxTest φ V (coordsOf S x) * (intOff S).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  have hNN : (∏ i, testFactor S (φ i) (fun v => V (i, v)) (x i)) =
      ((∏ i, φ i ((coordsOf S x).1 i)) *
        ∏ k, (V k).indicator (fun _ => (1 : ℝ≥0)) ((coordsOf S x).2 k)) *
          (intOff S).indicator (fun _ => (1 : ℝ≥0)) x := by
    rw [← prod_ite_integral_eq]
    simp only [testFactor, finPart, Finset.prod_mul_distrib, Fintype.prod_prod_type, mul_assoc]
    rfl
  rw [nnnorm_rowTest, hNN, ENNReal.coe_mul]
  unfold boxTest
  congr 1
  by_cases hx : x ∈ intOff S <;> simp [hx]

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

private def placeFun (w : InfinitePlace ℚ) (t : w.Completion) : InfiniteAdeleRing ℚ :=
  fun w' => cast (congrArg InfinitePlace.Completion (Subsingleton.elim w w')) t

private theorem placeFun_default (y : InfiniteAdeleRing ℚ) : placeFun default (y default) = y := by
  funext w'
  obtain rfl : (default : InfinitePlace ℚ) = w' := Subsingleton.elim _ _
  simp only [placeFun, cast_eq]

private def archFactorC (g : mixedEmbedding.mixedSpace ℚ → ℝ) (w : InfinitePlace ℚ) (t : w.Completion) : ℂ :=
  (g (archCoord (placeFun w t)) : ℂ)

private theorem prod_archFactorC (g : mixedEmbedding.mixedSpace ℚ → ℝ) (y : InfiniteAdeleRing ℚ) :
    (∏ w : InfinitePlace ℚ, archFactorC g w (y w)) = (g (archCoord y) : ℂ) := by
  rw [Fintype.prod_unique]
  simp only [archFactorC, placeFun_default]

private theorem exists_factorizable (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {φ : InfiniteAdeleRing ℚ → ℝ≥0}
    (hφ : φ ∈ smoothFamily archCoord) (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)) :
    ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (testFactorC S φ W) S g h := by
  obtain ⟨g, -, -, hg_nonneg, -, rfl⟩ := hφ
  refine ⟨archFactorC g, localFactorC S W, fun a => ?_⟩
  show (((Real.toNNReal (g (archCoord a.1)) * finPart S W a.2 : ℝ≥0) : ℝ) : ℂ) = _
  rw [NNReal.coe_mul, Complex.ofReal_mul, Real.coe_toNNReal _ (hg_nonneg _), finPart_eq_shape]
  by_cases hmem : a ∈ NumberField.TateGlobal.integralOutside (F := ℚ) S
  · have hc : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → a.2 v ∈ v.adicCompletionIntegers ℚ := hmem
    rw [if_pos hc, mul_one, Set.indicator_of_mem hmem, prod_archFactorC]
  · have hc : ¬ ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → a.2 v ∈ v.adicCompletionIntegers ℚ := hmem
    rw [if_neg hc, mul_zero, mul_zero, Set.indicator_of_notMem hmem]

private theorem rowTest_class (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0}
    (hφ : ∀ i, φ i ∈ smoothFamily archCoord) {V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)}
    (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    ∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
      (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
      rowTest S φ V = fun x => ∏ i, Φc i (x i) :=
  ⟨fun i => testFactorC S (φ i) (fun v => V (i, v)),
    fun i => testFactorC_mem_pureTensorSet S (hφ i) fun v => hV (i, v),
    fun i => exists_factorizable S (hφ i) _, rfl⟩

private theorem smoothFamily_exists_compact {φ : InfiniteAdeleRing ℚ → ℝ≥0} (hφ : φ ∈ smoothFamily archCoord) :
    ∃ K : Set (InfiniteAdeleRing ℚ), IsCompact K ∧ MeasurableSet K ∧ (∀ a, φ a ≤ 1) ∧ ∀ a, a ∉ K → φ a = 0 := by
  obtain ⟨g, -, hg_supp, -, hg_le, rfl⟩ := hφ
  refine ⟨archCoord ⁻¹' tsupport g, isCompact_preimage_archCoord continuous_archCoord hg_supp,
    ((isClosed_tsupport g).preimage continuous_archCoord).measurableSet, fun a => ?_, fun a ha => ?_⟩
  · exact Real.toNNReal_le_one.2 (hg_le _)
  · show Real.toNNReal (g (archCoord a)) = 0
    rw [image_eq_zero_of_notMem_tsupport ha, Real.toNNReal_zero]

private theorem measurable_boxTest_coords (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    {V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)} (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    Measurable (boxTest φ V) :=
  boxTest_measurable (fun i => smoothFamily_archCoord_measurable continuous_archCoord (hφ i))
    fun k => (hV k).2.measurableSet

private theorem exists_isCompact_rowTest_bound (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    {V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)} (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    ∃ L : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ), IsCompact L ∧
      ∀ x, ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ≥0∞) ≤ L.indicator (fun _ => (1 : ℝ≥0∞)) x := by
  choose K hKc hKm hφ₁ hφK using fun i => smoothFamily_exists_compact (hφ i)
  obtain ⟨L, hL, hsub⟩ :=
    exists_isCompact_superset S ((isCompact_univ_pi hKc).prod (isCompact_univ_pi fun k => (hV k).1))
  refine ⟨L, hL, fun x => ?_⟩
  rw [nnnorm_rowTest_eq]
  by_cases hx : x ∈ coordsOf S ⁻¹' ((univ.pi K) ×ˢ (univ.pi V)) ∩ intOff S
  · rw [indicator_of_mem (hsub hx)]
    calc boxTest φ V (coordsOf S x) * (intOff S).indicator (fun _ => (1 : ℝ≥0∞)) x
        ≤ ((univ.pi K) ×ˢ (univ.pi V)).indicator (fun _ => (1 : ℝ≥0∞)) (coordsOf S x) *
            (intOff S).indicator (fun _ => (1 : ℝ≥0∞)) x :=
          mul_le_mul_left (boxTest_le_indicator hφ₁ hφK V _) _
      _ ≤ 1 := by
          rw [indicator_of_mem (show coordsOf S x ∈ (univ.pi K) ×ˢ (univ.pi V) from hx.1), indicator_of_mem hx.2,
            mul_one]
  · rcases not_and_or.1 hx with hx1 | hx2
    · have h0 : boxTest φ V (coordsOf S x) = 0 :=
        le_antisymm ((boxTest_le_indicator hφ₁ hφK V _).trans_eq
          (indicator_of_notMem (show coordsOf S x ∉ (univ.pi K) ×ˢ (univ.pi V) from hx1) _)) zero_le
      rw [h0, zero_mul]
      exact zero_le
    · rw [indicator_of_notMem hx2, mul_zero]
      exact zero_le

private theorem integrable_re_rowTest (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    {V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)} (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    Integrable (fun x => (rowTest S φ V x).re) rowHaar := by
  obtain ⟨L, hL, hbound⟩ := exists_isCompact_rowTest_bound S hφ hV
  have hmeas : Measurable fun x => ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ≥0∞) := by
    simp only [nnnorm_rowTest_eq]
    exact ((measurable_boxTest_coords S hφ hV).comp (measurable_coordsOf S)).mul
      (measurable_const.indicator (measurableSet_intOff S))
  have hre : (fun x => (rowTest S φ V x).re) = fun x => ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ≥0∞).toReal := by
    funext x
    rw [re_rowTest, ENNReal.coe_toReal]
  rw [hre]
  refine Integrable.mono' ((integrableOn_const (C := (1 : ℝ)) hL.measure_lt_top.ne).integrable_indicator
    hL.measurableSet) hmeas.ennreal_toReal.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  by_cases hx : x ∈ L
  · rw [indicator_of_mem hx]
    have h := hbound x
    rw [indicator_of_mem hx] at h
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])
  · have h := hbound x
    rw [indicator_of_notMem hx] at h
    rw [indicator_of_notMem hx, nonpos_iff_eq_zero.1 h, ENNReal.toReal_zero]

private theorem sigmaFinite_coordsHaar (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : SigmaFinite (coordsHaar S) :=
  inferInstance

attribute [local instance] sigmaFinite_coordsHaar

end UniquenessHead

end UniquenessPrinciple

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

private theorem componentAt3_keptOutside_of_notMem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (h : AdelicGL 3 (𝓞 ℚ) ℚ)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S) : componentAt3 (𝓞 ℚ) ℚ p (keptOutside S h) = 1 := by
  rw [componentAt3_keptOutside, if_neg hp]

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

private def adeleAt (p : HeightOneSpectrum (𝓞 ℚ)) (t : p.adicCompletion ℚ) : AdeleRing (𝓞 ℚ) ℚ :=
  ((0, AdelicDock.splice (𝓞 ℚ) ℚ p 0 t) : AdeleRing (𝓞 ℚ) ℚ)

private theorem localToAdelic3_upperUnipotent3 (p : HeightOneSpectrum (𝓞 ℚ)) (x y z : p.adicCompletion ℚ) :
    localToAdelic3 p (upperUnipotent3 x y z) = upperUnipotent3 (adeleAt p x) (adeleAt p y) (adeleAt p z) := by
  apply Units.ext
  rw [coe_localToAdelic3, upperUnipotent3_coe, upperUnipotent3_coe]
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · rw [mapMatrix_arch_finMatN]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply, adeleAt] <;> rfl
  · rw [mapMatrix_fin_finMatN]
    refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    by_cases hw : w = p
    · subst hw
      rw [mapMatrix_localMatN_self]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
          adeleAt] <;> rfl
    · rw [mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ hw]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
          adeleAt, AdelicDock.splice_apply_of_ne (𝓞 ℚ) ℚ p _ _ hw] <;> rfl

private theorem localToAdelic3_upperUnipotent3_mem (p : HeightOneSpectrum (𝓞 ℚ)) (x y z : p.adicCompletion ℚ) :
    localToAdelic3 p (upperUnipotent3 x y z) ∈ WhittakerBlock.unipotentSubgroup3 := by
  rw [localToAdelic3_upperUnipotent3, WhittakerBlock.mem_unipotentSubgroup3_iff]
  exact ⟨_, _, _, rfl⟩

private def placedProduct (U : Finset (HeightOneSpectrum (𝓞 ℚ))) (u : ∀ p : HeightOneSpectrum (𝓞 ℚ), LocalGL3 p) :
    AdelicGL 3 (𝓞 ℚ) ℚ :=
  U.noncommProd (fun q => localToAdelic3 q (u q)) fun _ _ _ _ hab =>
    (commute_localToAdelic3 (componentAt3_localToAdelic3_of_ne hab _) _).symm

private theorem placedProduct_insert {U : Finset (HeightOneSpectrum (𝓞 ℚ))}
    (u : ∀ p : HeightOneSpectrum (𝓞 ℚ), LocalGL3 p) {a : HeightOneSpectrum (𝓞 ℚ)} (ha : a ∉ U) :
    placedProduct (insert a U) u = localToAdelic3 a (u a) * placedProduct U u := by
  unfold placedProduct
  rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]

private theorem componentAt3_placedProduct (U : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (u : ∀ p : HeightOneSpectrum (𝓞 ℚ), LocalGL3 p) (q : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ q (placedProduct U u) = if q ∈ U then u q else 1 := by
  refine Finset.induction_on U ?_ ?_
  · simp [placedProduct]
  · intro a U ha ih
    rw [placedProduct_insert u ha, map_mul, ih]
    by_cases hqa : q = a
    · subst hqa
      simp [componentAt3_localToAdelic3, ha]
    · simp [componentAt3_localToAdelic3_of_ne hqa, hqa]

private theorem placedProduct_mem_unipotent (U : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (u : ∀ p : HeightOneSpectrum (𝓞 ℚ), LocalGL3 p)
    (hu : ∀ p ∈ U, localToAdelic3 p (u p) ∈ WhittakerBlock.unipotentSubgroup3) :
    placedProduct U u ∈ WhittakerBlock.unipotentSubgroup3 :=
  Subgroup.noncommProd_mem _ _ hu

private abbrev standardPins : AutomorphicForm.CarrierPins ℚ :=
  productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)

private theorem exists_componentAt3_eq_one_and_whittaker3_ne_zero (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hGc : Continuous G)
    (hGinv : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) G)
    (hGaut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), G (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = G g)
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : ShellCond S g)
    (hW : whittaker3 standardPins NumberField.StandardAddChar.psiQ G g ≠ 0) :
    ∃ t : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
      whittaker3 standardPins NumberField.StandardAddChar.psiQ G t ≠ 0 := by
  classical
  choose! x y z k hkK hgk using hg

  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ p, p ∉ T →
      componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p :=
    ⟨(Filter.eventually_cofinite.1 (eventually_componentAt3_mem g)).toFinset, fun p hp => by
      by_contra h
      exact hp ((Set.Finite.mem_toFinset _).2 h)⟩
  set n := placedProduct (T \ S) fun p => upperUnipotent3 (x p) (y p) (z p) with hn_def
  have hn : n ∈ WhittakerBlock.unipotentSubgroup3 :=
    placedProduct_mem_unipotent _ _ fun p _ => localToAdelic3_upperUnipotent3_mem p _ _ _
  set h := n⁻¹ * g with hh_def
  have hhK : ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p h ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
    intro p hp
    rw [hh_def, map_mul, map_inv, hn_def, componentAt3_placedProduct]
    by_cases hpT : p ∈ T
    · rw [if_pos (Finset.mem_sdiff.2 ⟨hpT, hp⟩), hgk p hp, inv_mul_cancel_left]
      exact hkK p hp
    · rw [if_neg (fun hm => hpT (Finset.mem_sdiff.1 hm).1), inv_one, one_mul]
      exact hT p hpT
  have hWh : whittaker3 standardPins NumberField.StandardAddChar.psiQ G h ≠ 0 := by
    have hnorm := (whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul G hGaut).2 n hn h
    rw [hh_def, mul_inv_cancel_left] at hnorm
    intro h0
    apply hW
    rw [← norm_eq_zero, hnorm, h0, norm_zero]
  refine ⟨keptOutside S h, fun p hp => componentAt3_keptOutside_of_notMem S h hp, ?_⟩
  have htr := congrArg (fun F => whittaker3 standardPins NumberField.StandardAddChar.psiQ F 1)
    (translateRight_eq_translateRight_keptOutside S hhK hGc hGinv)
  simp only [whittaker3_translateRight, one_mul] at htr
  rwa [← htr]

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

private theorem exists_shellCond_and_whittaker3_ne_zero_of_block_ne_zero (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hb : WhittakerBlock.block pins ψ f Φ σ S ≠ 0) :
    ∃ g : AdelicGL 3 (𝓞 ℚ) ℚ, ShellCond S g ∧ whittaker3 pins ψ f g ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hb
  rw [block_eq_setLIntegral]
  refine (setLIntegral_congr_fun (measurableSet_zerothShell S) fun q hq => ?_).trans lintegral_zero
  have hq' : ShellCond S q.out := hq
  simp [integrand, hcon q.out hq']

end OffPlacesRepresentatives

section TestFunctionOfPositiveMass

open Filter Topology Set
open scoped NNReal Classical

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
attribute [local instance] NumberField.AdeleRing.secondCountableTopology

private theorem exists_archBalls_zero_one_mem :
    ∃ n : ℕ, (0 : InfiniteAdeleRing ℚ) ∈ archBalls n ∧ (1 : InfiniteAdeleRing ℚ) ∈ archBalls n := by
  have h0 : (0 : InfiniteAdeleRing ℚ) ∈ ⋃ n, archBalls n := by rw [archBalls_iUnion]; exact Set.mem_univ _
  have h1 : (1 : InfiniteAdeleRing ℚ) ∈ ⋃ n, archBalls n := by rw [archBalls_iUnion]; exact Set.mem_univ _
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp h0
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp h1
  exact ⟨max a b, archBalls_mono (le_max_left a b) ha, archBalls_mono (le_max_right a b) hb⟩

private theorem isOpen_archBalls (n : ℕ) : IsOpen (archBalls n) := by
  unfold archBalls
  exact Metric.isOpen_ball.preimage continuous_archCoord

private theorem exists_profile_one_le (n : ℕ) :
    ∃ φ ∈ smoothFamily archCoord, ∀ a ∈ archBalls n, (1 : ℝ≥0) ≤ φ a := by
  obtain ⟨Φ, hΦ, φ, -, hle, hlim⟩ := smoothFamily_approx archCoord (archBalls_mem n)
  refine ⟨Φ, hΦ, fun a ha => ?_⟩
  have h := hlim a
  rw [Set.indicator_of_mem ha] at h
  exact le_of_tendsto' h fun k => hle k a

private theorem e₃_fst_mem_archBalls {n : ℕ} (h0 : (0 : InfiniteAdeleRing ℚ) ∈ archBalls n)
    (h1 : (1 : InfiniteAdeleRing ℚ) ∈ archBalls n) (j : Fin 3) : (e₃ j).1 ∈ archBalls n := by
  by_cases hj : j = 2
  · rw [show e₃ j = 1 from by simp [e₃, hj]]
    exact h1
  · rw [show e₃ j = 0 from by simp [e₃, hj]]
    exact h0

private def integralSets (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (k : Fin 3 × {p // p ∈ S}) :
    Set (k.2.1.adicCompletion ℚ) :=
  (k.2.1.adicCompletionIntegers ℚ : Set (k.2.1.adicCompletion ℚ))

private theorem integralSets_mem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (k : Fin 3 × {p // p ∈ S}) :
    integralSets S k ∈ localCompactOpens k.2.1 :=
  ⟨isCompact_localIntegers k.2.1, Valued.isOpen_valuationSubring _⟩

private theorem finPart_integralSets_eq_one (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ goodRows W N)
    (j : Fin 3) : finPart S (fun v => integralSets S (j, v)) (x j).2 = 1 := by
  have hint : ∀ v : HeightOneSpectrum (𝓞 ℚ), (x j).2 v ∈ v.adicCompletionIntegers ℚ := fun v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (valued_rowAt_le_one_of_mem_goodRows hx v j)
  simp only [finPart]
  rw [if_pos fun v _ => hint v, mul_one]
  exact Finset.prod_eq_one fun v _ => Set.indicator_of_mem (SetLike.mem_coe.2 (hint v.1)) _

private theorem exists_testFunction_pos_mass (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) := by
  obtain ⟨n, h0, h1⟩ := exists_archBalls_zero_one_mem
  obtain ⟨φ₀, hφ₀, hge⟩ := exists_profile_one_le n
  have hφ : ∀ i : Fin 3, (fun _ : Fin 3 => φ₀) i ∈ smoothFamily archCoord := fun _ => hφ₀
  refine ⟨rowTest S (fun _ => φ₀) (integralSets S), rowTest_class S hφ (integralSets_mem S),
    rowTest_real S _ (integralSets S), ?_⟩
  show 0 < ∫ x, (rowTest S (fun _ => φ₀) (integralSets S) x).re ∂rowHaar
  rw [integral_pos_iff_support_of_nonneg (fun x => (rowTest_real S _ (integralSets S) x).1)
    (integrable_re_rowTest S hφ (integralSets_mem S))]
  refine (pos_rowHaar_inter_explicitRows ∅ (goodRows_mem_nhds (W := fun _ => archBalls n)
    (fun _ => isOpen_archBalls n) (e₃_fst_mem_archBalls h0 h1) one_ne_zero)).trans_le
    (measure_mono fun x hx => ?_)
  have hxg : x ∈ goodRows (fun _ => archBalls n) 1 := hx.1
  rw [Function.mem_support, rowTest_eq_ofReal, Complex.ofReal_re]
  norm_cast
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  have hj : (1 : ℝ≥0) ≤ φ₀ (x j).1 := hge _ ((mem_goodRows.mp hxg).1 j).1
  simp only [testFactor, finPart_integralSets_eq_one S hxg j, mul_one]
  exact (one_pos.trans_le hj).ne'

end TestFunctionOfPositiveMass

end Fibration
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

end RowFurniture
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

section Pairing

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

section CuspFunctionsClosure

open LanglandsTunnell.CubicInduction

private theorem integrable_of_continuous_of_isCompact_carrier {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    (hY : OpensMeasurableSpace Y) (ν : MeasureTheory.Measure Y) (hν : MeasureTheory.IsFiniteMeasure ν) {C : Set Y}
    (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C) (f : Y → ℂ) (hf : Continuous f) : MeasureTheory.Integrable f ν := by
  haveI := hY
  haveI := hν
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  exact MeasureTheory.Integrable.of_bound hf.aestronglyMeasurable M (hνC.mono fun y hy => hM y hy)

end CuspFunctionsClosure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

noncomputable section WhittakerLinear

open LanglandsTunnell.CubicInduction

private abbrev pins0 : AutomorphicForm.CarrierPins ℚ :=
  AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)

private theorem integral₃_add {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] (hY : OpensMeasurableSpace Y)
    (ν : MeasureTheory.Measure Y) (hν : MeasureTheory.IsFiniteMeasure ν) {C : Set Y} (hC : IsCompact C)
    (hνC : ∀ᵐ y ∂ν, y ∈ C) (u u' : Y → Y → Y → ℂ) (hu : Continuous fun t : (Y × Y) × Y => u t.1.1 t.1.2 t.2)
    (hu' : Continuous fun t : (Y × Y) × Y => u' t.1.1 t.1.2 t.2) :
    (∫ x, ∫ y, ∫ z, (u x y z + u' x y z) ∂ν ∂ν ∂ν) =
      (∫ x, ∫ y, ∫ z, u x y z ∂ν ∂ν ∂ν) + ∫ x, ∫ y, ∫ z, u' x y z ∂ν ∂ν ∂ν := by
  have hz : ∀ x y : Y, Continuous fun z : Y => ((x, y), z) := fun x y => continuous_const.prodMk continuous_id

  have h3 : ∀ x y : Y, (∫ z, (u x y z + u' x y z) ∂ν) = (∫ z, u x y z ∂ν) + ∫ z, u' x y z ∂ν := fun x y =>
    MeasureTheory.integral_add
      (integrable_of_continuous_of_isCompact_carrier hY ν hν hC hνC _ (hu.comp (hz x y)))
      (integrable_of_continuous_of_isCompact_carrier hY ν hν hC hνC _ (hu'.comp (hz x y)))

  have hI : Continuous fun p : Y × Y => ∫ z, u p.1 p.2 z ∂ν :=
    continuous_integral_of_isCompact_carrier hY ν hν hC hνC (fun p : Y × Y => fun z => u p.1 p.2 z) hu
  have hI' : Continuous fun p : Y × Y => ∫ z, u' p.1 p.2 z ∂ν :=
    continuous_integral_of_isCompact_carrier hY ν hν hC hνC (fun p : Y × Y => fun z => u' p.1 p.2 z) hu'

  have h2 : ∀ x : Y, (∫ y, ((∫ z, u x y z ∂ν) + ∫ z, u' x y z ∂ν) ∂ν) =
      (∫ y, ∫ z, u x y z ∂ν ∂ν) + ∫ y, ∫ z, u' x y z ∂ν ∂ν := fun x =>
    MeasureTheory.integral_add
      (integrable_of_continuous_of_isCompact_carrier hY ν hν hC hνC _
        (hI.comp (continuous_const.prodMk continuous_id : Continuous fun y : Y => (x, y))))
      (integrable_of_continuous_of_isCompact_carrier hY ν hν hC hνC _
        (hI'.comp (continuous_const.prodMk continuous_id : Continuous fun y : Y => (x, y))))

  have hJ : Continuous fun x : Y => ∫ y, ∫ z, u x y z ∂ν ∂ν :=
    continuous_integral_of_isCompact_carrier hY ν hν hC hνC (fun x y => ∫ z, u x y z ∂ν) hI
  have hJ' : Continuous fun x : Y => ∫ y, ∫ z, u' x y z ∂ν ∂ν :=
    continuous_integral_of_isCompact_carrier hY ν hν hC hνC (fun x y => ∫ z, u' x y z ∂ν) hI'
  calc (∫ x, ∫ y, ∫ z, (u x y z + u' x y z) ∂ν ∂ν ∂ν)
      = ∫ x, ∫ y, ((∫ z, u x y z ∂ν) + ∫ z, u' x y z ∂ν) ∂ν ∂ν := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => h3 x y)
    _ = ∫ x, ((∫ y, ∫ z, u x y z ∂ν ∂ν) + ∫ y, ∫ z, u' x y z ∂ν ∂ν) ∂ν :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h2)
    _ = (∫ x, ∫ y, ∫ z, u x y z ∂ν ∂ν ∂ν) + ∫ x, ∫ y, ∫ z, u' x y z ∂ν ∂ν ∂ν :=
        MeasureTheory.integral_add
          (integrable_of_continuous_of_isCompact_carrier hY ν hν hC hνC _ hJ)
          (integrable_of_continuous_of_isCompact_carrier hY ν hν hC hνC _ hJ')

private theorem continuous_whittaker3_integrand (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : Continuous F)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous fun t : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      F (upperUnipotent3 t.1.1 t.1.2 t.2 * g) * NumberField.StandardAddChar.psiQ (-(t.1.1 + t.1.2)) := by
  have hn := continuous_upperUnipotent3_triple (A := AdeleRing (𝓞 ℚ) ℚ)
  have hq : Continuous fun t : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ => (t.1.1, t.1.2, t.2) :=
    (continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hs : Continuous fun t : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ => -(t.1.1 + t.1.2) :=
    ((continuous_fst.comp continuous_fst).add (continuous_snd.comp continuous_fst)).neg
  exact (hF.comp ((hn.comp hq).mul continuous_const)).mul (NumberField.StandardAddChar.continuous_psiQ.comp hs)

private theorem whittaker3_add {F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : Continuous F) (hF' : Continuous F')
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins0 NumberField.StandardAddChar.psiQ (F + F') g =
      whittaker3 pins0 NumberField.StandardAddChar.psiQ F g +
        whittaker3 pins0 NumberField.StandardAddChar.psiQ F' g := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  have hY : OpensMeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) :=
    (NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ).opensMeasurable
  set ν : @MeasureTheory.Measure (AdeleRing (𝓞 ℚ) ℚ) (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ) := pins0.ν
  haveI : MeasureTheory.IsProbabilityMeasure ν := NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  have hν : MeasureTheory.IsFiniteMeasure ν := inferInstance
  obtain ⟨C, hC, hνC⟩ := exists_isCompact_ae_mem_productionPins_measure
  have key := integral₃_add hY ν hν hC hνC
    (fun x y z => F (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)))
    (fun x y z => F' (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)))
    (continuous_whittaker3_integrand F hF g) (continuous_whittaker3_integrand F' hF' g)
  simp only [whittaker3, Pi.add_apply, add_mul]
  exact key

private theorem whittaker3_smul (c : ℂ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins0 NumberField.StandardAddChar.psiQ (c • F) g =
      c * whittaker3 pins0 NumberField.StandardAddChar.psiQ F g := by
  simp only [whittaker3, Pi.smul_apply, smul_eq_mul, mul_assoc, MeasureTheory.integral_const_mul]

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

private theorem measurable_out_of_invariant [MeasurableSpace G] {u : G → ℂ} (hu : Measurable u)
    (hinv : ∀ n ∈ H, ∀ g, u (n * g) = u g) : Measurable fun q : MulAction.orbitRel.Quotient H G => u q.out := by
  rw [measurable_from_quotient]
  convert hu using 1
  funext g
  obtain ⟨n, hn, h⟩ := exists_mem_mul_eq_out H g
  simp only [Function.comp_apply]
  rw [← h, hinv n hn]

end Cosets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

private theorem conj_mul_mul_of_conj_mul_self (c u v : ℂ) (hc : (starRingEnd ℂ) c * c = 1) :
    (starRingEnd ℂ) (c * u) * (c * v) = (starRingEnd ℂ) u * v := by
  rw [map_mul]
  calc (starRingEnd ℂ) c * (starRingEnd ℂ) u * (c * v)
      = ((starRingEnd ℂ) c * c) * ((starRingEnd ℂ) u * v) := by ring
    _ = (starRingEnd ℂ) u * v := by rw [hc, one_mul]

private theorem pairing_unipotent_mul {F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g)
    (hF' : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F' (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F' g) :
    ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (starRingEnd ℂ) (whittaker3 pins0 NumberField.StandardAddChar.psiQ F (n * g)) *
          whittaker3 pins0 NumberField.StandardAddChar.psiQ F' (n * g) =
        (starRingEnd ℂ) (whittaker3 pins0 NumberField.StandardAddChar.psiQ F g) *
          whittaker3 pins0 NumberField.StandardAddChar.psiQ F' g := by
  intro n hn
  refine Subgroup.closure_induction (p := fun n _ => ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (starRingEnd ℂ) (whittaker3 pins0 NumberField.StandardAddChar.psiQ F (n * g)) *
          whittaker3 pins0 NumberField.StandardAddChar.psiQ F' (n * g) =
        (starRingEnd ℂ) (whittaker3 pins0 NumberField.StandardAddChar.psiQ F g) *
          whittaker3 pins0 NumberField.StandardAddChar.psiQ F' g)
    ?_ ?_ ?_ ?_ hn
  · rintro _ ⟨⟨x, y, z⟩, rfl⟩ g
    obtain ⟨h1, h2⟩ := whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul F hF
    obtain ⟨h1', -⟩ := whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul F' hF'
    have hmem : upperUnipotent3 x y z ∈ WhittakerBlock.unipotentSubgroup3 :=
      Subgroup.subset_closure ⟨⟨x, y, z⟩, rfl⟩
    rw [h1 x y z g, h1' x y z g]
    by_cases h0 : whittaker3 pins0 NumberField.StandardAddChar.psiQ F g = 0
    · rw [h0, mul_zero, map_zero, zero_mul, zero_mul]
    · refine conj_mul_mul_of_conj_mul_self _ _ _ ?_
      have hψ : (starRingEnd ℂ) (NumberField.StandardAddChar.psiQ (x + y)) *
          NumberField.StandardAddChar.psiQ (x + y) = 1 := by
        have hnorm := h2 _ hmem g
        rw [h1 x y z g, norm_mul] at hnorm
        have hn1 : ‖NumberField.StandardAddChar.psiQ (x + y)‖ = 1 := by
          have hpos : ‖whittaker3 pins0 NumberField.StandardAddChar.psiQ F g‖ ≠ 0 := norm_ne_zero_iff.2 h0
          refine mul_right_cancel₀ hpos ?_
          rw [one_mul]
          exact hnorm
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hn1]
        simp
      exact hψ
  · intro g
    simp only [one_mul]
  · intro m m' _ _ hm hm' g
    rw [mul_assoc, hm (m' * g), hm' g]
  · intro m _ hm g
    have := hm (m⁻¹ * g)
    rw [mul_inv_cancel_left] at this
    exact this.symm

end WhittakerLinear
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

section Constant

open LanglandsTunnell.CubicInduction

attribute [local instance] NumberField.AdelicHaar.adeleBorel

open scoped Classical in

private theorem continuous_of_mem_pureTensorSet {φ : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ AdelicFourier.pureTensorSet ℚ) :
    Continuous φ := by
  obtain ⟨g, h, hh, -, rfl⟩ := hφ
  exact (g.continuous.comp ((AdelicBox.continuous_ringEquiv_mixedSpace (K := ℚ)).comp continuous_fst)).mul
    (hh.continuous.comp continuous_snd)

private theorem continuous_prod_of_pureTensors {Φc : Fin 3 → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hΦc : ∀ i, Φc i ∈ AdelicFourier.pureTensorSet ℚ) :
    Continuous fun x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ => ∏ i, Φc i (x i) :=
  continuous_finsetProd _ fun i _ => (continuous_of_mem_pureTensorSet (hΦc i)).comp (continuous_apply i)

private def IsTest (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) : Prop :=
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))

private noncomputable abbrev μrow : Measure (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

private abbrev rowSet (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
    ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}

private noncomputable abbrev nsq (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (∫ g, F g * starRingEnd ℂ (F g) ∂(SlabL2.domainMeasure a b Φ₀)).re

private noncomputable abbrev mass (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) : ℝ≥0∞ := ENNReal.ofReal (∫ x, (Φ x).re ∂μrow)

private noncomputable abbrev fibreInt
    (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : ℝ≥0∞ :=
  ∫⁻ q, (((‖whittaker3 pins0 NumberField.StandardAddChar.psiQ
      (SlabL2.translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞)) ^ 2) ∂ν

section Tests

variable {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ}

private theorem test_continuous (hΦ : IsTest S Φ) :
    Continuous Φ := by
  obtain ⟨⟨Φc, hΦc, -, rfl⟩, -, -⟩ := hΦ
  exact continuous_prod_of_pureTensors hΦc

private theorem test_integral_pos (hΦ : IsTest S Φ) :
    0 < ∫ x, (Φ x).re ∂μrow := hΦ.2.2

private theorem test_re_integrable (hΦ : IsTest S Φ) :
    MeasureTheory.Integrable (fun x => (Φ x).re) μrow := by
  by_contra h
  have := test_integral_pos hΦ
  rw [MeasureTheory.integral_undef h] at this
  exact lt_irrefl _ this

private theorem test_apply_eq (hΦ : IsTest S Φ)
    (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : Φ x = ((Φ x).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [(hΦ.2.1 x).2]

private theorem test_nnnorm_eq (hΦ : IsTest S Φ)
    (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : ((‖Φ x‖₊ : ℝ≥0∞)) = ENNReal.ofReal (Φ x).re := by
  rw [← enorm_eq_nnnorm, ← ofReal_norm]
  show ENNReal.ofReal ‖Φ x‖ = _
  rw [test_apply_eq hΦ x, Complex.norm_real, Real.norm_of_nonneg (hΦ.2.1 x).1]
  simp

private theorem test_lintegral (hΦ : IsTest S Φ) :
    ∫⁻ x, ((‖Φ x‖₊ : ℝ≥0∞)) ∂μrow = mass Φ := by
  have h1 : ∫⁻ x, ((‖Φ x‖₊ : ℝ≥0∞)) ∂μrow = ∫⁻ x, ENNReal.ofReal (Φ x).re ∂μrow :=
    MeasureTheory.lintegral_congr fun x => test_nnnorm_eq hΦ x
  rw [h1, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (test_re_integrable hΦ)
    (Filter.Eventually.of_forall fun x => (hΦ.2.1 x).1)]

private theorem mass_ne_zero (hΦ : IsTest S Φ) :
    mass Φ ≠ 0 := (ENNReal.ofReal_pos.2 (test_integral_pos hΦ)).ne'

private theorem mass_ne_top : mass Φ ≠ ⊤ := ENNReal.ofReal_ne_top

private theorem test_integral_re (hΦ : IsTest S Φ) :
    (∫ x, Φ x ∂μrow).re = ∫ x, (Φ x).re ∂μrow := by
  have hint : MeasureTheory.Integrable Φ μrow := by
    have h := (test_re_integrable hΦ).ofReal (𝕜 := ℂ)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    exact (test_apply_eq hΦ x).symm
  simpa using (integral_re hint).symm

private theorem setLIntegral_test_ne_top (hΦ : IsTest S Φ) :
    ∫⁻ x in rowSet S, ((‖Φ x‖₊ : ℝ≥0∞)) ∂μrow ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [test_lintegral hΦ]; exact mass_ne_top) (MeasureTheory.setLIntegral_le_lintegral _ _)

private theorem test_nnnorm_measurable (hΦ : IsTest S Φ) :
    Measurable fun x => ((‖Φ x‖₊ : ℝ≥0∞)) := by
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ
  exact (test_continuous hΦ).measurable.nnnorm.coe_nnreal_ennreal

end Tests
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

private theorem block_mul_eq
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (adm : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → Prop) (V L : ℝ≥0∞)
    (ℓ : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ((Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) → ℝ≥0∞)
    (hF2 :
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      Filter.Tendsto
          (fun σ : ℝ => WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ σ S)
          (nhdsWithin 1 (Set.Ioi 1))
          (nhds (WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ 1 S)) ∧
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ 1 S * (V * L) = ℓ φ Φ)
    (κ : ℝ≥0∞)
    (hκ : ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm F →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        ℓ F Φ =
          κ * ENNReal.ofReal
            (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
              (∫ x, Φ x ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)).re) *
            ENNReal.ofReal (∫ g, F g * starRingEnd ℂ (F g) ∂(SlabL2.domainMeasure a b Φ₀)).re)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hFa : adm F) {Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ : IsTest S Φ) :
    WhittakerBlock.block pins0 NumberField.StandardAddChar.psiQ F Φ 1 S * (V * L) =
      κ * mass Φ * nsq a b Φ₀ F := by
  have h2 := (hF2 F hFa Φ hΦ).2
  have h3 := hκ F hFa Φ hΦ
  try simp only [] at h3
  rw [test_integral_re hΦ] at h3
  rw [h2, h3]

private theorem global_constants
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (adm : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → Prop) (V L : ℝ≥0∞)
    (ℓ : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ((Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) → ℝ≥0∞)
    (hℓ : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      ℓ φ Φ ≠ ⊤ ∧ (φ ≠ 0 → ℓ φ Φ ≠ 0))
    (hF2 :
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      Filter.Tendsto
          (fun σ : ℝ => WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ σ S)
          (nhdsWithin 1 (Set.Ioi 1))
          (nhds (WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ 1 S)) ∧
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ 1 S * (V * L) = ℓ φ Φ)
    (κ : ℝ≥0∞)
    (hκ : ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm F →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        ℓ F Φ =
          κ * ENNReal.ofReal
            (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
              (∫ x, Φ x ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)).re) *
            ENNReal.ofReal (∫ g, F g * starRingEnd ℂ (F g) ∂(SlabL2.domainMeasure a b Φ₀)).re)
    (F₀ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF₀a : adm F₀) (hF₀ : F₀ ≠ 0) {Φ₁ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ}
    (hΦ₁ : IsTest S Φ₁) :
    V * L ≠ 0 ∧ V * L ≠ ⊤ ∧ κ ≠ 0 ∧ κ ≠ ⊤ ∧ nsq a b Φ₀ F₀ ≠ 0 := by
  obtain ⟨hne_top, hne_zero⟩ := hℓ F₀ hF₀a Φ₁ hΦ₁
  have hℓ0 := hne_zero hF₀
  have hb := (hF2 F₀ hF₀a Φ₁ hΦ₁).2
  have hk := block_mul_eq ω _hω a b Φ₀ _hΦ₀ S adm V L ℓ hF2 κ hκ F₀ hF₀a hΦ₁

  rw [← hb] at hne_top hℓ0
  rw [hk] at hne_top hℓ0
  have hκ0 : κ ≠ 0 := fun h => hℓ0 (by rw [h, zero_mul, zero_mul])
  have hN0 : nsq a b Φ₀ F₀ ≠ 0 := fun h => hℓ0 (by rw [h, mul_zero])
  have hm0 : mass Φ₁ ≠ 0 := mass_ne_zero hΦ₁
  have hκtop : κ ≠ ⊤ := fun h => hne_top (by rw [h, ENNReal.top_mul hm0, ENNReal.top_mul hN0])
  have hblock0 : WhittakerBlock.block pins0 NumberField.StandardAddChar.psiQ F₀ Φ₁ 1 S ≠ 0 := by
    intro h
    apply hℓ0
    rw [← hk, h, zero_mul]
  have hVL0 : V * L ≠ 0 := by
    intro h
    apply hℓ0
    rw [← hk, h, mul_zero]
  have hVLtop : V * L ≠ ⊤ := by
    intro h
    apply hne_top
    rw [← hk, h, ENNReal.mul_top hblock0]
  exact ⟨hVL0, hVLtop, hκ0, hκtop, hN0⟩

private theorem unique_premise
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (adm : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → Prop) (V L : ℝ≥0∞)
    (ℓ : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ((Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) → ℝ≥0∞)
    (hF2 :
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      Filter.Tendsto
          (fun σ : ℝ => WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ σ S)
          (nhdsWithin 1 (Set.Ioi 1))
          (nhds (WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ 1 S)) ∧
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ 1 S * (V * L) = ℓ φ Φ)
    (κ : ℝ≥0∞)
    (hκ : ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm F →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        ℓ F Φ =
          κ * ENNReal.ofReal
            (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
              (∫ x, Φ x ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)).re) *
            ENNReal.ofReal (∫ g, F g * starRingEnd ℂ (F g) ∂(SlabL2.domainMeasure a b Φ₀)).re)
    (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hfib : ∀ F ∈ cuspFunctions ω a b Φ₀, ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F Φ 1 S =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
            ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (hVL : V * L ≠ 0) (hVL' : V * L ≠ ⊤) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hFc : F ∈ cuspFunctions ω a b Φ₀) (hFa : adm F)
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (hΦ : IsTest S Φ) :
    ∫⁻ x in rowSet S, ((‖Φ x‖₊ : ℝ≥0∞)) * fibreInt P ν s F x ∂μrow =
      κ * nsq a b Φ₀ F / (V * L) * ∫⁻ x, ((‖Φ x‖₊ : ℝ≥0∞)) ∂μrow := by
  have h := hfib F hFc Φ hΦ
  simp only [] at h
  rw [← h, test_lintegral hΦ]
  have hk := block_mul_eq ω _hω a b Φ₀ _hΦ₀ S adm V L ℓ hF2 κ hκ F hFa hΦ
  calc WhittakerBlock.block pins0 NumberField.StandardAddChar.psiQ F Φ 1 S
      = κ * mass Φ * nsq a b Φ₀ F / (V * L) := by
        exact (ENNReal.eq_div_iff hVL hVL').2 (by rw [mul_comm]; exact hk)
    _ = κ * nsq a b Φ₀ F / (V * L) * mass Φ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring

private theorem fibre_ae_const
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (adm : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → Prop) (V L : ℝ≥0∞)
    (ℓ : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ((Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) → ℝ≥0∞)
    (hF2 :
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      Filter.Tendsto
          (fun σ : ℝ => WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ σ S)
          (nhdsWithin 1 (Set.Ioi 1))
          (nhds (WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ 1 S)) ∧
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ 1 S * (V * L) = ℓ φ Φ)
    (κ : ℝ≥0∞)
    (hκ : ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm F →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        ℓ F Φ =
          κ * ENNReal.ofReal
            (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
              (∫ x, Φ x ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)).re) *
            ENNReal.ofReal (∫ g, F g * starRingEnd ℂ (F g) ∂(SlabL2.domainMeasure a b Φ₀)).re)
    (hinv : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) φ))
    (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hfib : ∀ F ∈ cuspFunctions ω a b Φ₀, ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F Φ 1 S =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
            ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (hunique : ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F) → ∀ C : ℝ≥0∞, C ≠ ⊤ →
      (∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
            C * ∫⁻ x, (‖Φ x‖₊ : ℝ≥0∞)
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) →
      ∃ C₁ : ℝ≥0∞,
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
              {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
              ∂ν = C₁))
    (hVL : V * L ≠ 0) (hVL' : V * L ≠ ⊤) (hκtop : κ ≠ ⊤)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hFc : F ∈ cuspFunctions ω a b Φ₀)
    (hFa : adm F) :
    ∃ C₁ : ℝ≥0∞, ∀ᵐ x ∂(μrow.restrict (rowSet S)), fibreInt P ν s F x = C₁ := by
  obtain ⟨C₁, hC₁⟩ := hunique F hFc.2.1 hFc.1.1 (hinv F hFa) (κ * nsq a b Φ₀ F / (V * L))
    (ENNReal.div_ne_top (ENNReal.mul_ne_top hκtop ENNReal.ofReal_ne_top) hVL) fun Φ hΦ =>
      unique_premise ω _hω a b Φ₀ _hΦ₀ S adm V L ℓ hF2 κ hκ P ν s hfib hVL hVL' F hFc hFa Φ hΦ
  refine ⟨C₁, ?_⟩
  simpa only [] using hC₁

private theorem fibre_const_mul
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (adm : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → Prop) (V L : ℝ≥0∞)
    (ℓ : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ((Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) → ℝ≥0∞)
    (hF2 :
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      Filter.Tendsto
          (fun σ : ℝ => WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ σ S)
          (nhdsWithin 1 (Set.Ioi 1))
          (nhds (WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ 1 S)) ∧
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ 1 S * (V * L) = ℓ φ Φ)
    (κ : ℝ≥0∞)
    (hκ : ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm F →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        ℓ F Φ =
          κ * ENNReal.ofReal
            (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
              (∫ x, Φ x ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)).re) *
            ENNReal.ofReal (∫ g, F g * starRingEnd ℂ (F g) ∂(SlabL2.domainMeasure a b Φ₀)).re)
    (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hfib : ∀ F ∈ cuspFunctions ω a b Φ₀, ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F Φ 1 S =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
            ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (hVL : V * L ≠ 0) (hVL' : V * L ≠ ⊤) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hFc : F ∈ cuspFunctions ω a b Φ₀) (hFa : adm F)
    {Φ₁ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ₁ : IsTest S Φ₁) {C₁ : ℝ≥0∞}
    (hC₁ : ∀ᵐ x ∂(μrow.restrict (rowSet S)), fibreInt P ν s F x = C₁) :
    C₁ * ∫⁻ x in rowSet S, ((‖Φ₁ x‖₊ : ℝ≥0∞)) ∂μrow = κ * nsq a b Φ₀ F / (V * L) * mass Φ₁ := by
  have hp := unique_premise ω _hω a b Φ₀ _hΦ₀ S adm V L ℓ hF2 κ hκ P ν s hfib hVL hVL' F hFc hFa Φ₁ hΦ₁
  rw [test_lintegral hΦ₁] at hp
  rw [← hp, mul_comm]
  rw [← MeasureTheory.lintegral_mul_const C₁ (test_nnnorm_measurable hΦ₁)]
  exact MeasureTheory.lintegral_congr_ae (hC₁.mono fun x hx => by beta_reduce; rw [hx])

private theorem exists_fibre_constant
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (adm : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → Prop) (V L : ℝ≥0∞)
    (ℓ : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ((Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) → ℝ≥0∞)
    (hℓ : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      ℓ φ Φ ≠ ⊤ ∧ (φ ≠ 0 → ℓ φ Φ ≠ 0))
    (hF2 :
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      Filter.Tendsto
          (fun σ : ℝ => WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ σ S)
          (nhdsWithin 1 (Set.Ioi 1))
          (nhds (WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ 1 S)) ∧
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ Φ 1 S * (V * L) = ℓ φ Φ)
    (κ : ℝ≥0∞)
    (hκ : ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm F →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        ℓ F Φ =
          κ * ENNReal.ofReal
            (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
              (∫ x, Φ x ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)).re) *
            ENNReal.ofReal (∫ g, F g * starRingEnd ℂ (F g) ∂(SlabL2.domainMeasure a b Φ₀)).re)
    (hclass : ∃ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (hinv : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) φ))
    (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hfib : ∀ F ∈ cuspFunctions ω a b Φ₀, ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F Φ 1 S =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
            ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (hunique : ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F) → ∀ C : ℝ≥0∞, C ≠ ⊤ →
      (∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
            C * ∫⁻ x, (‖Φ x‖₊ : ℝ≥0∞)
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) →
      ∃ C₁ : ℝ≥0∞,
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
              {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
              ∂ν = C₁))
    (F₀ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF₀c : F₀ ∈ cuspFunctions ω a b Φ₀) (hF₀a : adm F₀) (hF₀ : F₀ ≠ 0) :
    ∃ c₀ : ℝ≥0∞, c₀ ≠ 0 ∧ c₀ ≠ ⊤ ∧
      ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, F ∈ cuspFunctions ω a b Φ₀ → adm F →
        ∀ᵐ x ∂(μrow.restrict (rowSet S)), fibreInt P ν s F x = c₀ * nsq a b Φ₀ F := by
  obtain ⟨Φ₁, hΦ₁⟩ := hclass
  have hΦ₁' : IsTest S Φ₁ := hΦ₁
  obtain ⟨hVL, hVL', hκ0, hκtop, hN₀⟩ := global_constants ω _hω a b Φ₀ _hΦ₀ S adm V L ℓ hℓ hF2 κ hκ F₀ hF₀a hF₀ hΦ₁'
  set J : ℝ≥0∞ := ∫⁻ x in rowSet S, ((‖Φ₁ x‖₊ : ℝ≥0∞)) ∂μrow with hJ
  have hJtop : J ≠ ⊤ := setLIntegral_test_ne_top hΦ₁'
  have hJ0 : J ≠ 0 := by
    obtain ⟨C₀, hC₀⟩ :=
      fibre_ae_const ω _hω a b Φ₀ _hΦ₀ S adm V L ℓ hF2 κ hκ hinv P ν s hfib hunique hVL hVL' hκtop F₀ hF₀c hF₀a
    have h := fibre_const_mul ω _hω a b Φ₀ _hΦ₀ S adm V L ℓ hF2 κ hκ P ν s hfib hVL hVL' F₀ hF₀c hF₀a hΦ₁' hC₀
    intro hJ0
    rw [← hJ, hJ0, mul_zero] at h
    have hq : κ * nsq a b Φ₀ F₀ / (V * L) ≠ 0 := by
      rw [ne_eq, ENNReal.div_eq_zero_iff, not_or]
      exact ⟨mul_ne_zero hκ0 hN₀, hVL'⟩
    exact mul_ne_zero hq (mass_ne_zero hΦ₁') h.symm
  refine ⟨κ * mass Φ₁ / (V * L * J), ?_, ?_, ?_⟩
  · rw [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨mul_ne_zero hκ0 (mass_ne_zero hΦ₁'), ENNReal.mul_ne_top hVL' hJtop⟩
  · exact ENNReal.div_ne_top (ENNReal.mul_ne_top hκtop (mass_ne_top)) (mul_ne_zero hVL hJ0)
  · intro F hFc hFa
    obtain ⟨C₁, hC₁⟩ :=
      fibre_ae_const ω _hω a b Φ₀ _hΦ₀ S adm V L ℓ hF2 κ hκ hinv P ν s hfib hunique hVL hVL' hκtop F hFc hFa
    have h := fibre_const_mul ω _hω a b Φ₀ _hΦ₀ S adm V L ℓ hF2 κ hκ P ν s hfib hVL hVL' F hFc hFa hΦ₁' hC₁
    rw [← hJ] at h
    have hC : C₁ = κ * mass Φ₁ / (V * L * J) * nsq a b Φ₀ F := by
      rw [mul_comm] at h
      have h' := (ENNReal.eq_div_iff hJ0 hJtop).2 h
      rw [h', div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl hVL) (Or.inl hVL')]
      ring
    exact hC₁.mono fun x hx => by rw [hx, hC]

end Constant
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

section SquareIntegralIdentities

open LanglandsTunnell.CubicInduction

private abbrev IsAut (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g

private abbrev Orb (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) : Type :=
  MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P

private noncomputable abbrev Wq {P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)} (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (q : Orb P) : ℂ :=
  whittaker3 pins0 NumberField.StandardAddChar.psiQ F (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)

private theorem translateRight_aut {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : IsAut F) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    IsAut (SlabL2.translateRight h F) := by
  intro γ g
  simp only [SlabL2.translateRight, mul_assoc, hF]

private theorem continuous_translateRight {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : Continuous F) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous (SlabL2.translateRight h F) :=
  hF.comp (continuous_mul_const h)

private theorem measurable_pairing_out (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) {F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hFaut : IsAut F) (hF'aut : IsAut F') (hFc : Continuous F) (hF'c : Continuous F') :
    Measurable fun q : Orb P => (starRingEnd ℂ) (Wq F q) * Wq F' q := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  have hW : Continuous (whittaker3 pins0 NumberField.StandardAddChar.psiQ F) :=
    continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ F hFc
  have hW' : Continuous (whittaker3 pins0 NumberField.StandardAddChar.psiQ F') :=
    continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ F' hF'c
  have hu : Measurable fun p : ↥P =>
      (starRingEnd ℂ) (whittaker3 pins0 NumberField.StandardAddChar.psiQ F (p : AdelicGL 3 (𝓞 ℚ) ℚ)) *
        whittaker3 pins0 NumberField.StandardAddChar.psiQ F' (p : AdelicGL 3 (𝓞 ℚ) ℚ) :=
    ((Complex.continuous_conj.comp (hW.comp continuous_subtype_val)).mul
      (hW'.comp continuous_subtype_val)).measurable
  refine measurable_out_of_invariant hu ?_
  intro n hn p
  exact pairing_unipotent_mul hFaut hF'aut (n : AdelicGL 3 (𝓞 ℚ) ℚ)
    (Subgroup.mem_subgroupOf.1 hn) (p : AdelicGL 3 (𝓞 ℚ) ℚ)

private theorem integral_selfPairing_eq (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) (ν : Measure (Orb P))
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hFaut : IsAut F) (hFc : Continuous F) :
    ∫ q, (starRingEnd ℂ) (Wq F q) * Wq F q ∂ν =
      (((∫⁻ q, (((‖Wq F q‖₊ : ℝ≥0∞)) ^ 2) ∂ν).toReal : ℝ) : ℂ) := by
  have hm := measurable_pairing_out P hFaut hFaut hFc hFc
  have h1 : ∀ q : Orb P, (starRingEnd ℂ) (Wq F q) * Wq F q = ((‖Wq F q‖ ^ 2 : ℝ) : ℂ) :=
    fun q => by
    rw [Complex.conj_mul', Complex.ofReal_pow]
  have hmr : Measurable fun q : Orb P => ‖Wq F q‖ ^ 2 := by
    have hre : (fun q : Orb P => ‖Wq F q‖ ^ 2) =
        fun q => ((starRingEnd ℂ) (Wq F q) * Wq F q).re := by
      funext q
      rw [h1 q, Complex.ofReal_re]
    rw [hre]
    exact Complex.measurable_re.comp hm
  have hl : ∫⁻ q, ENNReal.ofReal (‖Wq F q‖ ^ 2) ∂ν = ∫⁻ q, (((‖Wq F q‖₊ : ℝ≥0∞)) ^ 2) ∂ν := by
    refine MeasureTheory.lintegral_congr fun q => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  calc ∫ q, (starRingEnd ℂ) (Wq F q) * Wq F q ∂ν
      = ∫ q, ((‖Wq F q‖ ^ 2 : ℝ) : ℂ) ∂ν :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ((∫ q, ‖Wq F q‖ ^ 2 ∂ν : ℝ) : ℂ) := integral_ofReal
    _ = _ := by
        rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => sq_nonneg _)
          hmr.aestronglyMeasurable, hl]

private theorem nsq_eq_norm_sq (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) :
    nsq a b Φ₀ F = ENNReal.ofReal (‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖ ^ 2) := by
  have hinner : ⟪toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2 ω a b Φ₀ ⟨F, hF.1⟩⟫_ℂ =
      ∫ g, F g * (starRingEnd ℂ) (F g) ∂(SlabL2.domainMeasure a b Φ₀) := by
    rw [MeasureTheory.L2.inner_def]
    have hae := (hF.1.2.2 : MeasureTheory.MemLp F 2 (SlabL2.domainMeasure a b Φ₀)).coeFn_toLp
    refine MeasureTheory.integral_congr_ae (hae.mono fun g hg => ?_)
    have hg' : ((toL2 ω a b Φ₀ ⟨F, hF.1⟩ : Carrier a b Φ₀) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g = F g := hg
    beta_reduce
    rw [hg', RCLike.inner_apply]
  show ENNReal.ofReal (∫ g, F g * (starRingEnd ℂ) (F g) ∂(SlabL2.domainMeasure a b Φ₀)).re = _
  rw [← hinner]
  congr 1
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (toL2 ω a b Φ₀ ⟨F, hF.1⟩)

end SquareIntegralIdentities
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

section GenericPairing

open MeasureTheory Filter Topology

open scoped InnerProductSpace ENNReal NNReal

namespace ConjProducts

private theorem enorm_eq_coe_nnnorm' (a : ℂ) : ‖a‖ₑ = (‖a‖₊ : ℝ≥0∞) := rfl

private theorem coe_nnnorm_conj_mul_self (a : ℂ) :
    ((‖(starRingEnd ℂ) a * a‖₊ : ℝ≥0∞)) = ((‖a‖₊ : ℝ≥0∞) ^ 2) := by
  have hc : ‖(starRingEnd ℂ) a‖₊ = ‖a‖₊ := NNReal.eq (RCLike.norm_conj a)
  rw [nnnorm_mul, hc, sq, ENNReal.coe_mul]

private theorem integrable_conj_mul_self {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {f : Y → ℂ}
    (hf : AEStronglyMeasurable (fun y : Y => (starRingEnd ℂ) (f y) * f y) ν)
    (hfin : ∫⁻ y, ((‖f y‖₊ : ℝ≥0∞) ^ 2) ∂ν < ⊤) :
    Integrable (fun y : Y => (starRingEnd ℂ) (f y) * f y) ν := by
  refine ⟨hf, ?_⟩
  show ∫⁻ y, ‖(starRingEnd ℂ) (f y) * f y‖ₑ ∂ν < ⊤
  have h : (∫⁻ y, ‖(starRingEnd ℂ) (f y) * f y‖ₑ ∂ν) = ∫⁻ y, ((‖f y‖₊ : ℝ≥0∞) ^ 2) ∂ν :=
    lintegral_congr fun y => by rw [enorm_eq_coe_nnnorm', coe_nnnorm_conj_mul_self]
  rw [h]
  exact hfin

private theorem integral_conj_mul_eq_polarization {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {W : Type*} [AddCommGroup W] [Module ℂ W] (A : W →ₗ[ℂ] (Y → ℂ))
    (hint : ∀ z : W, Integrable (fun y : Y => (starRingEnd ℂ) (A z y) * A z y) ν) (x x' : W) :
    ∫ y, (starRingEnd ℂ) (A x y) * A x' y ∂ν =
      ((∫ y, (starRingEnd ℂ) (A (x + x') y) * A (x + x') y ∂ν) -
          (∫ y, (starRingEnd ℂ) (A (x - x') y) * A (x - x') y ∂ν) +
        ((∫ y, (starRingEnd ℂ) (A (x - Complex.I • x') y) * A (x - Complex.I • x') y ∂ν) -
            (∫ y, (starRingEnd ℂ) (A (x + Complex.I • x') y) * A (x + Complex.I • x') y ∂ν)) * Complex.I) / 4 := by
  have hpt : ∀ y : Y, (starRingEnd ℂ) (A x y) * A x' y =
      ((starRingEnd ℂ) (A (x + x') y) * A (x + x') y - (starRingEnd ℂ) (A (x - x') y) * A (x - x') y +
        ((starRingEnd ℂ) (A (x - Complex.I • x') y) * A (x - Complex.I • x') y -
          (starRingEnd ℂ) (A (x + Complex.I • x') y) * A (x + Complex.I • x') y) * Complex.I) / 4 := by
    intro y
    simp only [map_add, map_sub, map_smul, map_mul, Complex.conj_I, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    linear_combination ((starRingEnd ℂ) (A x y) * A x' y - (starRingEnd ℂ) (A x' y) * A x y) / 2 * Complex.I_sq
  simp_rw [hpt]
  set P₁ : Y → ℂ := fun y => (starRingEnd ℂ) (A (x + x') y) * A (x + x') y with hP₁
  set P₂ : Y → ℂ := fun y => (starRingEnd ℂ) (A (x - x') y) * A (x - x') y with hP₂
  set P₃ : Y → ℂ := fun y => (starRingEnd ℂ) (A (x - Complex.I • x') y) * A (x - Complex.I • x') y with hP₃
  set P₄ : Y → ℂ := fun y => (starRingEnd ℂ) (A (x + Complex.I • x') y) * A (x + Complex.I • x') y with hP₄
  have h₁ : Integrable P₁ ν := hint _
  have h₂ : Integrable P₂ ν := hint _
  have h₃ : Integrable P₃ ν := hint _
  have h₄ : Integrable P₄ ν := hint _
  have e1 : ∫ y, (P₁ y - P₂ y + (P₃ y - P₄ y) * Complex.I) / 4 ∂ν =
      (∫ y, (P₁ y - P₂ y + (P₃ y - P₄ y) * Complex.I) ∂ν) / 4 := integral_div _ _
  have e2 : ∫ y, (P₁ y - P₂ y + (P₃ y - P₄ y) * Complex.I) ∂ν =
      (∫ y, (P₁ y - P₂ y) ∂ν) + ∫ y, (P₃ y - P₄ y) * Complex.I ∂ν :=
    integral_add (h₁.sub' h₂) ((h₃.sub' h₄).mul_const _)
  have e3 : ∫ y, (P₁ y - P₂ y) ∂ν = (∫ y, P₁ y ∂ν) - ∫ y, P₂ y ∂ν := integral_sub h₁ h₂
  have e4 : ∫ y, (P₃ y - P₄ y) * Complex.I ∂ν = (∫ y, (P₃ y - P₄ y) ∂ν) * Complex.I := integral_mul_const _ _
  have e5 : ∫ y, (P₃ y - P₄ y) ∂ν = (∫ y, P₃ y ∂ν) - ∫ y, P₄ y ∂ν := integral_sub h₃ h₄
  show ∫ y, (P₁ y - P₂ y + (P₃ y - P₄ y) * Complex.I) / 4 ∂ν =
    ((∫ y, P₁ y ∂ν) - (∫ y, P₂ y ∂ν) + ((∫ y, P₃ y ∂ν) - (∫ y, P₄ y ∂ν)) * Complex.I) / 4
  rw [e1, e2, e3, e4, e5]

end ConjProducts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

end GenericPairing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

private theorem conj_mul_combination {Y : Type*} (f f' : Y → ℂ) (u v : ℂ) :
    (fun y => (starRingEnd ℂ) (u * f y + v * f' y) * (u * f y + v * f' y)) =
      fun y => (starRingEnd ℂ) u * u * ((starRingEnd ℂ) (f y) * f y) +
        ((starRingEnd ℂ) u * v * ((starRingEnd ℂ) (f y) * f' y) +
          ((starRingEnd ℂ) v * u * ((starRingEnd ℂ) (f' y) * f y) +
            (starRingEnd ℂ) v * v * ((starRingEnd ℂ) (f' y) * f' y))) := by
  funext y
  simp only [map_add, map_mul]
  ring

private theorem ofReal_div_mul_eq (A v B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ENNReal.ofReal (A / v * B) = ENNReal.ofReal (1 / v) * ENNReal.ofReal A * ENNReal.ofReal B := by
  rw [show A / v * B = 1 / v * (A * B) by ring]
  rcases le_or_gt 0 (1 / v) with hv | hv
  · rw [ENNReal.ofReal_mul hv, ENNReal.ofReal_mul hA, mul_assoc]
  · have h1 : 1 / v * (A * B) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv.le (mul_nonneg hA hB)
    rw [ENNReal.ofReal_of_nonpos h1, ENNReal.ofReal_of_nonpos hv.le, zero_mul, zero_mul]

section CrossPairing

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}

private theorem integrable_conj_mul_of_self {f f' : Y → ℂ}
    (hff : Integrable (fun y => (starRingEnd ℂ) (f y) * f y) ν)
    (hf'f' : Integrable (fun y => (starRingEnd ℂ) (f' y) * f' y) ν)
    (hm : AEStronglyMeasurable (fun y => (starRingEnd ℂ) (f y) * f' y) ν) :
    Integrable (fun y => (starRingEnd ℂ) (f y) * f' y) ν := by
  refine Integrable.mono' (hff.norm.add hf'f'.norm) hm (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, norm_mul, Complex.norm_conj]
  nlinarith [two_mul_le_add_sq ‖f y‖ ‖f' y‖, norm_nonneg (f y), norm_nonneg (f' y)]

private theorem integrable_conj_mul_self_combination {f f' : Y → ℂ}
    (hff : Integrable (fun y => (starRingEnd ℂ) (f y) * f y) ν)
    (hf'f' : Integrable (fun y => (starRingEnd ℂ) (f' y) * f' y) ν)
    (hff' : AEStronglyMeasurable (fun y => (starRingEnd ℂ) (f y) * f' y) ν)
    (hf'f : AEStronglyMeasurable (fun y => (starRingEnd ℂ) (f' y) * f y) ν) (u v : ℂ) :
    Integrable (fun y => (starRingEnd ℂ) (u * f y + v * f' y) * (u * f y + v * f' y)) ν := by
  rw [conj_mul_combination]
  exact (hff.const_mul _).add (((integrable_conj_mul_of_self hff hf'f' hff').const_mul _).add
    (((integrable_conj_mul_of_self hf'f' hff hf'f).const_mul _).add (hf'f'.const_mul _)))

end CrossPairing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

section Combination

open scoped InnerProductSpace

variable {Y : Type*}

private def pairMap (f f' : Y → ℂ) : (ℂ × ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun w := fun y => w.1 * f y + w.2 * f' y
  map_add' w w' := by
    funext y
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' r w := by
    funext y
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
    ring

private theorem pairMap_apply (f f' : Y → ℂ) (w : ℂ × ℂ) (y : Y) :
    pairMap f f' w y = w.1 * f y + w.2 * f' y := rfl

variable [MeasurableSpace Y] {ν : Measure Y}

private theorem integral_conj_mul_eq_of_self_pairings {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {f f' : Y → ℂ} (e e' : H) (c : ℝ)
    (hff : Integrable (fun y => (starRingEnd ℂ) (f y) * f y) ν)
    (hf'f' : Integrable (fun y => (starRingEnd ℂ) (f' y) * f' y) ν)
    (hff' : AEStronglyMeasurable (fun y => (starRingEnd ℂ) (f y) * f' y) ν)
    (hf'f : AEStronglyMeasurable (fun y => (starRingEnd ℂ) (f' y) * f y) ν)
    (hself : ∀ z : ℂ, z = 1 ∨ z = -1 ∨ z = -Complex.I ∨ z = Complex.I →
      ∫ y, (starRingEnd ℂ) (f y + z * f' y) * (f y + z * f' y) ∂ν = ((c * ‖e + z • e'‖ ^ 2 : ℝ) : ℂ)) :
    ∫ y, (starRingEnd ℂ) (f y) * f' y ∂ν = c * ⟪e, e'⟫_ℂ := by
  have hint : ∀ w : ℂ × ℂ, Integrable (fun y => (starRingEnd ℂ) (pairMap f f' w y) * pairMap f f' w y) ν :=
    fun w => integrable_conj_mul_self_combination hff hf'f' hff' hf'f w.1 w.2
  have h := ConjProducts.integral_conj_mul_eq_polarization (pairMap f f') hint (1, 0) (0, 1)
  have hl : (fun y => (starRingEnd ℂ) (pairMap f f' (1, 0) y) * pairMap f f' (0, 1) y) =
      fun y => (starRingEnd ℂ) (f y) * f' y := by
    funext y
    simp [pairMap_apply]
  have hc : ∀ z : ℂ, (fun y => (starRingEnd ℂ) (pairMap f f' (1, z) y) * pairMap f f' (1, z) y) =
      fun y => (starRingEnd ℂ) (f y + z * f' y) * (f y + z * f' y) := by
    intro z
    funext y
    simp [pairMap_apply]
  have e₁ : ((1 : ℂ), (0 : ℂ)) + (0, 1) = (1, 1) := by ext <;> simp
  have e₂ : ((1 : ℂ), (0 : ℂ)) - (0, 1) = (1, -1) := by ext <;> simp
  have e₃ : ((1 : ℂ), (0 : ℂ)) - Complex.I • ((0 : ℂ), (1 : ℂ)) = (1, -Complex.I) := by ext <;> simp
  have e₄ : ((1 : ℂ), (0 : ℂ)) + Complex.I • ((0 : ℂ), (1 : ℂ)) = (1, Complex.I) := by ext <;> simp
  rw [e₁, e₂, e₃, e₄, hl, hc, hc, hc, hc, hself 1 (Or.inl rfl), hself (-1) (Or.inr (Or.inl rfl)),
    hself (-Complex.I) (Or.inr (Or.inr (Or.inl rfl))), hself Complex.I (Or.inr (Or.inr (Or.inr rfl)))] at h
  rw [h, inner_eq_sum_norm_sq_div_four]
  simp only [one_smul, neg_smul, sub_eq_add_neg, RCLike.I_to_complex, RCLike.ofReal_eq_complex_ofReal]
  push_cast
  ring

end Combination
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

section PairingAtRows

open LanglandsTunnell.CubicInduction

private theorem wq_translate_combination {P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)} {F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : Continuous F) (hF' : Continuous F') (z : ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (q : Orb P) :
    Wq (translateRight g fun y => F y + z * F' y) q =
      Wq (translateRight g F) q + z * Wq (translateRight g F') q := by
  have h : (translateRight g fun y => F y + z * F' y) = translateRight g F + z • translateRight g F' := by
    funext y
    simp only [translateRight_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Wq]
  rw [h, whittaker3_add (F' := z • translateRight g F') (continuous_translateRight hF g)
    ((continuous_translateRight hF' g).const_smul z), whittaker3_smul]

private theorem lintegral_sq_translate_eq (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) (ν : Measure (Orb P))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ) {c₀ : ℝ≥0∞} (hc₀top : c₀ ≠ ⊤)
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hG : G ∈ cuspFunctions ω a b Φ₀) {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ}
    (hx : fibreInt P ν s G x = c₀ * nsq a b Φ₀ G) :
    ∫⁻ q, (((‖Wq (translateRight (s x) G) q‖₊ : ℝ≥0∞)) ^ 2) ∂ν =
      ENNReal.ofReal (c₀.toReal * ‖toL2 ω a b Φ₀ ⟨G, hG.1⟩‖ ^ 2) := by
  have h : fibreInt P ν s G x = c₀ * nsq a b Φ₀ G := hx
  rw [nsq_eq_norm_sq ω a b Φ₀ hG] at h
  refine h.trans ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc₀top]

private theorem integral_selfPairing_translate_eq (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) (ν : Measure (Orb P))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ) {c₀ : ℝ≥0∞} (hc₀top : c₀ ≠ ⊤)
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hGaut : IsAut G) (hGc : Continuous G) (hG : G ∈ cuspFunctions ω a b Φ₀)
    {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : fibreInt P ν s G x = c₀ * nsq a b Φ₀ G) :
    ∫ q, (starRingEnd ℂ) (Wq (translateRight (s x) G) q) * Wq (translateRight (s x) G) q ∂ν =
      ((c₀.toReal * ‖toL2 ω a b Φ₀ ⟨G, hG.1⟩‖ ^ 2 : ℝ) : ℂ) := by
  rw [integral_selfPairing_eq P ν (translateRight_aut hGaut (s x)) (continuous_translateRight hGc (s x)),
    lintegral_sq_translate_eq ω a b Φ₀ P ν s hc₀top hG hx, ENNReal.toReal_ofReal (by positivity)]

private theorem integrable_selfPairing_translate (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) (ν : Measure (Orb P))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ) {c₀ : ℝ≥0∞} (hc₀top : c₀ ≠ ⊤)
    {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hGaut : IsAut G) (hGc : Continuous G) (hG : G ∈ cuspFunctions ω a b Φ₀)
    {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : fibreInt P ν s G x = c₀ * nsq a b Φ₀ G) :
    Integrable (fun q => (starRingEnd ℂ) (Wq (translateRight (s x) G) q) * Wq (translateRight (s x) G) q) ν := by
  refine ConjProducts.integrable_conj_mul_self ?_ ?_
  · exact (measurable_pairing_out P (translateRight_aut hGaut (s x)) (translateRight_aut hGaut (s x))
      (continuous_translateRight hGc (s x)) (continuous_translateRight hGc (s x))).aestronglyMeasurable
  · rw [lintegral_sq_translate_eq ω a b Φ₀ P ν s hc₀top hG hx]
    exact ENNReal.ofReal_lt_top

end PairingAtRows
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

private theorem integral_conj_whittaker3_mul_eq_mul_inner_of_adm
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (adm : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → Prop)
    (hadm : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      Continuous φ ∧
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * φ g) ∧
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) φ) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen1 p)) φ (lam1 p)) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen2 p)) φ (lam2 p)))
    (hcusp : ∀ φ, adm φ → φ ∈ cuspFunctions ω a b Φ₀)
    (V L : ℝ≥0∞) (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (ℓ : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ((Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) → ℝ≥0∞)
    (hℓ : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      ℓ φ Φ ≠ ⊤ ∧ (φ ≠ 0 → ℓ φ Φ ≠ 0))
    (hℓeq : ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ),
          ℓ φ Φ =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
          ENNReal.ofReal
            ((∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) /
                (3 * ((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
                  (Set.univ.pi fun _ : Fin 3 => NumberField.AdelicBox.adelicBox ℚ)).toReal) *
              ∫ g, ‖φ g‖ ^ 2 ∂(domainMeasure a b Φ₀))))
    (hF2 :
        ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
        ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
          (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
            (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
            Φ = fun x => ∏ i, Φc i (x i)) ∧
          (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
           0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        Filter.Tendsto
            (fun σ : ℝ => WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ Φ σ S)
            (nhdsWithin 1 (Set.Ioi 1))
            (nhds (WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ Φ 1 S)) ∧
          WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ Φ 1 S * (V * L) = ℓ φ Φ)
    (hclass : ∃ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hfib : ∀ F ∈ cuspFunctions ω a b Φ₀, ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F Φ 1 S =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
            ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (hs1 : Filter.Tendsto s (nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)) (nhds 1))
    (hdense : ∀ O ∈ nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0),
      (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
        0 < (Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
              (O ∩ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j})))
    (hunique : ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F) → ∀ C : ℝ≥0∞, C ≠ ⊤ →
      (∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
            C * ∫⁻ x, (‖Φ x‖₊ : ℝ≥0∞)
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) →
      ∃ C₁ : ℝ≥0∞,
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
              {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
              ∂ν = C₁)) :
    ∃ c : ℝ, 0 < c ∧
      (∀ (F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), adm F → adm F' → (∀ z : ℂ, adm (fun x => F x + z * F' x)) →
        ∀ (hF : F ∈ cuspFunctions ω a b Φ₀) (hF' : F' ∈ cuspFunctions ω a b Φ₀),
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
              {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
            ∫ q, (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)) *
                whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (translateRight (s x) F') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν =
                c * ⟪toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ)) ∧
      (∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm F → ∀ hF : F ∈ cuspFunctions ω a b Φ₀,
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
              {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
              ∂ν = ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖ ^ 2))) := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ

  have _ := @hL0
  have _ := @hLtop
  have _ := @hs1
  have _ := @hdense

  have hκ : ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm F → ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ, IsTest S Φ →
      ℓ F Φ = ENNReal.ofReal (1 / (3 * ((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
            (Set.univ.pi fun _ : Fin 3 => NumberField.AdelicBox.adelicBox ℚ)).toReal)) *
          ENNReal.ofReal (∫ x, Φ x ∂μrow).re *
          ENNReal.ofReal (∫ g, F g * (starRingEnd ℂ) (F g) ∂(domainMeasure a b Φ₀)).re := by
    intro F _ Φ hΦ
    have hΦre : (∫ x, Φ x ∂μrow).re = ∫ x, (Φ x).re ∂μrow := test_integral_re hΦ
    have hFre : (∫ g, F g * (starRingEnd ℂ) (F g) ∂(domainMeasure a b Φ₀)).re =
        ∫ g, ‖F g‖ ^ 2 ∂(domainMeasure a b Φ₀) := by
      have hpt : ∀ g, F g * (starRingEnd ℂ) (F g) = ((‖F g‖ ^ 2 : ℝ) : ℂ) := fun g => by
        rw [Complex.mul_conj']
        norm_cast
      simp_rw [hpt]
      rw [integral_complex_ofReal, Complex.ofReal_re]
    rw [hℓeq F Φ, hΦre, hFre]
    exact ofReal_div_mul_eq _ _ _ (test_integral_pos hΦ).le (integral_nonneg fun g => sq_nonneg _)
  have hinv : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) φ) :=
    fun φ hφ => (hadm φ hφ).2.2.2.1
  by_cases hex : ∃ F₀ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm F₀ ∧ F₀ ≠ 0
  · obtain ⟨F₀, hF₀a, hF₀⟩ := hex
    obtain ⟨c₀, hc₀0, hc₀top, hfc⟩ :=
      exists_fibre_constant ω hω a b Φ₀ hΦ₀ S adm V L ℓ hℓ hF2 _ hκ hclass hinv P ν s hfib hunique F₀
        (hcusp F₀ hF₀a) hF₀a hF₀
    refine ⟨c₀.toReal, ENNReal.toReal_pos hc₀0 hc₀top, ?_, ?_⟩
    · intro F F' hFa hF'a hz hF hF'
      have hzc : ∀ z : ℂ, ∀ᵐ x ∂(μrow.restrict (rowSet S)),
          fibreInt P ν s (fun y => F y + z * F' y) x = c₀ * nsq a b Φ₀ (fun y => F y + z * F' y) :=
        fun z => hfc _ (hcusp _ (hz z)) (hz z)
      filter_upwards [hfc F (hcusp F hFa) hFa, hfc F' (hcusp F' hF'a) hF'a, hzc 1, hzc (-1), hzc (-Complex.I),
        hzc Complex.I] with x hxF hxF' hx₁ hx₂ hx₃ hx₄
      have hFc : Continuous F := (hadm F hFa).1
      have hF'c : Continuous F' := (hadm F' hF'a).1
      have hFaut : IsAut F := (hadm F hFa).2.1
      have hF'aut : IsAut F' := (hadm F' hF'a).2.1
      refine integral_conj_mul_eq_of_self_pairings (f := fun q => Wq (translateRight (s x) F) q)
        (f' := fun q => Wq (translateRight (s x) F') q) (toL2 ω a b Φ₀ ⟨F, hF.1⟩) (toL2 ω a b Φ₀ ⟨F', hF'.1⟩)
        c₀.toReal (integrable_selfPairing_translate ω a b Φ₀ P ν s hc₀top hFaut hFc hF hxF)
        (integrable_selfPairing_translate ω a b Φ₀ P ν s hc₀top hF'aut hF'c hF' hxF')
        (measurable_pairing_out P (translateRight_aut hFaut (s x)) (translateRight_aut hF'aut (s x))
          (continuous_translateRight hFc (s x)) (continuous_translateRight hF'c (s x))).aestronglyMeasurable
        (measurable_pairing_out P (translateRight_aut hF'aut (s x)) (translateRight_aut hFaut (s x))
          (continuous_translateRight hF'c (s x)) (continuous_translateRight hFc (s x))).aestronglyMeasurable ?_
      intro z hzz

      have hcomb : ∀ (hx : fibreInt P ν s (fun y => F y + z * F' y) x = c₀ * nsq a b Φ₀ (fun y => F y + z * F' y)),
          ∫ q, (starRingEnd ℂ) (Wq (translateRight (s x) F) q + z * Wq (translateRight (s x) F') q) *
              (Wq (translateRight (s x) F) q + z * Wq (translateRight (s x) F') q) ∂ν =
            ((c₀.toReal * ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩ + z • toL2 ω a b Φ₀ ⟨F', hF'.1⟩‖ ^ 2 : ℝ) : ℂ) := by
        intro hx
        have hGa : adm fun y => F y + z * F' y := hz z
        have hG : (fun y => F y + z * F' y) ∈ cuspFunctions ω a b Φ₀ := hcusp _ hGa
        have hsub : (⟨fun y => F y + z * F' y, hG.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) =
            ⟨F, hF.1⟩ + z • ⟨F', hF'.1⟩ := by
          apply Subtype.ext
          funext y
          simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h := integral_selfPairing_translate_eq ω a b Φ₀ P ν s hc₀top (hadm _ hGa).2.1 (hadm _ hGa).1 hG hx
        simp only [wq_translate_combination hFc hF'c z (s x)] at h
        rw [h, hsub, map_add, map_smul]
      rcases hzz with rfl | rfl | rfl | rfl
      · exact hcomb hx₁
      · exact hcomb hx₂
      · exact hcomb hx₃
      · exact hcomb hx₄
    · intro F hFa hF
      filter_upwards [hfc F (hcusp F hFa) hFa] with x hx
      exact lintegral_sq_translate_eq ω a b Φ₀ P ν s hc₀top hF hx
  ·
    push Not at hex
    have hW0 : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        whittaker3 pins0 NumberField.StandardAddChar.psiQ (translateRight g (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) h = 0 := by
      intro g h
      have h0 : translateRight g (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = (0 : ℂ) • (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
        funext y
        simp only [translateRight_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, mul_zero]
      rw [h0, whittaker3_smul, zero_mul]
    refine ⟨1, one_pos, ?_, ?_⟩
    · intro F F' hFa hF'a _ hF hF'
      obtain rfl : F = 0 := hex F hFa
      obtain rfl : F' = 0 := hex F' hF'a
      refine Filter.Eventually.of_forall fun x => ?_
      have h0 : (⟨(0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), hF.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = 0 := rfl
      simp only [hW0, map_zero, mul_zero, integral_zero, h0, inner_zero_left]
    · intro F hFa hF
      obtain rfl : F = 0 := hex F hFa
      refine Filter.Eventually.of_forall fun x => ?_
      have h0 : (⟨(0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), hF.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = 0 := rfl
      simp only [hW0, nnnorm_zero, ENNReal.coe_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        lintegral_zero, h0, map_zero, norm_zero, mul_zero, ENNReal.ofReal_zero]

end Pairing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

section PairingLimit

noncomputable section WhittakerLinear

open LanglandsTunnell.CubicInduction

private theorem whittaker3_translateRight (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins0 NumberField.StandardAddChar.psiQ (SlabL2.translateRight h F) g =
      whittaker3 pins0 NumberField.StandardAddChar.psiQ F (g * h) := by
  simp only [whittaker3, SlabL2.translateRight, mul_assoc]

section Cosets

variable {G : Type} [Group G] (H : Subgroup G)

variable {H}

end Cosets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

end WhittakerLinear
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

section SquareIntegralIdentities

open LanglandsTunnell.CubicInduction

end SquareIntegralIdentities
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

section Sequence

open LanglandsTunnell.CubicInduction

private theorem exists_seq_tendsto_of_forall_pos {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) (e : X) (R : Set X) (hR : ∀ O ∈ nhds e, 0 < μ (O ∩ R)) {p : X → Prop}
    (hp : ∀ᵐ x ∂(μ.restrict R), p x) :
    ∃ x : ℕ → X, (∀ n, x n ∈ R ∧ p (x n)) ∧ Filter.Tendsto x Filter.atTop (nhds e) := by
  obtain ⟨O, hO⟩ := (nhds e).exists_antitone_basis
  have hnull : μ ({x | ¬ p x} ∩ R) = 0 :=
    le_antisymm ((MeasureTheory.Measure.le_restrict_apply R _).trans (MeasureTheory.ae_iff.1 hp).le) zero_le
  have hex : ∀ n : ℕ, ∃ x, x ∈ O n ∧ x ∈ R ∧ p x := by
    intro n
    by_contra hcon
    push Not at hcon
    have hsub : O n ∩ R ⊆ {x | ¬ p x} ∩ R := fun x hx => ⟨hcon x hx.1 hx.2, hx.2⟩
    have hpos := hR (O n) (hO.mem n)
    exact hpos.ne' (le_antisymm ((MeasureTheory.measure_mono hsub).trans hnull.le) zero_le)
  choose x hxO hxR hxp using hex
  exact ⟨x, fun n => ⟨hxR n, hxp n⟩, hO.tendsto hxO⟩

private noncomputable abbrev e₃row : Fin 3 → AdeleRing (𝓞 ℚ) ℚ :=
  fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0

end Sequence
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

noncomputable section PairingLimitGeneric

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace PairingLimit

private theorem enorm_eq_coe_nnnorm' (a : ℂ) : ‖a‖ₑ = (‖a‖₊ : ℝ≥0∞) := rfl

private theorem aemeasurable_coe_nnnorm_of_conj_mul {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {f : Y → ℂ}
    (hf : AEStronglyMeasurable (fun y : Y => (starRingEnd ℂ) (f y) * f y) ν) :
    AEMeasurable (fun y : Y => (‖f y‖₊ : ℝ≥0∞)) ν := by
  have hn : AEMeasurable (fun y : Y => ‖f y‖) ν := by
    have h := Real.continuous_sqrt.measurable.comp_aemeasurable hf.norm.aemeasurable
    refine h.congr (Eventually.of_forall fun y => ?_)
    show Real.sqrt ‖(starRingEnd ℂ) (f y) * f y‖ = ‖f y‖
    rw [norm_mul, RCLike.norm_conj, Real.sqrt_mul_self (norm_nonneg _)]
  have h := hn.ennreal_ofReal
  refine h.congr (Eventually.of_forall fun y => ?_)
  show ENNReal.ofReal ‖f y‖ = (‖f y‖₊ : ℝ≥0∞)
  rw [ofReal_norm, enorm_eq_coe_nnnorm']

private theorem lintegral_sq_le_of_tendsto_ae {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (f : ℕ → Y → ℂ) (F : Y → ℂ) (hf : ∀ n : ℕ, AEMeasurable (fun y : Y => ((‖f n y‖₊ : ℝ≥0∞) ^ 2)) ν) (B : ℝ≥0∞)
    (hB : ∀ n : ℕ, ∫⁻ y, ((‖f n y‖₊ : ℝ≥0∞) ^ 2) ∂ν ≤ B)
    (hlim : ∀ᵐ y ∂ν, Tendsto (fun n : ℕ => f n y) atTop (𝓝 (F y))) :
    ∫⁻ y, ((‖F y‖₊ : ℝ≥0∞) ^ 2) ∂ν ≤ B := by
  have h1 : ∫⁻ y, ((‖F y‖₊ : ℝ≥0∞) ^ 2) ∂ν = ∫⁻ y, liminf (fun n : ℕ => ((‖f n y‖₊ : ℝ≥0∞) ^ 2)) atTop ∂ν := by
    refine lintegral_congr_ae (hlim.mono fun y hy => ?_)
    have ht : Tendsto (fun n : ℕ => ((‖f n y‖₊ : ℝ≥0∞) ^ 2)) atTop (𝓝 ((‖F y‖₊ : ℝ≥0∞) ^ 2)) :=
      ENNReal.Tendsto.pow ((ENNReal.continuous_coe.tendsto _).comp hy.nnnorm)
    exact ht.liminf_eq.symm
  rw [h1]
  calc ∫⁻ y, liminf (fun n : ℕ => ((‖f n y‖₊ : ℝ≥0∞) ^ 2)) atTop ∂ν
      ≤ liminf (fun n : ℕ => ∫⁻ y, ((‖f n y‖₊ : ℝ≥0∞) ^ 2) ∂ν) atTop := lintegral_liminf_le' fun n => hf n
    _ ≤ B := liminf_le_of_frequently_le' (Frequently.of_forall hB)

private theorem rpow_lintegral_sq_le {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {u v : Y → ℂ}
    (hd : AEMeasurable (fun y : Y => (‖u y - v y‖₊ : ℝ≥0∞)) ν) (hv : AEMeasurable (fun y : Y => (‖v y‖₊ : ℝ≥0∞)) ν) :
    (∫⁻ y, ((‖u y‖₊ : ℝ≥0∞) ^ 2) ∂ν) ^ (((2 : ℕ) : ℝ)⁻¹) ≤
      (∫⁻ y, ((‖u y - v y‖₊ : ℝ≥0∞) ^ 2) ∂ν) ^ (((2 : ℕ) : ℝ)⁻¹) +
        (∫⁻ y, ((‖v y‖₊ : ℝ≥0∞) ^ 2) ∂ν) ^ (((2 : ℕ) : ℝ)⁻¹) := by
  have h12 : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) := by norm_num
  have hM := ENNReal.lintegral_Lp_add_le hd hv h12
  simp only [Pi.add_apply, ENNReal.rpow_natCast, one_div] at hM
  refine le_trans (ENNReal.rpow_le_rpow (lintegral_mono fun y => ?_) (by positivity)) hM
  have h : (‖u y‖₊ : ℝ≥0∞) ≤ ‖u y - v y‖₊ + ‖v y‖₊ := by
    have h' := nnnorm_add_le (u y - v y) (v y)
    rw [sub_add_cancel] at h'
    exact_mod_cast h'
  rw [sq, sq]
  exact mul_le_mul' h h

private theorem coe_nnnorm_conj_mul_sub_le (x x' y y' : ℂ) :
    ((‖(starRingEnd ℂ) x * y - (starRingEnd ℂ) x' * y'‖₊ : ℝ≥0∞)) ≤
      (‖x - x'‖₊ : ℝ≥0∞) * ‖y‖₊ + (‖x'‖₊ : ℝ≥0∞) * ‖y - y'‖₊ := by
  have he : (starRingEnd ℂ) x * y - (starRingEnd ℂ) x' * y' =
      (starRingEnd ℂ) (x - x') * y + (starRingEnd ℂ) x' * (y - y') := by
    rw [map_sub]; ring
  rw [he]
  have h := nnnorm_add_le ((starRingEnd ℂ) (x - x') * y) ((starRingEnd ℂ) x' * (y - y'))
  have h1 : ‖(starRingEnd ℂ) (x - x')‖₊ = ‖x - x'‖₊ := NNReal.eq (RCLike.norm_conj _)
  have h2 : ‖(starRingEnd ℂ) x'‖₊ = ‖x'‖₊ := NNReal.eq (RCLike.norm_conj _)
  rw [nnnorm_mul, nnnorm_mul, h1, h2] at h
  exact_mod_cast h

private theorem lintegral_mul_le_rpow_mul_rpow {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) {f g : Y → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hg : AEMeasurable g ν) :
    ∫⁻ y, f y * g y ∂ν ≤
      (∫⁻ y, (f y) ^ 2 ∂ν) ^ (((2 : ℕ) : ℝ)⁻¹) * (∫⁻ y, (g y) ^ 2 ∂ν) ^ (((2 : ℕ) : ℝ)⁻¹) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_two, one_div] at h
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2]
  exact h

private theorem integral_conj_mul_eq_of_tendsto {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {a b : Y → ℂ} {an bn : ℕ → Y → ℂ} {K : ℂ}
    (hpair : ∀ n : ℕ, ∫ y, (starRingEnd ℂ) (an n y) * bn n y ∂ν = K)
    (hab : AEStronglyMeasurable (fun y : Y => (starRingEnd ℂ) (a y) * b y) ν)
    (habn : ∀ n : ℕ, AEStronglyMeasurable (fun y : Y => (starRingEnd ℂ) (an n y) * bn n y) ν)
    (hNa : AEMeasurable (fun y : Y => (‖a y‖₊ : ℝ≥0∞)) ν) (hNb : AEMeasurable (fun y : Y => (‖b y‖₊ : ℝ≥0∞)) ν)
    (hNan : ∀ n : ℕ, AEMeasurable (fun y : Y => (‖an n y‖₊ : ℝ≥0∞)) ν)
    (hNbn : ∀ n : ℕ, AEMeasurable (fun y : Y => (‖bn n y‖₊ : ℝ≥0∞)) ν)
    (hNda : ∀ n : ℕ, AEMeasurable (fun y : Y => (‖an n y - a y‖₊ : ℝ≥0∞)) ν)
    (hNdb : ∀ n : ℕ, AEMeasurable (fun y : Y => (‖bn n y - b y‖₊ : ℝ≥0∞)) ν)
    (ha2 : ∫⁻ y, ((‖a y‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤) (hb2 : ∫⁻ y, ((‖b y‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤)
    (han2 : ∀ n : ℕ, ∫⁻ y, ((‖an n y‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤) (hbn2 : ∀ n : ℕ, ∫⁻ y, ((‖bn n y‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤)
    (hda : Tendsto (fun n : ℕ => ∫⁻ y, ((‖an n y - a y‖₊ : ℝ≥0∞) ^ 2) ∂ν) atTop (𝓝 0))
    (hdb : Tendsto (fun n : ℕ => ∫⁻ y, ((‖bn n y - b y‖₊ : ℝ≥0∞) ^ 2) ∂ν) atTop (𝓝 0)) :
    ∫ y, (starRingEnd ℂ) (a y) * b y ∂ν = K := by

  set r : ℝ := ((2 : ℕ) : ℝ)⁻¹ with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  set A : ℝ≥0∞ := (∫⁻ y, ((‖a y‖₊ : ℝ≥0∞) ^ 2) ∂ν) ^ r with hA
  set B : ℝ≥0∞ := (∫⁻ y, ((‖b y‖₊ : ℝ≥0∞) ^ 2) ∂ν) ^ r with hB
  set Ea : ℕ → ℝ≥0∞ := fun n => (∫⁻ y, ((‖an n y - a y‖₊ : ℝ≥0∞) ^ 2) ∂ν) ^ r with hEa
  set Eb : ℕ → ℝ≥0∞ := fun n => (∫⁻ y, ((‖bn n y - b y‖₊ : ℝ≥0∞) ^ 2) ∂ν) ^ r with hEb
  have hAtop : A ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0.le ha2
  have hBtop : B ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0.le hb2

  have hint : ∀ (u v : Y → ℂ), AEStronglyMeasurable (fun y : Y => (starRingEnd ℂ) (u y) * v y) ν →
      AEMeasurable (fun y : Y => (‖u y‖₊ : ℝ≥0∞)) ν → AEMeasurable (fun y : Y => (‖v y‖₊ : ℝ≥0∞)) ν →
      ∫⁻ y, ((‖u y‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤ → ∫⁻ y, ((‖v y‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤ →
      Integrable (fun y : Y => (starRingEnd ℂ) (u y) * v y) ν := by
    intro u v huv hu hv hu2 hv2
    refine ⟨huv, ?_⟩
    show ∫⁻ y, ‖(starRingEnd ℂ) (u y) * v y‖ₑ ∂ν < ⊤
    have he : ∀ y, ‖(starRingEnd ℂ) (u y) * v y‖ₑ = (‖u y‖₊ : ℝ≥0∞) * ‖v y‖₊ := by
      intro y
      have hc : ‖(starRingEnd ℂ) (u y)‖₊ = ‖u y‖₊ := NNReal.eq (RCLike.norm_conj _)
      rw [enorm_eq_coe_nnnorm', nnnorm_mul, hc, ENNReal.coe_mul]
    simp_rw [he]
    refine lt_of_le_of_lt (lintegral_mul_le_rpow_mul_rpow ν hu hv) ?_
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hr0.le hu2) (ENNReal.rpow_lt_top_of_nonneg hr0.le hv2)

  have hest : ∀ n : ℕ, ‖K - ∫ y, (starRingEnd ℂ) (a y) * b y ∂ν‖ₑ ≤ Ea n * (Eb n + B) + A * Eb n := by
    intro n
    rw [← hpair n, ← integral_sub (hint _ _ (habn n) (hNan n) (hNbn n) (han2 n) (hbn2 n))
      (hint _ _ hab hNa hNb ha2 hb2)]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    have hpt : ∀ y, ‖(starRingEnd ℂ) (an n y) * bn n y - (starRingEnd ℂ) (a y) * b y‖ₑ ≤
        (‖an n y - a y‖₊ : ℝ≥0∞) * ‖bn n y‖₊ + (‖a y‖₊ : ℝ≥0∞) * ‖bn n y - b y‖₊ := fun y => by
      rw [enorm_eq_coe_nnnorm']
      exact coe_nnnorm_conj_mul_sub_le _ _ _ _
    refine le_trans (lintegral_mono hpt) ?_
    rw [lintegral_add_left' ((hNda n).fun_mul (hNbn n))]
    have h1 := lintegral_mul_le_rpow_mul_rpow ν (hNda n) (hNbn n)
    have h2 := lintegral_mul_le_rpow_mul_rpow ν hNa (hNdb n)
    have h3 : (∫⁻ y, ((‖bn n y‖₊ : ℝ≥0∞) ^ 2) ∂ν) ^ r ≤ Eb n + B := rpow_lintegral_sq_le (hNdb n) hNb
    calc ∫⁻ y, (‖an n y - a y‖₊ : ℝ≥0∞) * ‖bn n y‖₊ ∂ν + ∫⁻ y, (‖a y‖₊ : ℝ≥0∞) * ‖bn n y - b y‖₊ ∂ν
        ≤ Ea n * (∫⁻ y, ((‖bn n y‖₊ : ℝ≥0∞) ^ 2) ∂ν) ^ r + A * Eb n := add_le_add h1 h2
      _ ≤ Ea n * (Eb n + B) + A * Eb n := by gcongr

  have hroot : ∀ (e : ℕ → ℝ≥0∞), Tendsto e atTop (𝓝 0) → Tendsto (fun n => (e n) ^ r) atTop (𝓝 0) := by
    intro e he
    have h := ((ENNReal.continuous_rpow_const (y := r)).tendsto (0 : ℝ≥0∞)).comp he
    rwa [ENNReal.zero_rpow_of_pos hr0] at h
  have hEa0 : Tendsto Ea atTop (𝓝 0) := hroot _ hda
  have hEb0 : Tendsto Eb atTop (𝓝 0) := hroot _ hdb
  have hlim : Tendsto (fun n => Ea n * (Eb n + B) + A * Eb n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => Ea n * (Eb n + B)) atTop (𝓝 (0 * (0 + B))) :=
      ENNReal.Tendsto.mul hEa0 (Or.inr (by simpa using hBtop)) (hEb0.add tendsto_const_nhds)
        (Or.inr ENNReal.zero_ne_top)
    have h2 : Tendsto (fun n => A * Eb n) atTop (𝓝 (A * 0)) := ENNReal.Tendsto.const_mul hEb0 (Or.inr hAtop)
    simpa using h1.add h2

  have h0 : ‖K - ∫ y, (starRingEnd ℂ) (a y) * b y ∂ν‖ₑ ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hest
  have h00 : K - ∫ y, (starRingEnd ℂ) (a y) * b y ∂ν = 0 := by simpa using le_antisymm h0 zero_le
  exact (sub_eq_zero.1 h00).symm

end PairingLimit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

end PairingLimitGeneric
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

section FibreLimit

open LanglandsTunnell.CubicInduction Filter Topology
open scoped NNReal

private theorem exists_rows_tendsto (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hs1 : Filter.Tendsto s (nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)) (nhds 1))
    (hdense : ∀ O ∈ nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0),
      (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
        0 < (Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
              (O ∩ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j})))
    {p : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → Prop}
    (hp : letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
      ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
          {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
            ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}), p x) :
    ∃ y : ℕ → (Fin 3 → AdeleRing (𝓞 ℚ) ℚ),
      (∀ n, y n ∈ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
          ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j} ∧ p (y n)) ∧
      Filter.Tendsto (fun n => s (y n)) Filter.atTop (nhds 1) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  have hR : ∀ O ∈ nhds e₃row, 0 < (Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
      (O ∩ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
        ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}) := by
    intro O hO
    have h := hdense O hO
    simpa only [] using h
  obtain ⟨y, hy, hye⟩ := exists_seq_tendsto_of_forall_pos
    (Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) e₃row _ hR hp
  exact ⟨y, hy, hs1.comp hye⟩

private theorem tendsto_Wq_translateRight (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hFc : Continuous F) {g : ℕ → AdelicGL 3 (𝓞 ℚ) ℚ} (hg : Filter.Tendsto g Filter.atTop (nhds 1)) (q : Orb P) :
    Filter.Tendsto (fun n => Wq (SlabL2.translateRight (g n) F) q) Filter.atTop (nhds (Wq F q)) := by
  have hW : Continuous (whittaker3 pins0 NumberField.StandardAddChar.psiQ F) :=
    continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hFc
  have h1 : (fun n => Wq (SlabL2.translateRight (g n) F) q) =
      fun n => whittaker3 pins0 NumberField.StandardAddChar.psiQ F ((q.out : AdelicGL 3 (𝓞 ℚ) ℚ) * g n) := by
    funext n
    exact whittaker3_translateRight _ _ _
  rw [h1]
  have h2 : Filter.Tendsto (fun n => (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) * g n) Filter.atTop
      (nhds ((q.out : AdelicGL 3 (𝓞 ℚ) ℚ) * 1)) :=
    tendsto_const_nhds.mul hg
  rw [mul_one] at h2
  exact (hW.tendsto _).comp h2

private theorem aemeasurable_sq_Wq (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) (ν : Measure (Orb P))
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hFaut : IsAut F) (hFc : Continuous F) :
    AEMeasurable (fun q : Orb P => ((‖Wq F q‖₊ : ℝ≥0∞) ^ 2)) ν :=
  (PairingLimit.aemeasurable_coe_nnnorm_of_conj_mul
    (measurable_pairing_out P hFaut hFaut hFc hFc).aestronglyMeasurable).pow_const 2

private theorem lintegral_sq_Wq_le_of_rows (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) (ν : Measure (Orb P))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hs1 : Filter.Tendsto s (nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)) (nhds 1))
    (hdense : ∀ O ∈ nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0),
      (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
        0 < (Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
              (O ∩ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j})))
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hFaut : IsAut F) (hFc : Continuous F) (C : ℝ≥0∞)
    (hrows : letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
      ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
          {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
            ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
        ∫⁻ q, ((‖Wq (SlabL2.translateRight (s x) F) q‖₊ : ℝ≥0∞) ^ 2) ∂ν = C) :
    ∫⁻ q, ((‖Wq F q‖₊ : ℝ≥0∞) ^ 2) ∂ν ≤ C := by
  obtain ⟨y, hy, hys⟩ := exists_rows_tendsto S s hs1 hdense hrows
  refine PairingLimit.lintegral_sq_le_of_tendsto_ae ν (fun n q => Wq (SlabL2.translateRight (s (y n)) F) q)
    (fun q => Wq F q) (fun n => ?_) C (fun n => ((hy n).2).le) (Eventually.of_forall fun q => ?_)
  · exact aemeasurable_sq_Wq P ν (translateRight_aut hFaut _) (continuous_translateRight hFc _)
  · exact tendsto_Wq_translateRight P hFc hys q

private theorem isAut_add_smul {F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : IsAut F) (hF' : IsAut F') (z : ℂ) :
    IsAut (F + z • F') := by
  intro γ g
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hF γ g, hF' γ g]

private theorem Wq_add_smul (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) {F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hFc : Continuous F) (hF'c : Continuous F') (z : ℂ) (q : Orb P) :
    Wq (F + z • F') q = Wq F q + z * Wq F' q := by
  show whittaker3 pins0 NumberField.StandardAddChar.psiQ (F + z • F') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) = _
  rw [whittaker3_add (F' := z • F') hFc (hF'c.const_smul z), whittaker3_smul]

private theorem integral_conj_whittaker3_translateRight_mul_eq_mul_inner
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (adm : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → Prop)
    (hadm : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      Continuous φ ∧
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * φ g) ∧
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) φ) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen1 p)) φ (lam1 p)) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen2 p)) φ (lam2 p)))
    (hcusp : ∀ φ, adm φ → φ ∈ cuspFunctions ω a b Φ₀)
    (V L : ℝ≥0∞) (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (ℓ : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ((Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) → ℝ≥0∞)
    (hℓ : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      ℓ φ Φ ≠ ⊤ ∧ (φ ≠ 0 → ℓ φ Φ ≠ 0))
    (hℓeq : ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ),
          ℓ φ Φ =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
          ENNReal.ofReal
            ((∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) /
                (3 * ((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
                  (Set.univ.pi fun _ : Fin 3 => NumberField.AdelicBox.adelicBox ℚ)).toReal) *
              ∫ g, ‖φ g‖ ^ 2 ∂(domainMeasure a b Φ₀))))
    (hF2 :
        ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
        ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
          (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
            (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
            Φ = fun x => ∏ i, Φc i (x i)) ∧
          (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
           0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        Filter.Tendsto
            (fun σ : ℝ => WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ Φ σ S)
            (nhdsWithin 1 (Set.Ioi 1))
            (nhds (WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ Φ 1 S)) ∧
          WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ Φ 1 S * (V * L) = ℓ φ Φ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hf : adm f) (hf0 : f ≠ 0)
    (f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hf' : adm f') (hf'0 : f' ≠ 0)
    (hmem :
        ∀ (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (φ : Fin n → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)),
          (∀ i, φ i = f ∨ φ i = f') →
          (∀ i, ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (t i) = 1) →
          adm (fun x => ∑ i, c i * φ i (x * t i)))
    (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hfib : ∀ F ∈ cuspFunctions ω a b Φ₀, ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F Φ 1 S =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
            ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)))
    (hs1 : Filter.Tendsto s (nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)) (nhds 1))
    (hdense : ∀ O ∈ nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0),
      (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
        0 < (Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
              (O ∩ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j})))
    (hunique : ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F) → ∀ C : ℝ≥0∞, C ≠ ⊤ →
      (∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
            C * ∫⁻ x, (‖Φ x‖₊ : ℝ≥0∞)
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) →
      ∃ C₁ : ℝ≥0∞,
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
              {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
              ∂ν = C₁))
    (hpair :
        ∃ c : ℝ, 0 < c ∧
          (∀ (F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), adm F → adm F' → (∀ z : ℂ, adm (fun x => F x + z * F' x)) →
            ∀ (hF : F ∈ cuspFunctions ω a b Φ₀) (hF' : F' ∈ cuspFunctions ω a b Φ₀),
            (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
              ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
                  {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                    ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
                ∫ q, (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                  NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)) *
                    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                  NumberField.StandardAddChar.psiQ (translateRight (s x) F') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν =
                    c * ⟪toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ)) ∧
          (∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm F → ∀ hF : F ∈ cuspFunctions ω a b Φ₀,
            (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
              ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
                  {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                    ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
                  ∂ν = ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖ ^ 2))))
    (hiso : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
        ∃ hmem : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, translateRight g F ∈ cuspFunctions ω a b Φ₀,
          (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
            ‖toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩‖ = ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖) ∧
          Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩)
    (hsec : ∀ x ∈ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
        ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
      ∃ t : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
        ∀ G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm G → translateRight (s x) G = translateRight t G) :
    ∃ c : ℝ, 0 < c ∧
      (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f ∈ automorphicSubmodule ω a b Φ₀)
          (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' f' ∈ automorphicSubmodule ω a b Φ₀),
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
        ∫ q, (starRingEnd ℂ) (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (translateRight g f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)) *
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (translateRight g' f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ) ∂ν =
      c * ⟪toL2 ω a b Φ₀ ⟨translateRight g f, hg⟩, toL2 ω a b Φ₀ ⟨translateRight g' f', hg'⟩⟫_ℂ) ∧
      (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f ∈ automorphicSubmodule ω a b Φ₀),
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
          ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (translateRight g f) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
        ∂ν = ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight g f, hg⟩‖ ^ 2)) ∧
      (∀ (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' f' ∈ automorphicSubmodule ω a b Φ₀),
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
          ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (translateRight g' f') (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
        ∂ν = ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight g' f', hg'⟩‖ ^ 2)) := by
  letI mA : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ

  have _ := @hω
  have _ := @hΦ₀
  have _ := @hL0
  have _ := @hLtop
  have _ := @hℓ
  have _ := @hℓeq
  have _ := @hF2
  have _ := @hf
  have _ := @hf0
  have _ := @hf'
  have _ := @hf'0
  have _ := @hfib
  have _ := @hunique
  obtain ⟨c, hc, hP, hL⟩ := hpair
  have haut : ∀ G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm G → IsAut G := fun G hG => (hadm G hG).2.1
  have hcon : ∀ G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm G → Continuous G := fun G hG => (hadm G hG).1

  have hmem1 : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, (φ = f ∨ φ = f') → ∀ t : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p t = 1) → adm (translateRight t φ) := by
    intro φ hφ t ht
    have h := hmem 1 (fun _ => 1) (fun _ => t) (fun _ => φ) (fun _ => hφ) (fun _ p hp => ht p hp)
    convert h using 1
    funext x
    simp [translateRight]
  have hmem2 : ∀ φ χ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, (φ = f ∨ φ = f') → (χ = f ∨ χ = f') →
      ∀ (c₁ c₂ : ℂ) (t₁ t₂ : AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p t₁ = 1) →
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p t₂ = 1) →
      adm (fun x => c₁ * φ (x * t₁) + c₂ * χ (x * t₂)) := by
    intro φ χ hφ hχ c₁ c₂ t₁ t₂ h₁ h₂
    have h := hmem 2 ![c₁, c₂] ![t₁, t₂] ![φ, χ] (fun i => by fin_cases i <;> simp [hφ, hχ])
      (fun i p hp => by fin_cases i <;> simp [h₁ p hp, h₂ p hp])
    convert h using 1
    funext x
    simp [Fin.sum_univ_two]

  have hsq : ∀ G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ∀ hG : adm G,
      ∫⁻ q, ((‖Wq G q‖₊ : ℝ≥0∞) ^ 2) ∂ν ≤ ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨G, (hcusp G hG).1⟩‖ ^ 2) :=
    fun G hG => lintegral_sq_Wq_le_of_rows S P ν s hs1 hdense (haut G hG) (hcon G hG) _ (hL G hG (hcusp G hG))

  have hcore : ∀ (F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : adm F) (hF' : adm F'),
      (∀ z : ℂ, adm (fun x => F x + z * F' x)) →
      (∀ x ∈ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
          ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
        adm (translateRight (s x) F + (-1 : ℂ) • F)) →
      (∀ x ∈ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
          ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
        adm (translateRight (s x) F' + (-1 : ℂ) • F')) →
      ∫ q, (starRingEnd ℂ) (Wq F q) * Wq F' q ∂ν =
        c * ⟪toL2 ω a b Φ₀ ⟨F, (hcusp F hF).1⟩, toL2 ω a b Φ₀ ⟨F', (hcusp F' hF').1⟩⟫_ℂ := by
    intro F F' hF hF' hz hdF hdF'
    have hFc := hcon F hF
    have hF'c := hcon F' hF'
    have hFa := haut F hF
    have hF'a := haut F' hF'
    have hFcu := hcusp F hF
    have hF'cu := hcusp F' hF'

    obtain ⟨y, hy, hys⟩ := exists_rows_tendsto S s hs1 hdense
      ((hP F F' hF hF' hz hFcu hF'cu).and ((hL F hF hFcu).and (hL F' hF' hF'cu)))
    obtain ⟨hmF, -, hcF⟩ := hiso F hFcu
    obtain ⟨hmF', -, hcF'⟩ := hiso F' hF'cu

    have hdiff : ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous G → ∀ (n : ℕ) (q : Orb P),
        Wq (translateRight (s (y n)) G + (-1 : ℂ) • G) q = Wq (translateRight (s (y n)) G) q - Wq G q := by
      intro G hGc n q
      rw [Wq_add_smul P (continuous_translateRight hGc _) hGc]
      ring
    have hdaut : ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), IsAut G → ∀ n : ℕ,
        IsAut (translateRight (s (y n)) G + (-1 : ℂ) • G) :=
      fun G hGa n => isAut_add_smul (translateRight_aut hGa _) hGa (-1)
    have hdcon : ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous G → ∀ n : ℕ,
        Continuous (translateRight (s (y n)) G + (-1 : ℂ) • G) :=
      fun G hGc n => (continuous_translateRight hGc _).add (hGc.const_smul (-1 : ℂ))

    have hNd : ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), IsAut G → Continuous G → ∀ n : ℕ,
        AEMeasurable (fun q : Orb P => (‖Wq (translateRight (s (y n)) G) q - Wq G q‖₊ : ℝ≥0∞)) ν := by
      intro G hGa hGc n
      refine (PairingLimit.aemeasurable_coe_nnnorm_of_conj_mul
        (measurable_pairing_out P (hdaut G hGa n) (hdaut G hGa n) (hdcon G hGc n)
          (hdcon G hGc n)).aestronglyMeasurable).congr (Eventually.of_forall fun q => ?_)
      show ((‖Wq (translateRight (s (y n)) G + (-1 : ℂ) • G) q‖₊ : ℝ≥0∞)) = _
      rw [hdiff G hGc n q]

    have hms : ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : adm G)
        (hmG : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, translateRight g G ∈ cuspFunctions ω a b Φ₀),
        (Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => toL2 ω a b Φ₀ ⟨translateRight g G, (hmG g).1⟩) →
        (∀ n : ℕ, adm (translateRight (s (y n)) G + (-1 : ℂ) • G)) →
        Tendsto (fun n : ℕ => ∫⁻ q, ((‖Wq (translateRight (s (y n)) G) q - Wq G q‖₊ : ℝ≥0∞) ^ 2) ∂ν)
          atTop (𝓝 0) := by
      intro G hG hmG hcG hdG
      have hGcu := hcusp G hG

      have hb : ∀ n : ℕ, ∫⁻ q, ((‖Wq (translateRight (s (y n)) G) q - Wq G q‖₊ : ℝ≥0∞) ^ 2) ∂ν ≤
          ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight (s (y n)) G, (hmG _).1⟩ -
            toL2 ω a b Φ₀ ⟨G, hGcu.1⟩‖ ^ 2) := by
        intro n
        have h := hsq _ (hdG n)
        have hl : ∫⁻ q, ((‖Wq (translateRight (s (y n)) G) q - Wq G q‖₊ : ℝ≥0∞) ^ 2) ∂ν =
            ∫⁻ q, ((‖Wq (translateRight (s (y n)) G + (-1 : ℂ) • G) q‖₊ : ℝ≥0∞) ^ 2) ∂ν :=
          lintegral_congr fun q => by rw [hdiff G (hcon G hG) n q]
        have hv : toL2 ω a b Φ₀ ⟨translateRight (s (y n)) G + (-1 : ℂ) • G, (hcusp _ (hdG n)).1⟩ =
            toL2 ω a b Φ₀ ⟨translateRight (s (y n)) G, (hmG _).1⟩ - toL2 ω a b Φ₀ ⟨G, hGcu.1⟩ := by
          rw [← map_sub]
          congr 1
          apply Subtype.ext
          show translateRight (s (y n)) G + (-1 : ℂ) • G = translateRight (s (y n)) G - G
          funext x
          simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          ring
        rw [hl, ← hv]
        exact h

      have h1 : Tendsto (fun n : ℕ => toL2 ω a b Φ₀ ⟨translateRight (s (y n)) G, (hmG _).1⟩) atTop
          (𝓝 (toL2 ω a b Φ₀ ⟨G, hGcu.1⟩)) := by
        have h := (hcG.tendsto 1).comp hys
        have he : toL2 ω a b Φ₀ ⟨translateRight 1 G, (hmG 1).1⟩ = toL2 ω a b Φ₀ ⟨G, hGcu.1⟩ := by
          congr 1
          exact Subtype.ext (translateRight_one G)
        rw [he] at h
        exact h
      have h2 : Tendsto (fun n : ℕ => ‖toL2 ω a b Φ₀ ⟨translateRight (s (y n)) G, (hmG _).1⟩ -
          toL2 ω a b Φ₀ ⟨G, hGcu.1⟩‖) atTop (𝓝 0) := by
        have h := (h1.sub (tendsto_const_nhds (x := toL2 ω a b Φ₀ ⟨G, hGcu.1⟩))).norm
        rw [sub_self, norm_zero] at h
        exact h
      have h3 : Tendsto (fun n : ℕ => ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight (s (y n)) G, (hmG _).1⟩ -
          toL2 ω a b Φ₀ ⟨G, hGcu.1⟩‖ ^ 2)) atTop (𝓝 0) := by
        have h := ENNReal.tendsto_ofReal ((h2.pow 2).const_mul c)
        rwa [zero_pow two_ne_zero, mul_zero, ENNReal.ofReal_zero] at h
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun n => zero_le) hb

    have hlim := PairingLimit.integral_conj_mul_eq_of_tendsto
      (ν := ν) (a := fun q => Wq F q) (b := fun q => Wq F' q)
      (an := fun n q => Wq (translateRight (s (y n)) F) q) (bn := fun n q => Wq (translateRight (s (y n)) F') q)
      (K := c * ⟪toL2 ω a b Φ₀ ⟨F, hFcu.1⟩, toL2 ω a b Φ₀ ⟨F', hF'cu.1⟩⟫_ℂ)
      (fun n => (hy n).2.1)
      (measurable_pairing_out P hFa hF'a hFc hF'c).aestronglyMeasurable
      (fun n => (measurable_pairing_out P (translateRight_aut hFa _) (translateRight_aut hF'a _)
        (continuous_translateRight hFc _) (continuous_translateRight hF'c _)).aestronglyMeasurable)
      (PairingLimit.aemeasurable_coe_nnnorm_of_conj_mul
        (measurable_pairing_out P hFa hFa hFc hFc).aestronglyMeasurable)
      (PairingLimit.aemeasurable_coe_nnnorm_of_conj_mul
        (measurable_pairing_out P hF'a hF'a hF'c hF'c).aestronglyMeasurable)
      (fun n => PairingLimit.aemeasurable_coe_nnnorm_of_conj_mul
        (measurable_pairing_out P (translateRight_aut hFa _) (translateRight_aut hFa _)
          (continuous_translateRight hFc _) (continuous_translateRight hFc _)).aestronglyMeasurable)
      (fun n => PairingLimit.aemeasurable_coe_nnnorm_of_conj_mul
        (measurable_pairing_out P (translateRight_aut hF'a _) (translateRight_aut hF'a _)
          (continuous_translateRight hF'c _) (continuous_translateRight hF'c _)).aestronglyMeasurable)
      (hNd F hFa hFc) (hNd F' hF'a hF'c)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsq F hF))
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsq F' hF'))
      (fun n => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_of_eq (hy n).2.2.1))
      (fun n => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_of_eq (hy n).2.2.2))
      (hms F hF hmF hcF fun n => hdF (y n) (hy n).1)
      (hms F' hF' hmF' hcF' fun n => hdF' (y n) (hy n).1)
    exact hlim

  have hpairId : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f ∈ automorphicSubmodule ω a b Φ₀)
      (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' f' ∈ automorphicSubmodule ω a b Φ₀),
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g' = 1) →
      ∫ q, (starRingEnd ℂ) (Wq (translateRight g f) q) * Wq (translateRight g' f') q ∂ν =
        c * ⟪toL2 ω a b Φ₀ ⟨translateRight g f, hg⟩, toL2 ω a b Φ₀ ⟨translateRight g' f', hg'⟩⟫_ℂ := by
    intro g hg g' hg' hgS hg'S
    have hFadm : adm (translateRight g f) := hmem1 f (Or.inl rfl) g hgS
    have hF'adm : adm (translateRight g' f') := hmem1 f' (Or.inr rfl) g' hg'S

    have hd : ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : φ = f ∨ φ = f') (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ),
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g₀ = 1) →
        ∀ x ∈ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
          ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
        adm (translateRight (s x) (translateRight g₀ φ) + (-1 : ℂ) • translateRight g₀ φ) := by
      intro φ hφ g₀ hg₀ x hx
      obtain ⟨t, ht, hts⟩ := hsec x hx
      rw [hts _ (hmem1 φ hφ g₀ hg₀), ← translateRight_mul]
      have htg : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (t * g₀) = 1 := fun p hp => by
        rw [map_mul, ht p hp, hg₀ p hp, one_mul]
      have h := hmem2 φ φ hφ hφ 1 (-1) (t * g₀) g₀ htg hg₀
      convert h using 1
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, translateRight]
      ring
    have hz : ∀ z : ℂ, adm (fun x => translateRight g f x + z * translateRight g' f' x) := by
      intro z
      have h := hmem2 f f' (Or.inl rfl) (Or.inr rfl) 1 z g g' hgS hg'S
      convert h using 1
      funext x
      simp only [translateRight, one_mul]
    exact hcore _ _ hFadm hF'adm hz (hd f (Or.inl rfl) g hgS) (hd f' (Or.inr rfl) g' hg'S)

  have hsqId : ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : φ = f ∨ φ = f') (g : AdelicGL 3 (𝓞 ℚ) ℚ)
      (hg : translateRight g φ ∈ automorphicSubmodule ω a b Φ₀),
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
      (∫ q, (starRingEnd ℂ) (Wq (translateRight g φ) q) * Wq (translateRight g φ) q ∂ν =
        c * ⟪toL2 ω a b Φ₀ ⟨translateRight g φ, hg⟩, toL2 ω a b Φ₀ ⟨translateRight g φ, hg⟩⟫_ℂ) →
      ∫⁻ q, ((‖Wq (translateRight g φ) q‖₊ : ℝ≥0∞) ^ 2) ∂ν =
        ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight g φ, hg⟩‖ ^ 2) := by
    intro φ hφ g hg hgS hself
    have hGadm : adm (translateRight g φ) := hmem1 φ hφ g hgS
    have htop : ∫⁻ q, ((‖Wq (translateRight g φ) q‖₊ : ℝ≥0∞) ^ 2) ∂ν ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsq _ hGadm)
    have h1 := integral_selfPairing_eq P ν (haut _ hGadm) (hcon _ hGadm)
    have h2 : (c : ℂ) * ⟪toL2 ω a b Φ₀ ⟨translateRight g φ, hg⟩, toL2 ω a b Φ₀ ⟨translateRight g φ, hg⟩⟫_ℂ =
        ((c * ‖toL2 ω a b Φ₀ ⟨translateRight g φ, hg⟩‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]
      push_cast
      ring
    have h3 : (((∫⁻ q, ((‖Wq (translateRight g φ) q‖₊ : ℝ≥0∞) ^ 2) ∂ν).toReal : ℝ) : ℂ) =
        ((c * ‖toL2 ω a b Φ₀ ⟨translateRight g φ, hg⟩‖ ^ 2 : ℝ) : ℂ) :=
      (h1.symm.trans hself).trans h2
    calc ∫⁻ q, ((‖Wq (translateRight g φ) q‖₊ : ℝ≥0∞) ^ 2) ∂ν
        = ENNReal.ofReal ((∫⁻ q, ((‖Wq (translateRight g φ) q‖₊ : ℝ≥0∞) ^ 2) ∂ν).toReal) :=
          (ENNReal.ofReal_toReal htop).symm
      _ = ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight g φ, hg⟩‖ ^ 2) := by
          rw [Complex.ofReal_injective h3]

  have hself : ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : φ = f ∨ φ = f') (g : AdelicGL 3 (𝓞 ℚ) ℚ)
      (hg : translateRight g φ ∈ automorphicSubmodule ω a b Φ₀),
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) →
      ∫⁻ q, ((‖Wq (translateRight g φ) q‖₊ : ℝ≥0∞) ^ 2) ∂ν =
        ENNReal.ofReal (c * ‖toL2 ω a b Φ₀ ⟨translateRight g φ, hg⟩‖ ^ 2) := by
    intro φ hφ g hg hgS
    have hGadm : adm (translateRight g φ) := hmem1 φ hφ g hgS
    have hd : ∀ x ∈ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
          ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
        adm (translateRight (s x) (translateRight g φ) + (-1 : ℂ) • translateRight g φ) := by
      intro x hx
      obtain ⟨t, ht, hts⟩ := hsec x hx
      rw [hts _ hGadm, ← translateRight_mul]
      have htg : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (t * g) = 1 := fun p hp => by
        rw [map_mul, ht p hp, hgS p hp, one_mul]
      have h := hmem2 φ φ hφ hφ 1 (-1) (t * g) g htg hgS
      convert h using 1
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, translateRight]
      ring
    have hz : ∀ z : ℂ, adm (fun x => translateRight g φ x + z * translateRight g φ x) := by
      intro z
      have h := hmem2 φ φ hφ hφ 1 z g g hgS hgS
      convert h using 1
      funext x
      simp only [translateRight, one_mul]
    exact hsqId φ hφ g hg hgS (hcore _ _ hGadm hGadm hz hd hd)
  exact ⟨c, hc, hpairId, fun g hg hgS => hself f (Or.inl rfl) g hg hgS,
    fun g' hg' hg'S => hself f' (Or.inr rfl) g' hg' hg'S⟩

end FibreLimit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

end PairingLimit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq.Fibration"

theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (adm : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → Prop)
    (hadm : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      Continuous φ ∧
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * φ g) ∧
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) φ) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen1 p)) φ (lam1 p)) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen2 p)) φ (lam2 p)))
    (hcusp : ∀ φ, adm φ → φ ∈ cuspFunctions ω a b Φ₀)
    (V L : ℝ≥0∞) (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (ℓ : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ((Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) → ℝ≥0∞)
    (hℓ : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      ℓ φ Φ ≠ ⊤ ∧ (φ ≠ 0 → ℓ φ Φ ≠ 0))
    (hℓeq : ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ),
          ℓ φ Φ =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
          ENNReal.ofReal
            ((∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) /
                (3 * ((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
                  (Set.univ.pi fun _ : Fin 3 => NumberField.AdelicBox.adelicBox ℚ)).toReal) *
              ∫ g, ‖φ g‖ ^ 2 ∂(domainMeasure a b Φ₀))))
    (hF2 :
        ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm φ →
        ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
          (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
            (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
            Φ = fun x => ∏ i, Φc i (x i)) ∧
          (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
           0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        Filter.Tendsto
            (fun σ : ℝ => WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ Φ σ S)
            (nhdsWithin 1 (Set.Ioi 1))
            (nhds (WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ Φ 1 S)) ∧
          WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ φ Φ 1 S * (V * L) = ℓ φ Φ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hf : adm f) (hf0 : f ≠ 0)
    (f' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hf' : adm f') (hf'0 : f' ≠ 0)
    (hmem :
        ∀ (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (φ : Fin n → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)),
          (∀ i, φ i = f ∨ φ i = f') →
          (∀ i, ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (t i) = 1) →
          adm (fun x => ∑ i, c i * φ i (x * t i))) :
    ∃ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f ∈ automorphicSubmodule ω a b Φ₀)
      (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' f' ∈ automorphicSubmodule ω a b Φ₀),
      ⟪toL2 ω a b Φ₀ ⟨translateRight g f, hg⟩, toL2 ω a b Φ₀ ⟨translateRight g' f', hg'⟩⟫_ℂ ≠ 0 := by

  by_contra hcontra
  have hvan0 : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g f ∈ automorphicSubmodule ω a b Φ₀)
      (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' f' ∈ automorphicSubmodule ω a b Φ₀),
      ⟪toL2 ω a b Φ₀ ⟨translateRight g f, hg⟩, toL2 ω a b Φ₀ ⟨translateRight g' f', hg'⟩⟫_ℂ = 0 := by
    intro g hg g' hg'
    by_contra hne
    exact hcontra ⟨g, hg, g', hg', hne⟩

  obtain ⟨P, ν, s, hfib, hs1, hdense, hunique, hP, hcomp, μP, c₀, hμP, hμPo, hμPc, hc₀, hc₀top, hν⟩ :=
    LanglandsTunnell.CubicInduction.exists_whittakerBlock_one_eq_lintegral_and_eq_smul_map_withDensity_haar ω a b Φ₀ S

  have hpair := integral_conj_whittaker3_mul_eq_mul_inner_of_adm S ω hω lam1 lam2 a b Φ₀ hΦ₀ adm hadm hcusp V L hL0
    hLtop ℓ hℓ hℓeq hF2 (Fibration.exists_testFunction_pos_mass S) P ν s hfib hs1 hdense hunique

  have hiso : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
      ∃ hmem : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, translateRight g F ∈ cuspFunctions ω a b Φ₀,
        (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
          ‖toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩‖ = ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖) ∧
        Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩ :=
    fun F hF =>
      LanglandsTunnell.CubicInduction.exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀
        hΦ₀ F hF
  have hsec : ∀ x ∈ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
      ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
      ∃ t : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
        ∀ G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, adm G → translateRight (s x) G = translateRight t G :=
    fun x hx =>
      ⟨Fibration.keptOutside S (s x), fun _ hp => Fibration.componentAt3_keptOutside_of_notMem S (s x) hp,
        fun G hG => Fibration.translateRight_eq_translateRight_keptOutside S (hcomp x hx) (hadm G hG).1
          (hadm G hG).2.2.2.1⟩

  have hmemFF : ∀ (φ ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), (φ = f ∨ φ = f') → (ψ = f ∨ ψ = f') →
      ∀ (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (χ : Fin n → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)),
        (∀ i, χ i = φ ∨ χ i = ψ) →
        (∀ i, ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (t i) = 1) →
        adm (fun x => ∑ i, c i * χ i (x * t i)) :=
    fun φ ψ hφ hψ n c t χ hχ ht =>
      hmem n c t χ (fun i => (hχ i).elim (fun h => by rw [h]; exact hφ) (fun h => by rw [h]; exact hψ)) ht
  have hG1L := fun (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : adm φ) (hφ0 : φ ≠ 0) (hφm : φ = f ∨ φ = f')
      (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hψ : adm ψ) (hψ0 : ψ ≠ 0) (hψm : ψ = f ∨ ψ = f') =>
    integral_conj_whittaker3_translateRight_mul_eq_mul_inner S ω hω lam1 lam2 a b Φ₀ hΦ₀ adm hadm hcusp V L hL0 hLtop
      ℓ hℓ hℓeq hF2 φ hφ hφ0 ψ hψ hψ0 (hmemFF φ ψ hφm hψm) P ν s hfib hs1 hdense hunique hpair hiso hsec
  obtain ⟨c, -, hpairT, -, -⟩ := hG1L f hf hf0 (Or.inl rfl) f' hf' hf'0 (Or.inr rfl)
  obtain ⟨c₁, hc₁, hpairF, hsqF, -⟩ := hG1L f hf hf0 (Or.inl rfl) f hf hf0 (Or.inl rfl)
  obtain ⟨c₂, hc₂, hpairF', hsqF', -⟩ := hG1L f' hf' hf'0 (Or.inr rfl) f' hf' hf'0 (Or.inr rfl)
  obtain ⟨hmf, -, -⟩ := hiso f (hcusp f hf)
  obtain ⟨hmf', -, -⟩ := hiso f' (hcusp f' hf')

  have hzero :=
    LanglandsTunnell.CubicInduction.conj_whittaker3_mul_whittaker3_eq_zero_of_forall_integral_conj_mul_eq_zero
      S ω hω lam1 lam2 a b Φ₀ hΦ₀ f f' (hcusp f hf) (hcusp f' hf')
      (hadm f hf).2.2.2.1 (hadm f' hf').2.2.2.1 ⟨(hadm f hf).2.2.2.2.1, (hadm f hf).2.2.2.2.2⟩
      ⟨(hadm f' hf').2.2.2.2.1, (hadm f' hf').2.2.2.2.2⟩ P hP ν μP hμP hμPo hμPc c₀ hc₀ hc₀top hν
      (fun g g' hgS hg'S => by
        rw [hpairT g (hmf g).1 g' (hmf' g').1 hgS hg'S, hvan0 g (hmf g).1 g' (hmf' g').1, mul_zero])
      ⟨c₁, hc₁, hpairF, hsqF⟩ ⟨c₂, hc₂, hpairF', hsqF'⟩

  obtain ⟨Φ₁, hΦ₁⟩ := Fibration.exists_testFunction_pos_mass S
  have hpt : ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), adm φ → φ ≠ 0 → ∃ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p g = 1) ∧
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ g ≠ 0 := by
    intro φ hφ hφ0
    have hblock : WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ Φ₁ 1 S ≠ 0 := fun h0 =>
      (hℓ φ hφ Φ₁ hΦ₁).2 hφ0 (by rw [← (hF2 φ hφ Φ₁ hΦ₁).2, h0, zero_mul])
    obtain ⟨g₁, hg₁, hW₁⟩ :=
      Fibration.exists_shellCond_and_whittaker3_ne_zero_of_block_ne_zero (S := S) (hb := hblock)
    exact Fibration.exists_componentAt3_eq_one_and_whittaker3_ne_zero S (hadm φ hφ).1 (hadm φ hφ).2.2.2.1
      (hadm φ hφ).2.1 hg₁ hW₁
  obtain ⟨g₀, hg₀S, hW₀⟩ := hpt f hf hf0
  obtain ⟨g₀', hg₀'S, hW₀'⟩ := hpt f' hf' hf'0
  exact mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hW₀) hW₀' (hzero g₀ g₀' hg₀S hg₀'S)

end S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq (solution)
