-- Prove2me | solution 1 for LanglandsTunnell.exists_admitsModulus_gaussSumFn_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/22ed39eb-91db-54c3-8901-b5b36730dd3c

import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_exists_admitsModulus_gaussSumFn_ne_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply"
p2m_attr_erase "simp" "Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option Elab.async false
set_option autoImplicit false

open NumberField
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel

section GSolLegs

open IsDedekindDomain
open scoped Classical

private theorem whittakerCoefficient_comb_aux (F : Type) [Field F] [NumberField F]
    (pins : AutomorphicForm.CarrierPins F)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ)
    {ι : Type} [Fintype ι] (w : ι → ℂ)
    (n : ι → AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F)
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F → ℂ)
    (h3 : ∀ (α : F) (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F),
      AutomorphicForm.WhittakerCoefficientIntegrable F pins ψ φ α g)
    (α : F) (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F) :
    AutomorphicForm.whittakerCoefficient F pins ψ (fun x => ∑ v : ι, w v * φ (x * n v)) α g =
      ∑ v : ι, w v * AutomorphicForm.whittakerCoefficient F pins ψ φ α (g * n v) := by
  simp only [AutomorphicForm.WhittakerCoefficientIntegrable] at h3
  simp only [AutomorphicForm.whittakerCoefficient]
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum _ fun v _ => (h3 α (g * n v)).const_mul _]
  simp_rw [MeasureTheory.integral_const_mul]

private theorem isBoundedGenuineFn_comb_aux (F : Type) [Field F] [NumberField F]
    (pins : AutomorphicForm.CarrierPins F)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ)
    {ι : Type} [Fintype ι] (w : ι → ℂ)
    (n : ι → AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F)
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F → ℂ)
    (h : AutomorphicForm.IsBoundedGenuineFn F pins ψ φ) :
    AutomorphicForm.IsBoundedGenuineFn F pins ψ (fun x => ∑ v : ι, w v * φ (x * n v)) := by
  classical
  rw [AutomorphicForm.isBoundedGenuineFn_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    exact continuous_finsetSum _ fun v _ =>
      continuous_const.mul (h1.comp (continuous_id.mul continuous_const))
  ·
    intro c u d₁ d₂ T hc hd₁
    choose C hC using fun v : ι => h2 c u d₁ d₂ (T.image (· * n v)) hc hd₁
    refine ⟨∑ v : ι, ‖w v‖ * C v, ?_⟩
    intro g hg
    obtain ⟨x, hxT, s, hs, rfl⟩ := Set.mem_iUnion₂.1 hg
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left (hC v _ ?_) (norm_nonneg _)
    exact Set.mem_iUnion₂.2
      ⟨x * n v, Finset.mem_image_of_mem (· * n v) hxT, ⟨s, hs, (mul_assoc s x (n v)).symm⟩⟩
  ·
    intro α g
    simp only [AutomorphicForm.WhittakerCoefficientIntegrable] at h3 ⊢
    simp_rw [Finset.sum_mul, mul_assoc]
    exact MeasureTheory.integrable_finsetSum _ fun v _ => (h3 α (g * n v)).const_mul _
  ·
    intro g
    simp_rw [whittakerCoefficient_comb_aux F pins ψ w n φ h3]
    exact summable_sum fun v _ => (h4 (g * n v)).mul_left _

private noncomputable def gsolEtaLoc (F : Type) [Field F] [NumberField F] (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : (𝔭.adicCompletionIntegers F)ˣ →* ℂˣ :=
  η.comp ((Units.map (finIncl (𝓞 F) F)).comp ((localUnit (𝓞 F) F 𝔭).comp
    (Units.map (𝔭.adicCompletionIntegers F).subtype.toMonoidHom)))

private noncomputable abbrev gsolFinAdele (F : Type) [Field F] [NumberField F] (x : FiniteAdeleRing (𝓞 F) F) :
    AdeleRing (𝓞 F) F :=
  ((0 : InfiniteAdeleRing F), x)

private noncomputable scoped instance gsolFintypeLocalGaussFactor (F : Type) [Field F] [NumberField F]
    (𝔣 : Ideal (𝓞 F)) (𝔭 : AutomorphicForm.GaussTwist.modulusPrimes F 𝔣) :
    Fintype (AutomorphicForm.GaussTwist.LocalGaussFactor F 𝔣 𝔭.1) :=
  Fintype.ofFinite _

private theorem l0_top_ne_bot (F : Type) [Field F] [NumberField F] : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := by
  simp

private theorem l0_idealMultiplicity_bot (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    HeckeCharacter.idealMultiplicity F v ⊥ = 0 := by
  unfold HeckeCharacter.idealMultiplicity
  rw [← Ideal.zero_eq_bot, Associates.mk_zero, Associates.factors_zero]
  unfold Associates.count
  split_ifs <;> rfl

private theorem l0_idealMultiplicity_top (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    HeckeCharacter.idealMultiplicity F v ⊤ = 0 := by
  unfold HeckeCharacter.idealMultiplicity
  rw [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
  by_cases hp : Irreducible (Associates.mk v.asIdeal)
  · exact Associates.count_zero hp
  · rw [Associates.count_reducible hp]; rfl

private theorem l0_admitsModulus_bot_iff_top (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :
    HeckeCharacter.AdmitsModulus F η ⊥ ↔ HeckeCharacter.AdmitsModulus F η ⊤ := by
  simp only [HeckeCharacter.AdmitsModulus, l0_idealMultiplicity_bot, l0_idealMultiplicity_top]

private theorem l0_exists_nonzero_modulus (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F)) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) :
    ∃ 𝔣' : Ideal (𝓞 F), 𝔣' ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus F η 𝔣' := by
  by_cases h : 𝔣 = ⊥
  · subst h
    exact ⟨⊤, l0_top_ne_bot F, (l0_admitsModulus_bot_iff_top F η).mp hmod⟩
  · exact ⟨𝔣, h, hmod⟩

private theorem leg_L0_nonzero_modulus (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F)) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) :
    ∃ 𝔣' : Ideal (𝓞 F), 𝔣' ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus F η 𝔣' := by
  exact l0_exists_nonzero_modulus F η 𝔣 hmod

section GSolL6bSpan

open IsDedekindDomain NumberField.AdelicLevel AutomorphicForm.GaussTwist NumberField.StandardAddChar

variable (F : Type) [Field F] [NumberField F]

private noncomputable def l6b_placeUnitIdele (𝔭 : HeightOneSpectrum (𝓞 F))
    (t : (𝔭.adicCompletionIntegers F)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F 𝔭
    (Units.map (𝔭.adicCompletionIntegers F).subtype.toMonoidHom t))

private theorem l6b_gsolEtaLoc_apply (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 F))
    (t : (𝔭.adicCompletionIntegers F)ˣ) : gsolEtaLoc F η 𝔭 t = η (l6b_placeUnitIdele F 𝔭 t) := rfl

private theorem l6b_unitIdele_eq_prod (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ) :
    unitIdele F 𝔣 r = ∏ 𝔭 : modulusPrimes F 𝔣, l6b_placeUnitIdele F 𝔭.1 (r 𝔭) := by
  unfold unitIdele l6b_placeUnitIdele
  rw [map_prod]
  exact Finset.prod_congr rfl fun 𝔭 _ =>
    congrArg (fun t => Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F 𝔭.1 t)) (Units.ext rfl)

private theorem l6b_gaussUnitIdele_eq_prod (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) :
    gaussUnitIdele F 𝔣 u
      = ∏ 𝔭 : modulusPrimes F 𝔣, l6b_placeUnitIdele F 𝔭.1 (gaussRep F 𝔣 u 𝔭) := by
  unfold gaussUnitIdele l6b_placeUnitIdele
  rw [map_prod]
  exact Finset.prod_congr rfl fun 𝔭 _ =>
    congrArg (fun t => Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F 𝔭.1 t)) (Units.ext rfl)

private theorem l6b_gaussWt_eq_prod (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    (u : GaussIndex F 𝔣) :
    gaussWt F η 𝔣 u
      = ∏ 𝔭 : modulusPrimes F 𝔣,
          ((gsolEtaLoc F η 𝔭.1 (unitQuotLift (𝔭.1.adicCompletionIntegers F)
              (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣) (u 𝔭)) : ℂˣ) : ℂ) := by
  unfold gaussWt
  rw [l6b_gaussUnitIdele_eq_prod, map_prod, Units.coe_prod]
  rfl

private theorem l6b_sum_apply {ι : Type} (s : Finset ι) (f : ι → FiniteAdeleRing (𝓞 F) F)
    (w : HeightOneSpectrum (𝓞 F)) : (∑ i ∈ s, f i) w = ∑ i ∈ s, f i w := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ← ih]; rfl

private theorem l6b_adeleOn_eq_sum (S : Finset (HeightOneSpectrum (𝓞 F)))
    (y : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) :
    adeleOn S y = ∑ w ∈ S, finAdeleSingleAt F w (y w) := by
  refine FiniteAdeleRing.ext F fun v => ?_
  rw [l6b_sum_apply]
  show (if v ∈ S then y v else 0) = _
  by_cases hv : v ∈ S
  · rw [if_pos hv, Finset.sum_eq_single v (fun w _ hw => finAdeleSingleAt_apply_of_ne F w (y w) hw.symm)
      (fun h => (h hv).elim), finAdeleSingleAt_apply_self]
  · rw [if_neg hv]
    exact (Finset.sum_eq_zero fun w hw =>
      finAdeleSingleAt_apply_of_ne F w (y w) (fun h => hv (by subst h; exact hw))).symm

private theorem l6b_stdAddChar_sum {ι : Type} (s : Finset ι) (f : ι → AdeleRing (𝓞 F) F) :
    stdAddChar F (∑ i ∈ s, f i) = ∏ i ∈ s, stdAddChar F (f i) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact AddChar.map_zero_eq_one _
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, AddChar.map_add_eq_mul, ih]

private theorem l6b_stdAddChar_zero_adeleOn (S : Finset (HeightOneSpectrum (𝓞 F)))
    (y : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) :
    stdAddChar F (gsolFinAdele F (adeleOn S y)) = ∏ w ∈ S, psiLocal F w (y w) := by
  rw [l6b_adeleOn_eq_sum]
  have h : gsolFinAdele F (∑ w ∈ S, finAdeleSingleAt F w (y w)) = ∑ w ∈ S, adeleSingleAt F w (y w) := by
    show AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
        (∑ w ∈ S, finAdeleSingleAt F w (y w)) = _
    rw [map_sum]
    rfl
  rw [h, l6b_stdAddChar_sum]
  rfl

private theorem l6b_mul_adeleOn (S : Finset (HeightOneSpectrum (𝓞 F))) (c : FiniteAdeleRing (𝓞 F) F)
    (y : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) :
    c * adeleOn S y = adeleOn S (fun w => c w * y w) := by
  refine FiniteAdeleRing.ext F fun v => ?_
  show c v * (if v ∈ S then y v else 0) = (if v ∈ S then c v * y v else 0)
  split_ifs <;> simp

private theorem l6b_scale (α : F) (tf : FiniteAdeleRing (𝓞 F) F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (y : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) :
    algebraMap F (AdeleRing (𝓞 F) F) α * gsolFinAdele F (tf * adeleOn S y)
      = gsolFinAdele F (adeleOn S (fun w => (algebraMap F (w.adicCompletion F) α * tf w) * y w)) := by
  refine Prod.ext (mul_zero _) ?_
  show algebraMap F (FiniteAdeleRing (𝓞 F) F) α * (tf * adeleOn S y) = _
  rw [← mul_assoc, l6b_mul_adeleOn]
  rfl

private theorem l6b_gaussY_coe (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) (𝔭 : modulusPrimes F 𝔣) :
    gaussY F 𝔣 u 𝔭.1
      = (((unitQuotLift (𝔭.1.adicCompletionIntegers F) (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣) (u 𝔭) :
            (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F) : 𝔭.1.adicCompletion F)
          * (gaussUnif F 𝔭.1)⁻¹ ^ HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣 := by
  unfold gaussY
  rw [dif_pos 𝔭.2]
  rfl

private theorem l6b_summand (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣₀ : Ideal (𝓞 F)) (α : F)
    (tf : FiniteAdeleRing (𝓞 F) F) (u : GaussIndex F 𝔣₀) :
    gaussWt F η 𝔣₀ u *
        stdAddChar F (algebraMap F (AdeleRing (𝓞 F) F) α *
          gsolFinAdele F (tf * adeleOn (modulusPrimes F 𝔣₀) (gaussY F 𝔣₀ u)))
      = ∏ 𝔭 : modulusPrimes F 𝔣₀,
          (((gsolEtaLoc F η 𝔭.1 (unitQuotLift (𝔭.1.adicCompletionIntegers F)
                (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀) (u 𝔭)) : ℂˣ) : ℂ) *
            psiLocal F 𝔭.1 ((algebraMap F (𝔭.1.adicCompletion F) α * tf 𝔭.1) *
              ((((unitQuotLift (𝔭.1.adicCompletionIntegers F)
                    (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀) (u 𝔭) :
                    (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F) :
                    𝔭.1.adicCompletion F) *
                (gaussUnif F 𝔭.1)⁻¹ ^ HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀))) := by
  rw [l6b_gaussWt_eq_prod, l6b_scale, l6b_stdAddChar_zero_adeleOn,
    ← Finset.prod_coe_sort (modulusPrimes F 𝔣₀), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun 𝔭 _ => ?_
  rw [l6b_gaussY_coe]

private theorem l6b_main (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣₀ : Ideal (𝓞 F)) (α : F)
    (tf : FiniteAdeleRing (𝓞 F) F) :
    ∑ u : GaussIndex F 𝔣₀,
        gaussWt F η 𝔣₀ u *
          stdAddChar F (algebraMap F (AdeleRing (𝓞 F) F) α *
            gsolFinAdele F (tf * adeleOn (modulusPrimes F 𝔣₀) (gaussY F 𝔣₀ u)))
      = ∏ 𝔭 : modulusPrimes F 𝔣₀,
          ∑ w : LocalGaussFactor F 𝔣₀ 𝔭.1,
            ((gsolEtaLoc F η 𝔭.1 (unitQuotLift (𝔭.1.adicCompletionIntegers F)
                (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀) w) : ℂˣ) : ℂ) *
              psiLocal F 𝔭.1 ((algebraMap F (𝔭.1.adicCompletion F) α * tf 𝔭.1) *
                ((((unitQuotLift (𝔭.1.adicCompletionIntegers F)
                      (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀) w :
                      (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F) :
                      𝔭.1.adicCompletion F) *
                  (gaussUnif F 𝔭.1)⁻¹ ^ HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀)) := by
  rw [Finset.sum_congr rfl fun u _ => l6b_summand F η 𝔣₀ α tf u, Fintype.prod_sum]

  exact Finset.sum_bij (fun u _ => u) (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => h)
    (fun x _ => ⟨x, Finset.mem_univ _, rfl⟩) (fun _ _ => rfl)

end GSolL6bSpan

section L1Pastes

open NumberField IsDedekindDomain NumberField.AdelicLevel
open AutomorphicForm.GaussTwist

section Local

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

private theorem integers_adicCompletionIntegers :
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Integers
      (v.adicCompletionIntegers K) :=
  Valuation.valuationSubring.integers _

private theorem valued_coe_eq_one_of_isUnit {x : v.adicCompletionIntegers K} (hx : IsUnit x) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
  (integers_adicCompletionIntegers K v).one_of_isUnit hx

private theorem isUnit_of_valued_coe_eq_one {x : v.adicCompletionIntegers K}
    (hx : Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) = 1) : IsUnit x :=
  (integers_adicCompletionIntegers K v).isUnit_of_one' hx

private theorem valued_units_coe (r : (v.adicCompletionIntegers K)ˣ) :
    Valued.v (((r : v.adicCompletionIntegers K) : v.adicCompletion K)) = 1 :=
  valued_coe_eq_one_of_isUnit K v r.isUnit

end Local

section Adelic

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

private theorem coe_prod_apply_of_units {ι : Type*} (s : Finset ι)
    (f : ι → (FiniteAdeleRing R K)ˣ) (w : HeightOneSpectrum R) :
    ((∏ i ∈ s, f i : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) w
      = ∏ i ∈ s, (((f i : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) w) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [coe_one_apply]
  | cons a s ha ih => simp only [Finset.prod_cons, Units.val_mul, coe_mul_apply, ih]

end Adelic

section Gauss

variable (F : Type) [Field F] [NumberField F]

open scoped Classical

private theorem unitIdele_fst (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ) :
    ((unitIdele F 𝔣 r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  rw [unitIdele, Units.coe_map]; exact finIncl_apply_fst (𝓞 F) F _

private theorem unitIdele_inv_fst (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ) :
    (((unitIdele F 𝔣 r)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  rw [unitIdele, ← map_inv, Units.coe_map]; exact finIncl_apply_fst (𝓞 F) F _

private theorem unitIdele_snd_apply_of_not_mem (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ modulusPrimes F 𝔣) :
    ((unitIdele F 𝔣 r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := by
  rw [unitIdele, Units.coe_map, finIncl_apply_snd, coe_prod_apply_of_units]
  exact Finset.prod_eq_one fun 𝔭 _ =>
    localUnit_apply_of_ne (𝓞 F) F 𝔭.1 _ (fun h => hw (h ▸ 𝔭.2))

private theorem unitIdele_snd_apply_of_mem (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ)
    {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : 𝔭 ∈ modulusPrimes F 𝔣) :
    ((unitIdele F 𝔣 r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 𝔭
      = (((r ⟨𝔭, h𝔭⟩ : (𝔭.adicCompletionIntegers F)ˣ)
            : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) := by
  rw [unitIdele, Units.coe_map, finIncl_apply_snd, coe_prod_apply_of_units]
  refine (Finset.prod_eq_single (⟨𝔭, h𝔭⟩ : modulusPrimes F 𝔣)
    (fun 𝔮 _ h𝔮 => localUnit_apply_of_ne (𝓞 F) F 𝔮.1 _ ?_)
    (fun h => absurd (Finset.mem_univ _) h)).trans ?_
  · exact fun h => h𝔮 (Subtype.ext h.symm)
  · exact localUnit_apply_self (𝓞 F) F 𝔭 _

private theorem inv_snd_apply_mul_snd_apply (x : (AdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w * (x : AdeleRing (𝓞 F) F).2 w = 1 := by
  have h : ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (x : AdeleRing (𝓞 F) F) = 1 :=
    x.inv_mul
  calc ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w * (x : AdeleRing (𝓞 F) F).2 w
      = (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (x : AdeleRing (𝓞 F) F)).2 w := rfl
    _ = (1 : AdeleRing (𝓞 F) F).2 w := by rw [h]
    _ = 1 := rfl

private theorem unitIdele_inv_snd_apply_of_not_mem (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ modulusPrimes F 𝔣) :
    (((unitIdele F 𝔣 r)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := by
  have h := inv_snd_apply_mul_snd_apply F (unitIdele F 𝔣 r) w
  rwa [unitIdele_snd_apply_of_not_mem F 𝔣 r hw, mul_one] at h

private theorem unitIdele_inv_snd_apply_of_mem (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ)
    {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : 𝔭 ∈ modulusPrimes F 𝔣) :
    (((unitIdele F 𝔣 r)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 𝔭
      = ((((r ⟨𝔭, h𝔭⟩ : (𝔭.adicCompletionIntegers F)ˣ)
            : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F))⁻¹ := by
  have h := inv_snd_apply_mul_snd_apply F (unitIdele F 𝔣 r) 𝔭
  rw [unitIdele_snd_apply_of_mem F 𝔣 r h𝔭] at h
  exact eq_inv_of_mul_eq_one_left h

end Gauss

end L1Pastes

section L1Core

open IsDedekindDomain NumberField.AdelicLevel AutomorphicForm.GaussTwist
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

private theorem l1_placeUnitIdele_fst (𝔭 : HeightOneSpectrum (𝓞 F)) (t : (𝔭.adicCompletionIntegers F)ˣ) :
    ((l6b_placeUnitIdele F 𝔭 t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  rw [l6b_placeUnitIdele, Units.coe_map]; exact finIncl_apply_fst (𝓞 F) F _

private theorem l1_placeUnitIdele_snd_self (𝔭 : HeightOneSpectrum (𝓞 F)) (t : (𝔭.adicCompletionIntegers F)ˣ) :
    ((l6b_placeUnitIdele F 𝔭 t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 𝔭
      = ((t : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) := by
  rw [l6b_placeUnitIdele, Units.coe_map, finIncl_apply_snd]; exact localUnit_apply_self (𝓞 F) F 𝔭 _

private theorem l1_placeUnitIdele_snd_of_ne (𝔭 : HeightOneSpectrum (𝓞 F)) (t : (𝔭.adicCompletionIntegers F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ 𝔭) :
    ((l6b_placeUnitIdele F 𝔭 t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := by
  rw [l6b_placeUnitIdele, Units.coe_map, finIncl_apply_snd]; exact localUnit_apply_of_ne (𝓞 F) F 𝔭 _ hw

variable (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)

private def L1TrivialAt (𝔭 : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Prop :=
  ∀ t : (𝔭.adicCompletionIntegers F)ˣ,
    Valued.v (((t : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) →
    gsolEtaLoc F η 𝔭 t = 1

variable (𝔣 : Ideal (𝓞 F))

private theorem l1_trivialAt_idealMultiplicity (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    (𝔭 : HeightOneSpectrum (𝓞 F)) : L1TrivialAt F η 𝔭 (HeckeCharacter.idealMultiplicity F 𝔭 𝔣) := by
  intro t ht
  rw [l6b_gsolEtaLoc_apply]
  refine hmod _ (l1_placeUnitIdele_fst F 𝔭 t) fun v => ?_
  by_cases hv : v = 𝔭
  · rw [hv, l1_placeUnitIdele_snd_self]
    exact ⟨valued_units_coe F 𝔭 t, ht⟩
  · rw [l1_placeUnitIdele_snd_of_ne F 𝔭 t hv]
    refine ⟨map_one _, ?_⟩
    rw [sub_self, map_zero]
    exact zero_le'

private theorem l1_exists_trivialAt (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    ∃ n : ℕ, L1TrivialAt F η 𝔭 n :=
  ⟨_, l1_trivialAt_idealMultiplicity F η 𝔣 hmod 𝔭⟩

private noncomputable def l1cond (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) (𝔭 : HeightOneSpectrum (𝓞 F)) : ℕ :=
  Nat.find (l1_exists_trivialAt F η 𝔣 hmod 𝔭)

private theorem l1_trivialAt_cond (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    L1TrivialAt F η 𝔭 (l1cond F η 𝔣 hmod 𝔭) :=
  Nat.find_spec (l1_exists_trivialAt F η 𝔣 hmod 𝔭)

private theorem l1_exists_ne_one_of_cond_pos (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {𝔭 : HeightOneSpectrum (𝓞 F)} (hc : 1 ≤ l1cond F η 𝔣 hmod 𝔭) :
    ∃ t : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((t : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-((l1cond F η 𝔣 hmod 𝔭 : ℤ) - 1)) ∧
        gsolEtaLoc F η 𝔭 t ≠ 1 := by
  have hlt : l1cond F η 𝔣 hmod 𝔭 - 1 < l1cond F η 𝔣 hmod 𝔭 := by omega
  have hnot : ¬ L1TrivialAt F η 𝔭 (l1cond F η 𝔣 hmod 𝔭 - 1) :=
    Nat.find_min (l1_exists_trivialAt F η 𝔣 hmod 𝔭) hlt
  have hcast : ((l1cond F η 𝔣 hmod 𝔭 - 1 : ℕ) : ℤ) = (l1cond F η 𝔣 hmod 𝔭 : ℤ) - 1 := by omega
  by_contra hcon
  refine hnot fun t ht => ?_
  by_contra hne
  refine hcon ⟨t, ?_, hne⟩
  rw [← hcast]
  exact ht

private theorem l1_idealMultiplicity_eq_zero (𝔣' : Ideal (𝓞 F)) (h𝔣' : 𝔣' ≠ ⊥) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ modulusPrimes F 𝔣') : HeckeCharacter.idealMultiplicity F v 𝔣' = 0 := by
  have h0 : 𝔣' ≠ 0 := by rw [Ideal.zero_eq_bot]; exact h𝔣'
  by_contra hne
  exact hv ((mem_modulusPrimes F h𝔣' v).mpr ((Associates.count_ne_zero_iff_dvd h0 v.irreducible).mp hne))

omit [NumberField F] in
private theorem l1_pow_ne_zero (k : HeightOneSpectrum (𝓞 F) → ℕ) (q : HeightOneSpectrum (𝓞 F)) :
    q.asIdeal ^ k q ≠ 0 := by
  have hq : q.asIdeal ≠ 0 := by rw [Ideal.zero_eq_bot]; exact q.ne_bot
  exact pow_ne_zero _ hq

omit [NumberField F] in
private theorem l1_prod_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) → ℕ) :
    (∏ q ∈ S, q.asIdeal ^ k q) ≠ 0 := by
  induction S using Finset.cons_induction with
  | empty =>
      rw [Finset.prod_empty, Ideal.one_eq_top, Ideal.zero_eq_bot]
      simp
  | cons a S ha ih =>
      rw [Finset.prod_cons]
      exact mul_ne_zero (l1_pow_ne_zero F k a) ih

private theorem l1_count_prod (S : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) → ℕ)
    (𝔭 : HeightOneSpectrum (𝓞 F)) :
    (Associates.mk 𝔭.asIdeal).count (Associates.mk (∏ q ∈ S, q.asIdeal ^ k q)).factors
      = if 𝔭 ∈ S then k 𝔭 else 0 := by
  induction S using Finset.cons_induction with
  | empty =>
      rw [Finset.prod_empty, Associates.mk_one, Associates.factors_one, if_neg (Finset.notMem_empty 𝔭)]
      exact Associates.count_zero 𝔭.associates_irreducible
  | cons a S ha ih =>
      rw [Finset.prod_cons, ← Associates.mk_mul_mk,
        Associates.count_mul (Associates.mk_ne_zero.mpr (l1_pow_ne_zero F k a))
          (Associates.mk_ne_zero.mpr (l1_prod_ne_zero F S k)) 𝔭.associates_irreducible,
        ih, Associates.mk_pow,
        Associates.count_pow (Associates.mk_ne_zero.mpr (by rw [Ideal.zero_eq_bot]; exact a.ne_bot))
          𝔭.associates_irreducible]
      by_cases h : 𝔭 = a
      · rw [h, Associates.count_self a.associates_irreducible, if_neg ha, if_pos (Finset.mem_cons.mpr (Or.inl rfl)),
          mul_one, add_zero]
      · have hne : Associates.mk 𝔭.asIdeal ≠ Associates.mk a.asIdeal := fun heq =>
          h (HeightOneSpectrum.ext (associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp heq)))
        rw [Associates.count_eq_zero_of_ne 𝔭.associates_irreducible a.associates_irreducible hne, mul_zero,
          zero_add]
        by_cases hS : 𝔭 ∈ S
        · rw [if_pos hS, if_pos (Finset.mem_cons.mpr (Or.inr hS))]
        · rw [if_neg hS, if_neg (fun hm => (Finset.mem_cons.mp hm).elim h hS)]

end L1Core

section L1Legs

open IsDedekindDomain NumberField.AdelicLevel AutomorphicForm.GaussTwist

private theorem l1_leg_conductor (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣' : Ideal (𝓞 F)) (h𝔣' : 𝔣' ≠ ⊥)
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣') :
    ∃ cexp : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ,
      (∀ 𝔭 ∈ AutomorphicForm.GaussTwist.modulusPrimes F 𝔣', ∀ r : (𝔭.adicCompletionIntegers F)ˣ,
          Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
              ≤ WithZero.exp (-(cexp 𝔭 : ℤ)) →
            gsolEtaLoc F η 𝔭 r = 1) ∧
      (∀ 𝔭 ∈ AutomorphicForm.GaussTwist.modulusPrimes F 𝔣', 1 ≤ cexp 𝔭 →
          ∃ r : (𝔭.adicCompletionIntegers F)ˣ,
            Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
                ≤ WithZero.exp (-((cexp 𝔭 : ℤ) - 1)) ∧
              gsolEtaLoc F η 𝔭 r ≠ 1) := by
  have _ := h𝔣'
  exact ⟨l1cond F η 𝔣' hmod, fun 𝔭 _ r hr => l1_trivialAt_cond F η 𝔣' hmod 𝔭 r hr,
    fun 𝔭 _ hc => l1_exists_ne_one_of_cond_pos F η 𝔣' hmod hc⟩

private theorem l1_leg_admits (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣' : Ideal (𝓞 F)) (h𝔣' : 𝔣' ≠ ⊥)
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣')
    (cexp : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ)
    (htriv : ∀ 𝔭 ∈ AutomorphicForm.GaussTwist.modulusPrimes F 𝔣', ∀ r : (𝔭.adicCompletionIntegers F)ˣ,
        Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
            ≤ WithZero.exp (-(cexp 𝔭 : ℤ)) →
          gsolEtaLoc F η 𝔭 r = 1)
    (𝔣₀ : Ideal (𝓞 F))
    (hle : ∀ 𝔭 ∈ AutomorphicForm.GaussTwist.modulusPrimes F 𝔣',
        cexp 𝔭 ≤ HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀) :
    HeckeCharacter.AdmitsModulus F η 𝔣₀ := by
  intro u hu1 hu

  have hxmem : ∀ 𝔭 : modulusPrimes F 𝔣',
      (u : AdeleRing (𝓞 F) F).2 𝔭.1 ∈ 𝔭.1.adicCompletionIntegers F := fun 𝔭 =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hu 𝔭.1).1.le
  have hxunit : ∀ 𝔭 : modulusPrimes F 𝔣',
      IsUnit (⟨(u : AdeleRing (𝓞 F) F).2 𝔭.1, hxmem 𝔭⟩ : 𝔭.1.adicCompletionIntegers F) := fun 𝔭 =>
    isUnit_of_valued_coe_eq_one F 𝔭.1 (hu 𝔭.1).1
  let r : ∀ 𝔭 : modulusPrimes F 𝔣', (𝔭.1.adicCompletionIntegers F)ˣ := fun 𝔭 => (hxunit 𝔭).unit
  have hr : ∀ 𝔭 : modulusPrimes F 𝔣',
      (((r 𝔭 : (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F) : 𝔭.1.adicCompletion F)
        = (u : AdeleRing (𝓞 F) F).2 𝔭.1 := fun 𝔭 => congrArg Subtype.val (hxunit 𝔭).unit_spec
  have hsplit : u = u * (unitIdele F 𝔣' r)⁻¹ * unitIdele F 𝔣' r := (inv_mul_cancel_right u _).symm

  have hright : η (unitIdele F 𝔣' r) = 1 := by
    rw [l6b_unitIdele_eq_prod, map_prod]
    refine Finset.prod_eq_one fun 𝔭 _ => ?_
    rw [← l6b_gsolEtaLoc_apply]
    refine htriv 𝔭.1 𝔭.2 (r 𝔭) ?_
    rw [hr 𝔭]
    exact (hu 𝔭.1).2.trans (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast hle 𝔭.1 𝔭.2)))

  have hleft : η (u * (unitIdele F 𝔣' r)⁻¹) = 1 := by
    refine hmod _ ?_ fun v => ?_
    ·

      have h1 : ((u * (unitIdele F 𝔣' r)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1
          = (u : AdeleRing (𝓞 F) F).1
              * (((unitIdele F 𝔣' r)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 := rfl
      rw [h1, hu1, unitIdele_inv_fst F 𝔣' r, one_mul]
    · have h2 : ((u * (unitIdele F 𝔣' r)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
          = (u : AdeleRing (𝓞 F) F).2 v
              * (((unitIdele F 𝔣' r)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v := rfl
      rw [h2]
      by_cases hv : v ∈ modulusPrimes F 𝔣'
      · rw [unitIdele_inv_snd_apply_of_mem F 𝔣' r hv, hr ⟨v, hv⟩]
        have hne : (u : AdeleRing (𝓞 F) F).2 v ≠ 0 := fun h0 => by
          have h1 := (hu v).1
          rw [h0, map_zero] at h1
          exact zero_ne_one h1
        rw [mul_inv_cancel₀ hne]
        refine ⟨map_one _, ?_⟩
        rw [sub_self, map_zero]
        exact zero_le'
      · rw [unitIdele_inv_snd_apply_of_not_mem F 𝔣' r hv, mul_one, l1_idealMultiplicity_eq_zero F 𝔣' h𝔣' hv]
        refine ⟨(hu v).1, ?_⟩
        rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
        refine (Valuation.map_sub _ _ _).trans ?_
        rw [(hu v).1, map_one, max_self]
  rw [hsplit, map_mul, hleft, hright, mul_one]

private theorem l1_leg_arith (F : Type) [Field F] [NumberField F]
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (k : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ) (hk : ∀ 𝔭 ∈ S₀, 1 ≤ k 𝔭) :
    (∏ 𝔭 ∈ S₀, 𝔭.asIdeal ^ k 𝔭) ≠ ⊥ ∧
      AutomorphicForm.GaussTwist.modulusPrimes F (∏ 𝔭 ∈ S₀, 𝔭.asIdeal ^ k 𝔭) = S₀ ∧
      ∀ 𝔭 ∈ S₀, HeckeCharacter.idealMultiplicity F 𝔭 (∏ 𝔭 ∈ S₀, 𝔭.asIdeal ^ k 𝔭) = k 𝔭 := by
  have h0 : (∏ 𝔭 ∈ S₀, 𝔭.asIdeal ^ k 𝔭) ≠ 0 := l1_prod_ne_zero F S₀ k
  have hbot : (∏ 𝔭 ∈ S₀, 𝔭.asIdeal ^ k 𝔭) ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact h0
  refine ⟨hbot, ?_, fun 𝔭 h𝔭 => ?_⟩
  · ext 𝔭
    rw [mem_modulusPrimes F hbot]
    constructor
    · intro hdvd
      have hcount := (Associates.count_ne_zero_iff_dvd h0 𝔭.irreducible).mpr hdvd
      rw [l1_count_prod F S₀ k 𝔭] at hcount
      by_contra hnot
      exact hcount (if_neg hnot)
    · intro h𝔭
      exact (dvd_pow_self 𝔭.asIdeal (by have := hk 𝔭 h𝔭; omega)).trans (Finset.dvd_prod_of_mem _ h𝔭)
  · unfold HeckeCharacter.idealMultiplicity
    rw [l1_count_prod F S₀ k 𝔭, if_pos h𝔭]

end L1Legs

private theorem leg_L1_conductor (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣' : Ideal (𝓞 F)) (h𝔣' : 𝔣' ≠ ⊥)
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣') :
    ∃ cexp : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ,
      (∀ 𝔭 ∈ AutomorphicForm.GaussTwist.modulusPrimes F 𝔣', ∀ r : (𝔭.adicCompletionIntegers F)ˣ,
          Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
              ≤ WithZero.exp (-(cexp 𝔭 : ℤ)) →
            gsolEtaLoc F η 𝔭 r = 1) ∧
      (∀ 𝔭 ∈ AutomorphicForm.GaussTwist.modulusPrimes F 𝔣', 1 ≤ cexp 𝔭 →
          ∃ r : (𝔭.adicCompletionIntegers F)ˣ,
            Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
                ≤ WithZero.exp (-((cexp 𝔭 : ℤ) - 1)) ∧
              gsolEtaLoc F η 𝔭 r ≠ 1) := by
  exact l1_leg_conductor F η 𝔣' h𝔣' hmod

private theorem leg_L1b_admits (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣' : Ideal (𝓞 F)) (h𝔣' : 𝔣' ≠ ⊥)
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣')
    (cexp : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ)
    (htriv : ∀ 𝔭 ∈ AutomorphicForm.GaussTwist.modulusPrimes F 𝔣', ∀ r : (𝔭.adicCompletionIntegers F)ˣ,
        Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
            ≤ WithZero.exp (-(cexp 𝔭 : ℤ)) →
          gsolEtaLoc F η 𝔭 r = 1)
    (𝔣₀ : Ideal (𝓞 F))
    (hle : ∀ 𝔭 ∈ AutomorphicForm.GaussTwist.modulusPrimes F 𝔣',
        cexp 𝔭 ≤ HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀) :
    HeckeCharacter.AdmitsModulus F η 𝔣₀ := by
  exact l1_leg_admits F η 𝔣' h𝔣' hmod cexp htriv 𝔣₀ hle

private theorem leg_L1b_arith (F : Type) [Field F] [NumberField F]
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (k : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ) (hk : ∀ 𝔭 ∈ S₀, 1 ≤ k 𝔭) :
    (∏ 𝔭 ∈ S₀, 𝔭.asIdeal ^ k 𝔭) ≠ ⊥ ∧
      AutomorphicForm.GaussTwist.modulusPrimes F (∏ 𝔭 ∈ S₀, 𝔭.asIdeal ^ k 𝔭) = S₀ ∧
      ∀ 𝔭 ∈ S₀, HeckeCharacter.idealMultiplicity F 𝔭 (∏ 𝔭 ∈ S₀, 𝔭.asIdeal ^ k 𝔭) = k 𝔭 := by
  exact l1_leg_arith F S₀ k hk

namespace GsolL2

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm

private theorem l2_approx (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (A : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F))
    (hA : ∀ v, A v ∈ nhds (t v)) :
    ∃ x : F, ∀ v ∈ S, algebraMap F (v.adicCompletion F) x ∈ A v := by
  have hd := NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi (K := F) S
  have hd' := (Prod.fst_surjective.denseRange).comp hd continuous_fst
  have hmem : Set.pi Set.univ (fun w : S => A w.1) ∈ nhds (fun w : S => t w.1) :=
    set_pi_mem_nhds Set.finite_univ (fun w _ => hA w.1)
  obtain ⟨x, hx⟩ := hd'.mem_nhds hmem
  have hx' : ∀ w : S, algebraMap F (w.1.adicCompletion F) x ∈ A w.1 := fun w =>
    Set.mem_univ_pi.1 hx w
  exact ⟨x, fun v hv => hx' ⟨v, hv⟩⟩

private theorem l2_exists_gl (F : Type) [Field F] (r₀ r₁ : F) (hr : r₀ ≠ 0 ∨ r₁ ≠ 0) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) F,
      (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = r₀ ∧ (γ : Matrix (Fin 2) (Fin 2) F) 1 1 = r₁ := by
  by_cases h1 : r₁ = 0
  · have h0 : r₀ ≠ 0 := by
      rcases hr with h | h
      · exact h
      · exact absurd h1 h
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; r₀, r₁] ?_, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simpa [h1] using h0
    · simp
    · simp
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; r₀, r₁] ?_, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simpa using h1
    · simp
    · simp

private theorem l2_kill (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (b : WithZero (Multiplicative ℤ)) (e₀ e₁ : v.adicCompletion F)
    (h₀ : Valued.v e₀ ≤ b) (h₁ : Valued.v e₁ = 1) :
    ∃ y : v.adicCompletion F, Valued.v y ≤ b ∧ e₀ + e₁ * y = 0 := by
  have he₁ : e₁ ≠ 0 := by
    intro h
    rw [h, map_zero] at h₁
    exact zero_ne_one h₁
  refine ⟨-(e₀ / e₁), ?_, ?_⟩
  · rw [Valuation.map_neg, Valuation.map_div, h₁, div_one]
    exact h₀
  · rw [mul_neg, mul_div_cancel₀ e₀ he₁, add_neg_cancel]

private noncomputable def l2_rowMap (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
    (p : v.adicCompletion F × v.adicCompletion F) : v.adicCompletion F × v.adicCompletion F :=
  (p.1 * M 0 0 + p.2 * M 1 0, p.1 * M 0 1 + p.2 * M 1 1)

private theorem l2_continuous_rowMap (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) :
    Continuous (l2_rowMap F v M) := by
  unfold l2_rowMap
  fun_prop

private theorem l2_local (F : Type) [Field F] [NumberField F] {N : Ideal (𝓞 F)} (hN : N ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) (M Mi : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
    (hMi : Mi * M = 1) :
    ∃ t₀ t₁ : v.adicCompletion F, ∃ A₀ ∈ nhds t₀, ∃ A₁ ∈ nhds t₁, ∀ p₀ ∈ A₀, ∀ p₁ ∈ A₁,
      Valued.v (p₀ * M 0 1 + p₁ * M 1 1) = 1 ∧
      ∃ y : v.adicCompletion F, Valued.v y ≤ idealBound (𝓞 F) N v ∧
        (p₀ * M 0 0 + p₁ * M 1 0) + (p₀ * M 0 1 + p₁ * M 1 1) * y = 0 := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp_neg (K := F) v 1
  have hA : IsOpen {z : v.adicCompletion F | Valued.v z ≤ idealBound (𝓞 F) N v} :=
    isOpen_setOf_valued_le_idealBound (K := F) v hN
  have hB : IsOpen ((fun z : v.adicCompletion F => z - 1) ⁻¹'
      {z : v.adicCompletion F | Valued.v z ≤ Valued.v t}) :=
    (continuous_id.sub continuous_const).isOpen_preimage _ (isOpen_setOf_valued_le v t ht)
  have hne : (1 : Fin 2) ≠ 0 := by decide
  have h0 : Mi 1 0 * M 0 0 + Mi 1 1 * M 1 0 = 0 := by
    have h := congrFun (congrFun hMi 1) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne hne] at h
  have h1 : Mi 1 0 * M 0 1 + Mi 1 1 * M 1 1 = 1 := by
    have h := congrFun (congrFun hMi 1) 1
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
  have hΦt : l2_rowMap F v M (Mi 1 0, Mi 1 1) = (0, 1) := Prod.ext h0 h1
  have hW : ({z : v.adicCompletion F | Valued.v z ≤ idealBound (𝓞 F) N v} ×ˢ
      ((fun z : v.adicCompletion F => z - 1) ⁻¹' {z : v.adicCompletion F | Valued.v z ≤ Valued.v t}))
      ∈ nhds (l2_rowMap F v M (Mi 1 0, Mi 1 1)) := by
    rw [hΦt]
    refine prod_mem_nhds (hA.mem_nhds ?_) (hB.mem_nhds ?_)
    · show Valued.v (0 : v.adicCompletion F) ≤ idealBound (𝓞 F) N v
      rw [map_zero]
      exact zero_le'
    · show Valued.v ((1 : v.adicCompletion F) - 1) ≤ Valued.v t
      rw [sub_self, map_zero]
      exact zero_le'
  have hpre := ((l2_continuous_rowMap F v M).continuousAt (x := (Mi 1 0, Mi 1 1))).preimage_mem_nhds hW
  rw [mem_nhds_prod_iff] at hpre
  obtain ⟨A₀, hA₀, A₁, hA₁, hsub⟩ := hpre
  refine ⟨Mi 1 0, Mi 1 1, A₀, hA₀, A₁, hA₁, fun p₀ hp₀ p₁ hp₁ => ?_⟩
  have hp : l2_rowMap F v M (p₀, p₁) ∈ {z : v.adicCompletion F | Valued.v z ≤ idealBound (𝓞 F) N v} ×ˢ
      ((fun z : v.adicCompletion F => z - 1) ⁻¹' {z : v.adicCompletion F | Valued.v z ≤ Valued.v t}) :=
    hsub (Set.mk_mem_prod hp₀ hp₁)
  obtain ⟨he₀, he₁⟩ := hp
  have he₀' : Valued.v (p₀ * M 0 0 + p₁ * M 1 0) ≤ idealBound (𝓞 F) N v := he₀
  have he₁' : Valued.v ((p₀ * M 0 1 + p₁ * M 1 1) - 1) ≤ Valued.v t := he₁
  have hlt : Valued.v ((p₀ * M 0 1 + p₁ * M 1 1) - 1) < Valued.v (1 : v.adicCompletion F) := by
    rw [map_one]
    refine lt_of_le_of_lt he₁' ?_
    rw [hvt]
    exact (WithZero.exp_lt_exp.2 (by norm_num : (-((1 : ℕ) : ℤ)) < 0)).trans_eq WithZero.exp_zero
  have hone : Valued.v (p₀ * M 0 1 + p₁ * M 1 1) = 1 := by
    have h := Valuation.map_add_eq_of_lt_right Valued.v hlt
    rwa [sub_add_cancel, map_one] at h
  exact ⟨hone, l2_kill F v _ _ _ he₀' hone⟩

private theorem l2_pick (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (P : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → Prop)
    (h : ∀ v ∈ S, ∃ y : v.adicCompletion F, P v y) :
    ∃ y : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F, ∀ v ∈ S, P v (y v) := by
  classical
  refine ⟨fun v => if hv : v ∈ S then (h v hv).choose else 0, fun v hv => ?_⟩
  simp only [dif_pos hv]
  exact (h v hv).choose_spec

private theorem l2_adeleOn_apply (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) (w : HeightOneSpectrum (𝓞 F)) :
    GaussTwist.adeleOn S y w = if w ∈ S then y w else 0 := rfl

private theorem l2_adeleOn_apply_of_mem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∈ S) : GaussTwist.adeleOn S y w = y w := by
  rw [l2_adeleOn_apply, if_pos hw]

private theorem l2_adeleOn_mem_idealBall (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F)
    (hy : ∀ w ∈ S, Valued.v (y w) ≤ idealBound (𝓞 F) N w) :
    GaussTwist.adeleOn S y ∈ idealBall (𝓞 F) F N := fun w => by
  by_cases hw : w ∈ S
  · rw [l2_adeleOn_apply, if_pos hw]
    exact hy w hw
  · rw [l2_adeleOn_apply, if_neg hw, map_zero]
    exact zero_le'

private theorem l2_neg_mem_idealBall (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F))
    (x : FiniteAdeleRing (𝓞 F) F) (hx : x ∈ idealBall (𝓞 F) F N) :
    -x ∈ idealBall (𝓞 F) F N := fun w => by
  rw [coe_neg_apply, Valuation.map_neg]
  exact hx w

private theorem l2_lower_mul_lower (F : Type) [Field F] [NumberField F]
    (x y : FiniteAdeleRing (𝓞 F) F) :
    (!![1, 0; x, 1] : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) * !![1, 0; y, 1]
      = !![1, 0; x + y, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private noncomputable def l2_lowerUnip (F : Type) [Field F] [NumberField F]
    (x : FiniteAdeleRing (𝓞 F) F) : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F) where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by rw [l2_lower_mul_lower, add_neg_cancel, Matrix.one_fin_two]
  inv_val := by rw [l2_lower_mul_lower, neg_add_cancel, Matrix.one_fin_two]

private theorem l2_isLevelOne (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F))
    (y : FiniteAdeleRing (𝓞 F) F) (hy : y ∈ idealBall (𝓞 F) F N) :
    IsLevelOneMatrix (𝓞 F) F N !![1, 0; y, 1] where
  integral := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using one_mem_integralFiniteAdeles (R := 𝓞 F) (K := F)
    · simpa using zero_mem_integralFiniteAdeles (R := 𝓞 F) (K := F)
    · simpa using idealBall_subset_integralFiniteAdeles N hy
    · simpa using one_mem_integralFiniteAdeles (R := 𝓞 F) (K := F)
  lowerLeft := by simpa using hy
  lowerRight := by simpa using zero_mem_idealBall (R := 𝓞 F) (K := F) N

private theorem l2_glFin_finLift (F : Type) [Field F] [NumberField F]
    (h : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glFin (𝓞 F) F (GaussTwist.finLift h) = h := by
  ext i j
  rfl

private theorem l2_glArch_finLift (F : Type) [Field F] [NumberField F]
    (h : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glArch (𝓞 F) F (GaussTwist.finLift h) = 1 := by
  ext i j
  rw [Units.val_one]
  rfl

private theorem l2_finLift_lowerUnip_mem (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F))
    (x : FiniteAdeleRing (𝓞 F) F) (hx : x ∈ idealBall (𝓞 F) F N) :
    GaussTwist.finLift (l2_lowerUnip F x) ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, l2_glFin_finLift, mem_finiteLevelOne_iff]
    exact ⟨l2_isLevelOne F N x hx, l2_isLevelOne F N (-x) (l2_neg_mem_idealBall F N x hx)⟩
  · rw [mem_finiteAdelicGL2Subgroup_iff]
    exact l2_glArch_finLift F _

private theorem l2_comp_globalPoints (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (γ : Matrix.GeneralLinearGroup (Fin 2) F) (i j : Fin 2) :
    (finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      = algebraMap F (v.adicCompletion F) ((γ : Matrix (Fin 2) (Fin 2) F) i j) := rfl

private theorem l2_comp_lowerUnip_zero_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : FiniteAdeleRing (𝓞 F) F) :
    (finComponent (𝓞 F) F v (glFin (𝓞 F) F (GaussTwist.finLift (l2_lowerUnip F x))) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 = 1 := rfl

private theorem l2_comp_lowerUnip_one_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : FiniteAdeleRing (𝓞 F) F) :
    (finComponent (𝓞 F) F v (glFin (𝓞 F) F (GaussTwist.finLift (l2_lowerUnip F x))) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = x v := rfl

private theorem l2_entry (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g₀ : AdelicGL2 (𝓞 F) F) (x : FiniteAdeleRing (𝓞 F) F) :
    ((((globalPoints (𝓞 F) F γ * (g₀ * GaussTwist.finLift (l2_lowerUnip F x)) : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) v
      = (algebraMap F (v.adicCompletion F) ((γ : Matrix (Fin 2) (Fin 2) F) 1 0)
            * (finComponent (𝓞 F) F v (glFin (𝓞 F) F g₀) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0
          + algebraMap F (v.adicCompletion F) ((γ : Matrix (Fin 2) (Fin 2) F) 1 1)
            * (finComponent (𝓞 F) F v (glFin (𝓞 F) F g₀) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0)
        + (algebraMap F (v.adicCompletion F) ((γ : Matrix (Fin 2) (Fin 2) F) 1 0)
            * (finComponent (𝓞 F) F v (glFin (𝓞 F) F g₀) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1
          + algebraMap F (v.adicCompletion F) ((γ : Matrix (Fin 2) (Fin 2) F) 1 1)
            * (finComponent (𝓞 F) F v (glFin (𝓞 F) F g₀) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1)
          * x v := by
  show (finComponent (𝓞 F) F v (glFin (𝓞 F) F
      (globalPoints (𝓞 F) F γ * (g₀ * GaussTwist.finLift (l2_lowerUnip F x)))) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = _
  simp only [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, l2_comp_globalPoints,
    l2_comp_lowerUnip_zero_zero, l2_comp_lowerUnip_one_zero]
  ring

private theorem l2_main (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hright : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      φ (g * k) = φ g)
    (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0) :
    ∃ m : AdelicGL2 (𝓞 F) F, φ m ≠ 0 ∧
      ∀ 𝔭 ∈ S₀, (((m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) 𝔭 = 0 := by
  classical
  rcases S₀.eq_empty_or_nonempty with hS | ⟨𝔮, h𝔮⟩
  · exact ⟨g₀, hg₀, fun 𝔭 h𝔭 => by simp [hS] at h𝔭⟩
  have hloc := fun v : HeightOneSpectrum (𝓞 F) =>
    l2_local F hN v _ _ (Units.inv_mul (finComponent (𝓞 F) F v (glFin (𝓞 F) F g₀)))
  choose t₀ t₁ A₀ hA₀ A₁ hA₁ hAB using hloc
  obtain ⟨r₀, hr₀⟩ := l2_approx F S₀ t₀ A₀ hA₀
  obtain ⟨r₁, hr₁⟩ := l2_approx F S₀ t₁ A₁ hA₁
  have hex := fun v (hv : v ∈ S₀) => hAB v _ (hr₀ v hv) _ (hr₁ v hv)
  have hr : r₀ ≠ 0 ∨ r₁ ≠ 0 := by
    rcases eq_or_ne r₀ 0 with h0 | h0
    · rcases eq_or_ne r₁ 0 with h1 | h1
      · exfalso
        have h := (hex 𝔮 h𝔮).1
        simp [h0, h1] at h
      · exact Or.inr h1
    · exact Or.inl h0
  obtain ⟨γ, hγ0, hγ1⟩ := l2_exists_gl F r₀ r₁ hr
  obtain ⟨y, hy⟩ := l2_pick F S₀ _ (fun v hv => (hex v hv).2)
  refine ⟨globalPoints (𝓞 F) F γ * (g₀ * GaussTwist.finLift (l2_lowerUnip F (GaussTwist.adeleOn S₀ y))),
    ?_, ?_⟩
  · rw [hleft, hright _ _ (l2_finLift_lowerUnip_mem F N _
      (l2_adeleOn_mem_idealBall F N S₀ y (fun w hw => (hy w hw).1)))]
    exact hg₀
  · intro v hv
    refine (l2_entry F v γ g₀ (GaussTwist.adeleOn S₀ y)).trans ?_
    rw [hγ0, hγ1, l2_adeleOn_apply_of_mem F S₀ y hv]
    exact (hy v hv).2

end GsolL2

private theorem leg_L2_point (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hright : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      φ (g * k) = φ g)
    (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0) :
    ∃ m : AdelicGL2 (𝓞 F) F, φ m ≠ 0 ∧
      ∀ 𝔭 ∈ S₀, (((m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) 𝔭 = 0 := by
  exact GsolL2.l2_main F N hN S₀ φ hleft hright g₀ hg₀

namespace WhittakerTranslate

open MeasureTheory Set NumberField IsDedekindDomain
open AutomorphicForm NumberField.AdelicHaar NumberField.AdelicBox
open scoped ProbabilityTheory Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
  NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox

section Countable

variable (K : Type) [Field K] [NumberField K]

private theorem countable_numberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 K) K) := by
  haveI := countable_numberField K
  exact (Set.countable_range (algebraMap K (AdeleRing (𝓞 K) K))).to_subtype

end Countable

section BoxIntegral

variable (K : Type) [Field K] [NumberField K]

private theorem setIntegral_adelicBox_comp_add_right {f : AdeleRing (𝓞 K) K → ℂ}
    (hf : ∀ (k : K) (x : AdeleRing (𝓞 K) K), f (algebraMap K (AdeleRing (𝓞 K) K) k + x) = f x)
    (x₀ : AdeleRing (𝓞 K) K) :
    ∫ x in adelicBox K, f (x + x₀) ∂(adelicAddHaar (𝓞 K) K)
      = ∫ x in adelicBox K, f x ∂(adelicAddHaar (𝓞 K) K) := by
  haveI := countable_principalSubgroup K
  have hB := isAddFundamentalDomain_adelicBox_adelicAddHaar K

  have hBt : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) (x₀ +ᵥ adelicBox K)
      (adelicAddHaar (𝓞 K) K) := hB.vadd_of_comm x₀

  have hf' : ∀ (g : AdeleRing.principalSubgroup (𝓞 K) K) (x : AdeleRing (𝓞 K) K),
      f (g +ᵥ x) = f x := by
    rintro ⟨_, k, rfl⟩ x
    exact hf k x

  have himg : (fun x => x + x₀) '' adelicBox K = x₀ +ᵥ adelicBox K := by
    ext y
    simp only [Set.mem_image, Set.mem_vadd_set, vadd_eq_add]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, add_comm _ _⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, add_comm _ _⟩
  have hmp := (measurePreserving_add_right (adelicAddHaar (𝓞 K) K) x₀).setIntegral_image_emb
    (measurableEmbedding_addRight x₀) f (adelicBox K)
  rw [himg] at hmp
  rw [← hmp]
  exact hBt.setIntegral_eq hB hf'

end BoxIntegral

section UnipotentTranslate

variable (K : Type) [Field K] [NumberField K]

private theorem globalPoints_unipotentGL2 (k : K) :
    globalPoints (𝓞 K) K (unipotentGL2 k) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change algebraMap K (AdeleRing (𝓞 K) K) ((unipotentGL2 k : Matrix (Fin 2) (Fin 2) K) i j)
    = (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) : Matrix (Fin 2) (Fin 2) _) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem setIntegral_adelicBox_unipotentGL2_mul
    {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ} (hψ : IsPrincipalInvariantAddChar K ψ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ (k : K) (h : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) * h) = φ h)
    (α : K) (x₀ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    ∫ x in adelicBox K, φ (unipotentGL2 x * (unipotentGL2 x₀ * g))
        * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) ∂(adelicAddHaar (𝓞 K) K)
      = ψ (algebraMap K (AdeleRing (𝓞 K) K) α * x₀)
        * ∫ x in adelicBox K, φ (unipotentGL2 x * g)
            * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) ∂(adelicAddHaar (𝓞 K) K) := by
  set a : AdeleRing (𝓞 K) K := algebraMap K (AdeleRing (𝓞 K) K) α with ha

  have hshift : ∀ x : AdeleRing (𝓞 K) K,
      φ (unipotentGL2 x * (unipotentGL2 x₀ * g)) * ψ (-(a * x))
        = (φ (unipotentGL2 (x + x₀) * g) * ψ (-(a * (x + x₀)))) * ψ (a * x₀) := by
    intro x
    have hn : unipotentGL2 x * (unipotentGL2 x₀ * g) = unipotentGL2 (x + x₀) * g := by
      rw [unipotentGL2_add, mul_assoc]
    have hψ' : ψ (-(a * x)) = ψ (-(a * (x + x₀))) * ψ (a * x₀) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [hn, hψ', mul_assoc]
  simp only [hshift]
  rw [integral_mul_const, mul_comm]
  congr 1

  refine setIntegral_adelicBox_comp_add_right K
    (f := fun y => φ (unipotentGL2 y * g) * ψ (-(a * y))) ?_ x₀
  intro k y
  show φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k + y) * g)
      * ψ (-(a * (algebraMap K (AdeleRing (𝓞 K) K) k + y)))
    = φ (unipotentGL2 y * g) * ψ (-(a * y))
  have hk : ψ (-(a * algebraMap K (AdeleRing (𝓞 K) K) k)) = 1 := by
    rw [ha, ← map_mul, ← map_neg]
    exact hψ _
  rw [unipotentGL2_add, mul_assoc, hφ, mul_add, neg_add, AddChar.map_add_eq_mul, hk, one_mul]

private theorem whittakerCoefficient_unipotentGL2_mul
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ} (hψ : IsPrincipalInvariantAddChar K ψ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ (k : K) (h : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) * h) = φ h)
    (α : K) (x₀ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ φ α (unipotentGL2 x₀ * g)
      = ψ (algebraMap K (AdeleRing (𝓞 K) K) α * x₀)
        * whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ φ α g := by
  show (∫ x, φ (unipotentGL2 x * (unipotentGL2 x₀ * g))
          * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) ∂((adelicAddHaar (𝓞 K) K)[|adelicBox K]))
      = ψ (algebraMap K (AdeleRing (𝓞 K) K) α * x₀)
        * ∫ x, φ (unipotentGL2 x * g)
          * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) ∂((adelicAddHaar (𝓞 K) K)[|adelicBox K])
  rw [ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure,
    setIntegral_adelicBox_unipotentGL2_mul K hψ hφ α x₀ g, mul_smul_comm]

private theorem whittakerCoefficient_unipotentGL2_mul_of_globalPoints
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ} (hψ : IsPrincipalInvariantAddChar K ψ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ (k : K) (h : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K (unipotentGL2 k) * h) = φ h)
    (α : K) (x₀ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ φ α (unipotentGL2 x₀ * g)
      = ψ (algebraMap K (AdeleRing (𝓞 K) K) α * x₀)
        * whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ φ α g :=
  whittakerCoefficient_unipotentGL2_mul K D U gen hψ
    (fun k h => by rw [← globalPoints_unipotentGL2, hφ]) α x₀ g

private theorem whittakerCoefficient_unipotentGL2_mul_of_isGlobalAddChar
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ} (hψ : IsGlobalAddChar K ψ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ (k : K) (h : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K (unipotentGL2 k) * h) = φ h)
    (α : K) (x₀ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ φ α (unipotentGL2 x₀ * g)
      = ψ (algebraMap K (AdeleRing (𝓞 K) K) α * x₀)
        * whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ φ α g :=
  whittakerCoefficient_unipotentGL2_mul_of_globalPoints K D U gen hψ.principalInvariant hφ α x₀ g

end UnipotentTranslate

end WhittakerTranslate

private theorem leg_L3_translate (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g)
    (α : F) (x₀ : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α (unipotentGL2 x₀ * g)
      = ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x₀) *
          whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g := by
  exact WhittakerTranslate.whittakerCoefficient_unipotentGL2_mul F D U gen hψ.principalInvariant hφ α x₀ g

section EntryComputation

variable {A : Type*} [CommRing A]

private theorem gl2_mul_unipotentGL2_eq_unipotentGL2_mul (m : GL (Fin 2) A) {y s : A}
    (hc : (m : Matrix (Fin 2) (Fin 2) A) 1 0 * y = 0)
    (hsc : s * (m : Matrix (Fin 2) (Fin 2) A) 1 0 = 0)
    (hsd : s * (m : Matrix (Fin 2) (Fin 2) A) 1 1 = (m : Matrix (Fin 2) (Fin 2) A) 0 0 * y) :
    m * AutomorphicForm.unipotentGL2 y = AutomorphicForm.unipotentGL2 s * m := by
  apply Units.ext
  simp only [Units.val_mul, AutomorphicForm.unipotentGL2_coe]
  rw [Matrix.eta_fin_two (m : Matrix (Fin 2) (Fin 2) A), Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc, hsc, hsd, add_comm]

end EntryComputation

section Adelic

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem adele_eq_of_parts {z z' : NumberField.AdeleRing R K}
    (ha : NumberField.AdelicLevel.adeleArch R K z = NumberField.AdelicLevel.adeleArch R K z')
    (hf : NumberField.AdelicLevel.adeleFin R K z = NumberField.AdelicLevel.adeleFin R K z') :
    z = z' :=
  Prod.ext ha hf

private noncomputable def finAdeleIn (x : IsDedekindDomain.FiniteAdeleRing R K) : NumberField.AdeleRing R K :=
  ((0 : NumberField.InfiniteAdeleRing K), x)

private theorem adeleArch_finAdeleIn (x : IsDedekindDomain.FiniteAdeleRing R K) :
    NumberField.AdelicLevel.adeleArch R K (finAdeleIn x) = 0 := rfl

private theorem adeleFin_finAdeleIn (x : IsDedekindDomain.FiniteAdeleRing R K) :
    NumberField.AdelicLevel.adeleFin R K (finAdeleIn x) = x := rfl

private theorem finLift_unipotentGL2 (x : IsDedekindDomain.FiniteAdeleRing R K) :
    AutomorphicForm.GaussTwist.finLift (AutomorphicForm.unipotentGL2 x)
      = AutomorphicForm.unipotentGL2 (finAdeleIn (R := R) (K := K) x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem adelicGL2_lowerRight_ne_zero_of_lowerLeft_eq_zero (m : AutomorphicForm.AdelicGL2 R K)
    {w : IsDedekindDomain.HeightOneSpectrum R}
    (hc : NumberField.AdelicLevel.adeleFin R K
      ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 0) w = 0) :
    NumberField.AdelicLevel.adeleFin R K
      ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 1) w ≠ 0 := by
  intro hd
  have h1 : (m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)).det
      * ((m⁻¹ : GL (Fin 2) (NumberField.AdeleRing R K)) :
          Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have h2 := congrArg (fun z => NumberField.AdelicLevel.adeleFin R K z w) h1
  simp only [map_mul, map_one, NumberField.AdelicLevel.coe_mul_apply,
    NumberField.AdelicLevel.coe_one_apply] at h2
  rw [Matrix.det_fin_two (m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)), map_sub,
    map_mul, map_mul, NumberField.AdelicLevel.coe_sub_apply, NumberField.AdelicLevel.coe_mul_apply,
    NumberField.AdelicLevel.coe_mul_apply, hc, hd, mul_zero, mul_zero, sub_zero, zero_mul] at h2
  exact zero_ne_one h2

variable (S : Finset (IsDedekindDomain.HeightOneSpectrum R)) [DecidablePred (· ∈ S)]

private noncomputable def borelConjEntry (m : AutomorphicForm.AdelicGL2 R K) (y : IsDedekindDomain.FiniteAdeleRing R K) :
    IsDedekindDomain.FiniteAdeleRing R K :=
  AutomorphicForm.GaussTwist.adeleOn S fun w =>
    NumberField.AdelicLevel.adeleFin R K
        ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 0 0) w
      / NumberField.AdelicLevel.adeleFin R K
        ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 1) w
      * y w

private theorem borelConjEntry_apply_of_mem (m : AutomorphicForm.AdelicGL2 R K)
    (y : IsDedekindDomain.FiniteAdeleRing R K) {w : IsDedekindDomain.HeightOneSpectrum R}
    (hw : w ∈ S) :
    borelConjEntry S m y w =
      NumberField.AdelicLevel.adeleFin R K
          ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 0 0) w
        / NumberField.AdelicLevel.adeleFin R K
          ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 1) w
        * y w := by
  show (if w ∈ S then _ else (0 : w.adicCompletion K)) = _
  rw [if_pos hw]

private theorem borelConjEntry_apply_of_not_mem (m : AutomorphicForm.AdelicGL2 R K)
    (y : IsDedekindDomain.FiniteAdeleRing R K) {w : IsDedekindDomain.HeightOneSpectrum R}
    (hw : w ∉ S) : borelConjEntry S m y w = 0 := by
  show (if w ∈ S then _ else (0 : w.adicCompletion K)) = _
  rw [if_neg hw]

private theorem adelicGL2_mul_finLift_unipotentGL2 (m : AutomorphicForm.AdelicGL2 R K)
    (y : IsDedekindDomain.FiniteAdeleRing R K)
    (hy : ∀ w : IsDedekindDomain.HeightOneSpectrum R, w ∉ S → y w = 0)
    (hc : ∀ w ∈ S, NumberField.AdelicLevel.adeleFin R K
      ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 0) w = 0) :
    m * AutomorphicForm.GaussTwist.finLift (AutomorphicForm.unipotentGL2 y)
      = AutomorphicForm.GaussTwist.finLift (AutomorphicForm.unipotentGL2 (borelConjEntry S m y))
        * m := by
  rw [finLift_unipotentGL2, finLift_unipotentGL2]
  apply gl2_mul_unipotentGL2_eq_unipotentGL2_mul
  · apply adele_eq_of_parts
    · rw [map_mul, adeleArch_finAdeleIn, mul_zero, map_zero]
    · rw [map_mul, adeleFin_finAdeleIn, map_zero]
      ext w
      rw [NumberField.AdelicLevel.coe_mul_apply, NumberField.AdelicLevel.coe_zero_apply]
      by_cases hw : w ∈ S
      · rw [hc w hw, zero_mul]
      · rw [hy w hw, mul_zero]
  · apply adele_eq_of_parts
    · rw [map_mul, adeleArch_finAdeleIn, zero_mul, map_zero]
    · rw [map_mul, adeleFin_finAdeleIn, map_zero]
      ext w
      rw [NumberField.AdelicLevel.coe_mul_apply, NumberField.AdelicLevel.coe_zero_apply]
      by_cases hw : w ∈ S
      · rw [hc w hw, mul_zero]
      · rw [borelConjEntry_apply_of_not_mem S m y hw, zero_mul]
  · apply adele_eq_of_parts
    · rw [map_mul, map_mul, adeleArch_finAdeleIn, adeleArch_finAdeleIn, zero_mul, mul_zero]
    · rw [map_mul, map_mul, adeleFin_finAdeleIn, adeleFin_finAdeleIn]
      ext w : 1
      rw [NumberField.AdelicLevel.coe_mul_apply, NumberField.AdelicLevel.coe_mul_apply]
      by_cases hw : w ∈ S
      · rw [borelConjEntry_apply_of_mem S m y hw]
        have hd := adelicGL2_lowerRight_ne_zero_of_lowerLeft_eq_zero (R := R) (K := K) m (hc w hw)
        calc NumberField.AdelicLevel.adeleFin R K
                ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 0 0) w
              / NumberField.AdelicLevel.adeleFin R K
                ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 1) w
              * y w
              * NumberField.AdelicLevel.adeleFin R K
                ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 1) w
            = NumberField.AdelicLevel.adeleFin R K
                ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 0 0) w * y w
              * (NumberField.AdelicLevel.adeleFin R K
                  ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 1) w
                / NumberField.AdelicLevel.adeleFin R K
                  ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 1) w) := by ring
          _ = NumberField.AdelicLevel.adeleFin R K
                ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 0 0) w * y w := by
              rw [div_self hd, mul_one]
      · rw [borelConjEntry_apply_of_not_mem S m y hw, zero_mul, hy w hw, mul_zero]

private theorem adelicGL2_upperLeft_ne_zero_of_lowerLeft_eq_zero (m : AutomorphicForm.AdelicGL2 R K)
    {w : IsDedekindDomain.HeightOneSpectrum R}
    (hc : NumberField.AdelicLevel.adeleFin R K
      ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 0) w = 0) :
    NumberField.AdelicLevel.adeleFin R K
      ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 0 0) w ≠ 0 := by
  intro ha
  have h1 : (m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)).det
      * ((m⁻¹ : GL (Fin 2) (NumberField.AdeleRing R K)) :
          Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have h2 := congrArg (fun z => NumberField.AdelicLevel.adeleFin R K z w) h1
  simp only [map_mul, map_one, NumberField.AdelicLevel.coe_mul_apply,
    NumberField.AdelicLevel.coe_one_apply] at h2
  rw [Matrix.det_fin_two (m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)), map_sub,
    map_mul, map_mul, NumberField.AdelicLevel.coe_sub_apply, NumberField.AdelicLevel.coe_mul_apply,
    NumberField.AdelicLevel.coe_mul_apply, hc, ha, zero_mul, mul_zero, sub_zero, zero_mul] at h2
  exact zero_ne_one h2

private noncomputable def borelConjRatio (m : AutomorphicForm.AdelicGL2 R K) : IsDedekindDomain.FiniteAdeleRing R K :=
  AutomorphicForm.GaussTwist.adeleOn S fun w =>
    NumberField.AdelicLevel.adeleFin R K
        ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 0 0) w
      / NumberField.AdelicLevel.adeleFin R K
        ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 1) w

private theorem borelConjRatio_apply_of_mem (m : AutomorphicForm.AdelicGL2 R K)
    {w : IsDedekindDomain.HeightOneSpectrum R} (hw : w ∈ S) :
    borelConjRatio S m w =
      NumberField.AdelicLevel.adeleFin R K
          ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 0 0) w
        / NumberField.AdelicLevel.adeleFin R K
          ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 1) w := by
  show (if w ∈ S then _ else (0 : w.adicCompletion K)) = _
  rw [if_pos hw]

private theorem borelConjRatio_apply_of_not_mem (m : AutomorphicForm.AdelicGL2 R K)
    {w : IsDedekindDomain.HeightOneSpectrum R} (hw : w ∉ S) : borelConjRatio S m w = 0 := by
  show (if w ∈ S then _ else (0 : w.adicCompletion K)) = _
  rw [if_neg hw]

private theorem borelConjRatio_apply_ne_zero (m : AutomorphicForm.AdelicGL2 R K)
    {w : IsDedekindDomain.HeightOneSpectrum R} (hw : w ∈ S)
    (hc : NumberField.AdelicLevel.adeleFin R K
      ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 0) w = 0) :
    borelConjRatio S m w ≠ 0 := by
  rw [borelConjRatio_apply_of_mem S m hw]
  exact div_ne_zero (adelicGL2_upperLeft_ne_zero_of_lowerLeft_eq_zero m hc)
    (adelicGL2_lowerRight_ne_zero_of_lowerLeft_eq_zero m hc)

private theorem borelConjEntry_eq_borelConjRatio_mul (m : AutomorphicForm.AdelicGL2 R K)
    (y : IsDedekindDomain.FiniteAdeleRing R K) :
    borelConjEntry S m y = borelConjRatio S m * y := by
  ext w
  rw [NumberField.AdelicLevel.coe_mul_apply]
  by_cases hw : w ∈ S
  · rw [borelConjEntry_apply_of_mem S m y hw, borelConjRatio_apply_of_mem S m hw]
  · rw [borelConjEntry_apply_of_not_mem S m y hw, borelConjRatio_apply_of_not_mem S m hw, zero_mul]

private theorem exists_borelConj_datum (m : AutomorphicForm.AdelicGL2 R K)
    (hm : ∀ w ∈ S, (((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 0).2) w = 0) :
    ∃ tf : IsDedekindDomain.FiniteAdeleRing R K, (∀ w ∈ S, tf w ≠ 0) ∧
      ∀ y : IsDedekindDomain.FiniteAdeleRing R K,
        (∀ q : IsDedekindDomain.HeightOneSpectrum R, q ∉ S → y q = 0) →
          m * AutomorphicForm.GaussTwist.finLift (AutomorphicForm.unipotentGL2 y)
            = AutomorphicForm.unipotentGL2 (finAdeleIn (R := R) (K := K) (tf * y)) * m := by
  have hc : ∀ w ∈ S, NumberField.AdelicLevel.adeleFin R K
      ((m : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R K)) 1 0) w = 0 := by
    intro w hw
    rw [NumberField.AdelicLevel.adeleFin_apply]
    exact hm w hw
  refine ⟨borelConjRatio S m, fun w hw => borelConjRatio_apply_ne_zero S m hw (hc w hw),
    fun y hy => ?_⟩
  rw [adelicGL2_mul_finLift_unipotentGL2 S m y hy hc, finLift_unipotentGL2,
    borelConjEntry_eq_borelConjRatio_mul S m y]

end Adelic

private theorem leg_L3b_conj (F : Type) [Field F] [NumberField F]
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (m : AdelicGL2 (𝓞 F) F)
    (hm : ∀ 𝔭 ∈ S₀, (((m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) 𝔭 = 0) :
    ∃ tf : FiniteAdeleRing (𝓞 F) F, (∀ 𝔭 ∈ S₀, tf 𝔭 ≠ 0) ∧
      ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ 𝔮, 𝔮 ∉ S₀ → y 𝔮 = 0) →
        m * AutomorphicForm.GaussTwist.finLift (unipotentGL2 y)
          = unipotentGL2 (gsolFinAdele F (tf * y)) * m := by
  exact exists_borelConj_datum S₀ m hm

private theorem l4_mul_finAdeleSingleAt (F : Type) [Field F] [NumberField F]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (c : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    (y : 𝔭.adicCompletion F) :
    c * NumberField.StandardAddChar.finAdeleSingleAt F 𝔭 y
      = NumberField.StandardAddChar.finAdeleSingleAt F 𝔭 (c 𝔭 * y) := by
  refine DFunLike.ext _ _ fun w => ?_
  change c w * NumberField.StandardAddChar.finAdeleSingleAt F 𝔭 y w
    = NumberField.StandardAddChar.finAdeleSingleAt F 𝔭 (c 𝔭 * y) w
  by_cases hw : w = 𝔭
  · rw [hw, NumberField.StandardAddChar.finAdeleSingleAt_apply_self,
      NumberField.StandardAddChar.finAdeleSingleAt_apply_self]
  · rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne F 𝔭 y hw,
      NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne F 𝔭 (c 𝔭 * y) hw, mul_zero]

private theorem l4_single_support (F : Type) [Field F] [NumberField F]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (h𝔭 : 𝔭 ∈ S₀) (y : 𝔭.adicCompletion F) :
    ∀ 𝔮, 𝔮 ∉ S₀ → NumberField.StandardAddChar.finAdeleSingleAt F 𝔭 y 𝔮 = 0 := by
  intro 𝔮 h𝔮
  refine NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne F 𝔭 y ?_
  rintro rfl
  exact h𝔮 h𝔭

private theorem l4_single_integral (F : Type) [Field F] [NumberField F]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (y : 𝔭.adicCompletion F) (hy : Valued.v y ≤ 1) :
    NumberField.StandardAddChar.finAdeleSingleAt F 𝔭 y
      ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F := by
  simp only [NumberField.AdelicLevel.integralFiniteAdeles, Set.mem_setOf_eq]
  intro w
  by_cases hw : w = 𝔭
  · subst hw
    rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_self]
    exact hy
  · rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne F 𝔭 y hw]
    exact (w.adicCompletionIntegers F).zero_mem

private theorem l4_isLevelOne_unipotent (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F))
    (s : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    (hs : s ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F) :
    NumberField.AdelicLevel.IsLevelOneMatrix (𝓞 F) F N !![1, s; 0, 1] where
  integral i j := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact NumberField.AdelicLevel.one_mem_integralFiniteAdeles
        | exact NumberField.AdelicLevel.zero_mem_integralFiniteAdeles
        | exact hs
  lowerLeft := NumberField.AdelicLevel.zero_mem_idealBall N
  lowerRight := by
    show (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) - 1 ∈ NumberField.AdelicLevel.idealBall (𝓞 F) F N
    rw [sub_self]
    exact NumberField.AdelicLevel.zero_mem_idealBall N

private theorem l4_unipotent_mem (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F))
    (s : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    (hs : s ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F) :
    AutomorphicForm.GaussTwist.finLift (unipotentGL2 s)
      ∈ NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup F := by
  have hneg : -s ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F := by
    rw [← zero_sub]
    exact NumberField.AdelicLevel.sub_mem_integralFiniteAdeles
      NumberField.AdelicLevel.zero_mem_integralFiniteAdeles hs
  have hfin : NumberField.AdelicLevel.glFin (𝓞 F) F (AutomorphicForm.GaussTwist.finLift (unipotentGL2 s))
      = unipotentGL2 s := by
    ext i j
    rfl
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · refine NumberField.AdelicLevel.mem_levelOne_iff.2 ?_
    rw [hfin]
    exact NumberField.AdelicLevel.mem_finiteLevelOne_iff.2
      ⟨l4_isLevelOne_unipotent F N s hs, l4_isLevelOne_unipotent F N (-s) hneg⟩
  · refine (AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff F _).2 ?_
    ext i j
    rw [Units.val_one]
    rfl

private theorem l4_whittakerCoefficient_mul_right (F : Type) [Field F] [NumberField F]
    (pins : AutomorphicForm.CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g k : AdelicGL2 (𝓞 F) F)
    (hk : ∀ h : AdelicGL2 (𝓞 F) F, φ (h * k) = φ h) :
    AutomorphicForm.whittakerCoefficient F pins ψ φ α (g * k)
      = AutomorphicForm.whittakerCoefficient F pins ψ φ α g := by
  letI := pins.nS
  simp only [AutomorphicForm.whittakerCoefficient, ← mul_assoc, hk]

private theorem l4_stdAddChar_eq_psiLocal (F : Type) [Field F] [NumberField F]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (α : F)
    (tf : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (y : 𝔭.adicCompletion F)
    (x : AdeleRing (𝓞 F) F) (hx1 : x.1 = 0)
    (hx2 : x.2 = tf * NumberField.StandardAddChar.finAdeleSingleAt F 𝔭 y) :
    NumberField.StandardAddChar.stdAddChar F (algebraMap F (AdeleRing (𝓞 F) F) α * x)
      = NumberField.StandardAddChar.psiLocal F 𝔭 (algebraMap F (𝔭.adicCompletion F) α * tf 𝔭 * y) := by
  rw [NumberField.StandardAddChar.psiLocal_apply]
  have h1 : (algebraMap F (AdeleRing (𝓞 F) F) α * x).1 = (0 : InfiniteAdeleRing F) := by
    change (algebraMap F (AdeleRing (𝓞 F) F) α).1 * x.1 = 0
    rw [hx1, mul_zero]
  have h2 : (algebraMap F (AdeleRing (𝓞 F) F) α * x).2
      = NumberField.StandardAddChar.finAdeleSingleAt F 𝔭
          (algebraMap F (𝔭.adicCompletion F) α * tf 𝔭 * y) := by
    change (algebraMap F (AdeleRing (𝓞 F) F) α).2 * x.2 = _
    rw [hx2, ← mul_assoc, l4_mul_finAdeleSingleAt]
    rfl
  exact congrArg (fun z => NumberField.StandardAddChar.stdAddChar F z) (Prod.ext h1 h2)

private theorem l4_lattice_of_translate (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (N : Ideal (𝓞 F)) (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hright : ∀ g : AdelicGL2 (𝓞 F) F,
      ∀ k ∈ NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup F,
        φ (g * k) = φ g)
    (m : AdelicGL2 (𝓞 F) F) (tf : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    (hconj : ∀ y : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F, (∀ 𝔮, 𝔮 ∉ S₀ → y 𝔮 = 0) →
      m * AutomorphicForm.GaussTwist.finLift (unipotentGL2 y)
        = unipotentGL2 (gsolFinAdele F (tf * y)) * m)
    (α : F)
    (hα : AutomorphicForm.whittakerCoefficient F
      (AutomorphicForm.productionPinsOf F D U gen (NumberField.AdelicBox.adelicBox F))
      (NumberField.StandardAddChar.stdAddChar F) φ α m ≠ 0)
    (htrans : ∀ (x₀ : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      AutomorphicForm.whittakerCoefficient F
          (AutomorphicForm.productionPinsOf F D U gen (NumberField.AdelicBox.adelicBox F))
          (NumberField.StandardAddChar.stdAddChar F) φ α (unipotentGL2 x₀ * g)
        = NumberField.StandardAddChar.stdAddChar F (algebraMap F (AdeleRing (𝓞 F) F) α * x₀) *
            AutomorphicForm.whittakerCoefficient F
              (AutomorphicForm.productionPinsOf F D U gen (NumberField.AdelicBox.adelicBox F))
              (NumberField.StandardAddChar.stdAddChar F) φ α g) :
    ∀ 𝔭 ∈ S₀, ∀ y : 𝔭.adicCompletion F, Valued.v y ≤ 1 →
      NumberField.StandardAddChar.psiLocal F 𝔭 (algebraMap F (𝔭.adicCompletion F) α * tf 𝔭 * y) = 1 := by
  intro 𝔭 h𝔭 y hy
  have hmem := l4_unipotent_mem F N (NumberField.StandardAddChar.finAdeleSingleAt F 𝔭 y)
    (l4_single_integral F 𝔭 y hy)
  have h1 := l4_whittakerCoefficient_mul_right F
    (AutomorphicForm.productionPinsOf F D U gen (NumberField.AdelicBox.adelicBox F))
    (NumberField.StandardAddChar.stdAddChar F) φ α m
    (AutomorphicForm.GaussTwist.finLift (unipotentGL2 (NumberField.StandardAddChar.finAdeleSingleAt F 𝔭 y)))
    (fun h => hright h _ hmem)
  rw [hconj _ (l4_single_support F 𝔭 S₀ h𝔭 y), htrans] at h1
  have h2 := mul_right_cancel₀ hα (h1.trans (one_mul _).symm)
  have h3 := l4_stdAddChar_eq_psiLocal F 𝔭 α tf y
    (gsolFinAdele F (tf * NumberField.StandardAddChar.finAdeleSingleAt F 𝔭 y)) rfl rfl
  exact h3.symm.trans h2

private theorem leg_L4_lattice (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (N : Ideal (𝓞 F)) (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g)
    (hright : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      φ (g * k) = φ g)
    (m : AdelicGL2 (𝓞 F) F) (tf : FiniteAdeleRing (𝓞 F) F)
    (hconj : ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ 𝔮, 𝔮 ∉ S₀ → y 𝔮 = 0) →
      m * AutomorphicForm.GaussTwist.finLift (unipotentGL2 y)
        = unipotentGL2 (gsolFinAdele F (tf * y)) * m)
    (α : F)
    (hα : whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F))
      (NumberField.StandardAddChar.stdAddChar F) φ α m ≠ 0) :
    ∀ 𝔭 ∈ S₀, ∀ y : 𝔭.adicCompletion F, Valued.v y ≤ 1 →
      NumberField.StandardAddChar.psiLocal F 𝔭 (algebraMap F (𝔭.adicCompletion F) α * tf 𝔭 * y) = 1 := by
  exact l4_lattice_of_translate F D U gen N S₀ φ hright m tf hconj α hα
    (leg_L3_translate F D U gen (NumberField.StandardAddChar.stdAddChar F)
      (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar F) φ hφ α)

private noncomputable def gsolL5_scaledPsi (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (z : v.adicCompletion K) : AddChar (v.adicCompletion K) ℂ :=
  (NumberField.StandardAddChar.psiLocal K v).compAddMonoidHom (AddMonoidHom.mulLeft z)

private theorem gsolL5_scaledPsi_apply (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (z x : v.adicCompletion K) :
    gsolL5_scaledPsi K v z x = NumberField.StandardAddChar.psiLocal K v (z * x) := rfl

private theorem gsolL5_scaledPsi_ne_one (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (z : v.adicCompletion K) (hz : z ≠ 0) : gsolL5_scaledPsi K v z ≠ 1 := by
  intro h
  apply LanglandsTunnell.TateLocal.psiLocal_ne_one K v
  ext y
  have hy := congrArg (fun θ : AddChar (v.adicCompletion K) ℂ => θ (z⁻¹ * y)) h
  simpa [gsolL5_scaledPsi_apply, mul_inv_cancel_left₀ hz] using hy

private theorem gsolL5_level (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (z : v.adicCompletion K) (hz : z ≠ 0)
    (htriv : ∀ x : v.adicCompletion K, x ∈ v.adicCompletionIntegers K →
      NumberField.StandardAddChar.psiLocal K v (z * x) = 1) :
    0 ≤ LanglandsTunnell.TateLocal.addCharLevel (gsolL5_scaledPsi K v z) ∧
      (∀ x : v.adicCompletion K,
        Valued.v x ≤
            WithZero.exp (LanglandsTunnell.TateLocal.addCharLevel (gsolL5_scaledPsi K v z)) →
          NumberField.StandardAddChar.psiLocal K v (z * x) = 1) ∧
      ∃ x : v.adicCompletion K,
        Valued.v x ≤
            WithZero.exp (LanglandsTunnell.TateLocal.addCharLevel (gsolL5_scaledPsi K v z) + 1) ∧
          NumberField.StandardAddChar.psiLocal K v (z * x) ≠ 1 := by
  have hint : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (0 : ℤ) →
      NumberField.StandardAddChar.psiLocal K v (z * x) = 1 := by
    intro x hx
    apply htriv
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have hball : ∃ k : ℤ, ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp k →
      gsolL5_scaledPsi K v z x = 1 :=
    ⟨0, fun x hx => by rw [gsolL5_scaledPsi_apply]; exact hint x hx⟩
  obtain ⟨h₁, x₀, hx₀, hne⟩ :=
    LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel K v
      (gsolL5_scaledPsi K v z) hball (gsolL5_scaledPsi_ne_one K v z hz)
  rw [gsolL5_scaledPsi_apply] at hne
  refine ⟨?_, fun x hx => ?_, ⟨x₀, hx₀, hne⟩⟩
  · by_contra hneg
    have hle : LanglandsTunnell.TateLocal.addCharLevel (gsolL5_scaledPsi K v z) + 1 ≤ 0 := by
      omega
    exact hne (hint x₀ (hx₀.trans (WithZero.exp_le_exp.2 hle)))
  · have hx' := h₁ x hx
    rwa [gsolL5_scaledPsi_apply] at hx'

private theorem gsolL5_dock (F : Type) [Field F] [NumberField F]
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (z : (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
      𝔭.adicCompletion F)
    (hz : ∀ 𝔭 ∈ S₀, z 𝔭 ≠ 0)
    (hlat : ∀ 𝔭 ∈ S₀, ∀ y : 𝔭.adicCompletion F, Valued.v y ≤ 1 →
      NumberField.StandardAddChar.psiLocal F 𝔭 (z 𝔭 * y) = 1) :
    ∃ d : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ℕ, ∀ 𝔭 ∈ S₀,
      (∀ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp (d 𝔭 : ℤ) →
          NumberField.StandardAddChar.psiLocal F 𝔭 (z 𝔭 * y) = 1) ∧
        ∃ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp ((d 𝔭 : ℤ) + 1) ∧
          NumberField.StandardAddChar.psiLocal F 𝔭 (z 𝔭 * y) ≠ 1 := by
  refine ⟨fun 𝔭 => (LanglandsTunnell.TateLocal.addCharLevel (gsolL5_scaledPsi F 𝔭 (z 𝔭))).toNat, ?_⟩
  intro 𝔭 h𝔭
  obtain ⟨hd, h₁, h₂⟩ := gsolL5_level F 𝔭 (z 𝔭) (hz 𝔭 h𝔭) (fun y hy => hlat 𝔭 h𝔭 y hy)
  rw [Int.toNat_of_nonneg hd]
  exact ⟨h₁, h₂⟩

private theorem leg_L5_level (F : Type) [Field F] [NumberField F]
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (z : (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) → 𝔭.adicCompletion F)
    (hz : ∀ 𝔭 ∈ S₀, z 𝔭 ≠ 0)
    (hlat : ∀ 𝔭 ∈ S₀, ∀ y : 𝔭.adicCompletion F, Valued.v y ≤ 1 →
      NumberField.StandardAddChar.psiLocal F 𝔭 (z 𝔭 * y) = 1) :
    ∃ d : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ, ∀ 𝔭 ∈ S₀,
      (∀ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp (d 𝔭 : ℤ) →
          NumberField.StandardAddChar.psiLocal F 𝔭 (z 𝔭 * y) = 1) ∧
        ∃ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp ((d 𝔭 : ℤ) + 1) ∧
          NumberField.StandardAddChar.psiLocal F 𝔭 (z 𝔭 * y) ≠ 1 := by
  exact gsolL5_dock F S₀ z hz hlat

section L6GaussCore

variable {A : Type*} [CommRing A] [Fintype Aˣ]

private theorem l6_sum_units_eq_zero (η : Aˣ →* ℂˣ) (ψ : AddChar A ℂ) (y : A) (r : Aˣ)
    (hr : η r ≠ 1) (hry : (r : A) * y = y) :
    ∑ t : Aˣ, ((η t : ℂˣ) : ℂ) * ψ (y * t) = 0 := by
  have hr' : ((η r : ℂˣ) : ℂ) ≠ 1 := fun h => hr (Units.val_eq_one.mp h)
  have hre : ∑ t : Aˣ, ((η (r * t) : ℂˣ) : ℂ) * ψ (y * ((r * t : Aˣ) : A))
      = ∑ t : Aˣ, ((η t : ℂˣ) : ℂ) * ψ (y * t) :=
    (Group.mulLeft_bijective r).sum_comp (fun t : Aˣ => ((η t : ℂˣ) : ℂ) * ψ (y * t))
  refine eq_zero_of_mul_eq_self_left hr' ?_
  rw [Finset.mul_sum, ← hre]
  refine Finset.sum_congr rfl fun t _ => ?_
  have e : y * ((r * t : Aˣ) : A) = y * t := by
    rw [Units.val_mul, ← mul_assoc, mul_comm y (r : A), hry]
  rw [e, η.map_mul r t, Units.val_mul, mul_assoc]

private theorem l6_gaussSum_mul_eq_card [Fintype A] (η : Aˣ →* ℂˣ) (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive)
    (hη : ∀ y : A, ¬ IsUnit y → ∃ r : Aˣ, η r ≠ 1 ∧ (r : A) * y = y) :
    (∑ u : Aˣ, ((η u : ℂˣ) : ℂ) * ψ u) * (∑ v : Aˣ, ((η v⁻¹ : ℂˣ) : ℂ) * ψ (-(v : A)))
      = Fintype.card A := by

  have hsummand : ∀ t v : Aˣ,
      ((η (t * v) : ℂˣ) : ℂ) * ψ ((t * v : Aˣ) : A) * (((η v⁻¹ : ℂˣ) : ℂ) * ψ (-(v : A)))
        = ((η t : ℂˣ) : ℂ) * ψ ((v : A) * ((t : A) - 1)) := by
    intro t v
    have e1 : ((η (t * v) : ℂˣ) : ℂ) * ((η v⁻¹ : ℂˣ) : ℂ) = ((η t : ℂˣ) : ℂ) := by
      rw [← Units.val_mul, ← η.map_mul, mul_inv_cancel_right]
    have e2 : ψ ((t * v : Aˣ) : A) * ψ (-(v : A)) = ψ ((v : A) * ((t : A) - 1)) := by
      rw [← AddChar.map_add_eq_mul, Units.val_mul]
      congr 1
      ring
    calc ((η (t * v) : ℂˣ) : ℂ) * ψ ((t * v : Aˣ) : A) * (((η v⁻¹ : ℂˣ) : ℂ) * ψ (-(v : A)))
        = (((η (t * v) : ℂˣ) : ℂ) * ((η v⁻¹ : ℂˣ) : ℂ))
            * (ψ ((t * v : Aˣ) : A) * ψ (-(v : A))) := by ring
      _ = ((η t : ℂˣ) : ℂ) * ψ ((v : A) * ((t : A) - 1)) := by rw [e1, e2]

  have h1 : (∑ u : Aˣ, ((η u : ℂˣ) : ℂ) * ψ u) * (∑ v : Aˣ, ((η v⁻¹ : ℂˣ) : ℂ) * ψ (-(v : A)))
      = ∑ t : Aˣ, ((η t : ℂˣ) : ℂ) * ∑ v : Aˣ, ψ ((v : A) * ((t : A) - 1)) := by
    rw [Fintype.sum_mul_sum, Finset.sum_comm]
    calc ∑ v : Aˣ, ∑ u : Aˣ, ((η u : ℂˣ) : ℂ) * ψ u * (((η v⁻¹ : ℂˣ) : ℂ) * ψ (-(v : A)))
        = ∑ v : Aˣ, ∑ t : Aˣ, ((η t : ℂˣ) : ℂ) * ψ ((v : A) * ((t : A) - 1)) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          symm
          exact Fintype.sum_bijective (· * v) (Group.mulRight_bijective v) _ _
            fun t => (hsummand t v).symm
      _ = ∑ t : Aˣ, ((η t : ℂˣ) : ℂ) * ∑ v : Aˣ, ψ ((v : A) * ((t : A) - 1)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ => (Finset.mul_sum _ _ _).symm

  have hunits : ∀ s : A, ∑ v : Aˣ, ψ ((v : A) * s)
      = (∑ x : A, ψ (x * s)) - ∑ x ∈ Finset.univ.filter (fun x : A => ¬ IsUnit x), ψ (x * s) := by
    intro s
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset A)
      (fun x : A => IsUnit x) (fun x : A => ψ (x * s))
    have himg : Finset.univ.filter (fun x : A => IsUnit x)
        = (Finset.univ : Finset Aˣ).image (fun v : Aˣ => (v : A)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨u, hu⟩
        exact ⟨u, hu⟩
      · rintro ⟨u, hu⟩
        exact ⟨u, hu⟩
    have hvals : ∑ x ∈ Finset.univ.filter (fun x : A => IsUnit x), ψ (x * s)
        = ∑ v : Aˣ, ψ ((v : A) * s) := by
      rw [himg, Finset.sum_image fun a _ b _ h => Units.ext h]
    rw [← hvals, eq_sub_iff_add_eq]
    exact hsplit

  have h2 : ∀ t : Aˣ, ((η t : ℂˣ) : ℂ) * ∑ v : Aˣ, ψ ((v : A) * ((t : A) - 1))
      = ((η t : ℂˣ) : ℂ) * ((if (t : A) - 1 = 0 then Fintype.card A else 0 : ℕ) : ℂ)
        - ((η t : ℂˣ) : ℂ) *
            ∑ x ∈ Finset.univ.filter (fun x : A => ¬ IsUnit x), ψ (x * ((t : A) - 1)) := by
    intro t
    rw [hunits, AddChar.sum_mulShift _ hψ, mul_sub]
  have hfirst : ∑ t : Aˣ, ((η t : ℂˣ) : ℂ) * ((if (t : A) - 1 = 0 then Fintype.card A else 0 : ℕ) : ℂ)
      = Fintype.card A := by
    rw [Finset.sum_eq_single (1 : Aˣ)]
    · rw [map_one, Units.val_one, Units.val_one, sub_self, if_pos rfl, one_mul]
    · intro t _ ht
      rw [if_neg (fun h => ht (Units.val_eq_one.mp (sub_eq_zero.mp h))), Nat.cast_zero, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h

  have hsecond : ∑ t : Aˣ, ((η t : ℂˣ) : ℂ) *
      ∑ x ∈ Finset.univ.filter (fun x : A => ¬ IsUnit x), ψ (x * ((t : A) - 1)) = 0 := by
    have hcomm : ∑ t : Aˣ, ((η t : ℂˣ) : ℂ) *
        ∑ x ∈ Finset.univ.filter (fun x : A => ¬ IsUnit x), ψ (x * ((t : A) - 1))
        = ∑ x ∈ Finset.univ.filter (fun x : A => ¬ IsUnit x),
            ψ (-x) * ∑ t : Aˣ, ((η t : ℂˣ) : ℂ) * ψ (x * t) := by
      calc ∑ t : Aˣ, ((η t : ℂˣ) : ℂ) *
            ∑ x ∈ Finset.univ.filter (fun x : A => ¬ IsUnit x), ψ (x * ((t : A) - 1))
          = ∑ t : Aˣ, ∑ x ∈ Finset.univ.filter (fun x : A => ¬ IsUnit x),
              ψ (-x) * (((η t : ℂˣ) : ℂ) * ψ (x * t)) := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            have e : x * ((t : A) - 1) = -x + x * t := by ring
            rw [e, AddChar.map_add_eq_mul]
            ring
        _ = ∑ x ∈ Finset.univ.filter (fun x : A => ¬ IsUnit x),
              ψ (-x) * ∑ t : Aˣ, ((η t : ℂˣ) : ℂ) * ψ (x * t) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
    rw [hcomm]
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨r, hr, hrx⟩ := hη x (Finset.mem_filter.mp hx).2
    rw [l6_sum_units_eq_zero η ψ x r hr hrx, mul_zero]
  rw [h1, Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_sub_distrib, hfirst, hsecond, sub_zero]

private theorem l6_gaussSum_ne_zero [Fintype A] (η : Aˣ →* ℂˣ) (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive)
    (hη : ∀ y : A, ¬ IsUnit y → ∃ r : Aˣ, η r ≠ 1 ∧ (r : A) * y = y) :
    ∑ u : Aˣ, ((η u : ℂˣ) : ℂ) * ψ u ≠ 0 := by
  intro h
  have hcard := l6_gaussSum_mul_eq_card η ψ hψ hη
  rw [h, zero_mul] at hcard
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero hcard.symm

end L6GaussCore

section L6Fibre

private theorem l6_sum_comp_ne_zero {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (π : G →* H) (hπ : Function.Surjective π) (f : H → ℂ) (hf : ∑ b : H, f b ≠ 0) :
    ∑ a : G, f (π a) ≠ 0 := by
  classical
  have hfib : ∀ b : H, (Finset.univ.filter fun a : G => π a = b).card
      = (Finset.univ.filter fun a : G => π a = 1).card := by
    intro b
    obtain ⟨g₀, rfl⟩ := hπ b
    have himage : (Finset.univ.filter fun a : G => π a = π g₀)
        = (Finset.univ.filter fun a : G => π a = 1).image (fun k : G => k * g₀) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        refine ⟨a * g₀⁻¹, ?_, inv_mul_cancel_right a g₀⟩
        rw [map_mul, map_inv, h, mul_inv_cancel]
      · rintro ⟨k, hk, rfl⟩
        rw [map_mul, hk, one_mul]
    rw [himage, Finset.card_image_of_injective _ (mul_left_injective g₀)]
  have hN : (Finset.univ.filter fun a : G => π a = 1).card ≠ 0 :=
    Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, map_one π⟩)
  have hcomp : ∑ a : G, f (π a)
      = ((Finset.univ.filter fun a : G => π a = 1).card : ℂ) * ∑ b : H, f b := by
    rw [← Finset.sum_fiberwise' Finset.univ π f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_const, hfib b, nsmul_eq_mul]
  rw [hcomp]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hN) hf

end L6Fibre

section L6LocalRing

set_option maxSynthPendingDepth 3

open AutomorphicForm.GaussTwist

variable (A : Type*) [CommRing A] [IsLocalRing A]

private theorem units_map_quotient_maximalIdeal_pow_surjective (n : ℕ) :
    Function.Surjective
      (Units.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n)).toMonoidHom) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hsub : Subsingleton (A ⧸ (IsLocalRing.maximalIdeal A) ^ n) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [hn, pow_zero, Ideal.one_eq_top])
    exact fun y => ⟨1, Subsingleton.elim _ _⟩
  · refine IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective ?_
    refine isLocalHom_of_le_jacobson_bot _ ?_
    calc (IsLocalRing.maximalIdeal A) ^ n
        ≤ IsLocalRing.maximalIdeal A := Ideal.pow_le_self hn.ne'
      _ = Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm

private theorem unitQuotLift_spec (n : ℕ) (x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) :
    Units.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n)).toMonoidHom
      (unitQuotLift A n x) = x :=
  Function.surjInv_eq (units_map_quotient_maximalIdeal_pow_surjective A n) x

private theorem mk_coe_unitQuotLift (n : ℕ) (x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) (unitQuotLift A n x : A)
      = ((x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) : A ⧸ (IsLocalRing.maximalIdeal A) ^ n) :=
  congrArg Units.val (unitQuotLift_spec A n x)

end L6LocalRing

section L6Local

set_option maxSynthPendingDepth 3

open IsDedekindDomain AutomorphicForm.GaussTwist

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

private theorem valued_localUnif : Valued.v (localUnif K v) = WithZero.exp (-1 : ℤ) := by
  unfold localUnif
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_exists_uniformizer K).choose_spec

private theorem le_exp_neg_one_of_lt_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) :
    γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, γ = WithZero.exp m := ⟨WithZero.log γ, (WithZero.exp_log h0).symm⟩
    subst hm
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    exact WithZero.exp_le_exp.mpr (by omega)

private theorem valued_coe_le_exp_neg_one_of_mem_maximalIdeal {x : v.adicCompletionIntegers K}
    (hx : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ WithZero.exp (-1 : ℤ) := by
  refine le_exp_neg_one_of_lt_one (lt_of_le_of_ne
    ((HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp x.2) fun h => ?_)
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx))
    (isUnit_of_valued_coe_eq_one K v h)

private theorem valued_coe_le_exp_neg_of_mem_maximalIdeal_pow {n : ℕ} {x : v.adicCompletionIntegers K}
    (hx : x ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K)
      ≤ WithZero.exp (-(n : ℤ)) := by
  induction n generalizing x with
  | zero =>
      rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp x.2
  | succ n ih =>
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun m hm y hy => ?_) (fun y z hy hz => ?_)
      · rw [show ((m * y : v.adicCompletionIntegers K) : v.adicCompletion K)
            = (m : v.adicCompletion K) * y from rfl, map_mul, Nat.cast_succ, neg_add,
          WithZero.exp_add]
        exact mul_le_mul' (ih hm) (valued_coe_le_exp_neg_one_of_mem_maximalIdeal K v hy)
      · rw [show ((y + z : v.adicCompletionIntegers K) : v.adicCompletion K)
            = (y : v.adicCompletion K) + z from rfl]
        exact Valuation.map_add_le _ hy hz

private theorem valued_coe_sub_le_of_mk_eq {n : ℕ} {x y : v.adicCompletionIntegers K}
    (h : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n) x
      = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n) y) :
    Valued.v ((x : v.adicCompletion K) - y) ≤ WithZero.exp (-(n : ℤ)) := by
  have h' := valued_coe_le_exp_neg_of_mem_maximalIdeal_pow K v (Ideal.Quotient.eq.mp h)
  rwa [AddSubgroupClass.coe_sub] at h'

end L6Local

section L6Descent

set_option maxSynthPendingDepth 3

open IsDedekindDomain AutomorphicForm.GaussTwist

private theorem l6_finite_quotient (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Finite ((𝔭.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ n) :=
  IsLocalRing.isOpen_iff_finite_quotient.mp
    (IsLocalRing.isOpen_maximalIdeal_pow (𝔭.adicCompletionIntegers F) n)

private theorem l6_valued_localUnif_inv_pow (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (L : ℕ) :
    Valued.v ((localUnif F 𝔭)⁻¹ ^ L) = WithZero.exp (L : ℤ) := by
  rw [map_pow, map_inv₀, valued_localUnif F 𝔭, WithZero.exp_neg, inv_inv, ← WithZero.exp_nsmul,
    nsmul_one]

private theorem l6_mem_maximalIdeal_pow_of_valued_le (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (n : ℕ) (x : 𝔭.adicCompletionIntegers F)
    (hx : Valued.v ((x : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)
      ≤ WithZero.exp (-(n : ℤ))) :
    x ∈ (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ n := by
  have hϖv : Valued.v (localUnif F 𝔭) = WithZero.exp (-1 : ℤ) := valued_localUnif F 𝔭
  have hϖint : localUnif F 𝔭 ∈ 𝔭.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hϖv, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  have hϖ0 : localUnif F 𝔭 ≠ 0 := fun h => by
    rw [h, map_zero] at hϖv
    exact WithZero.exp_ne_zero hϖv.symm
  set ϖ : 𝔭.adicCompletionIntegers F := ⟨localUnif F 𝔭, hϖint⟩
  have hϖmem : ϖ ∈ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := valued_coe_eq_one_of_isUnit F 𝔭 hu
    rw [show ((ϖ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) = localUnif F 𝔭 from rfl,
      hϖv] at h1
    exact absurd h1 (ne_of_lt (by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by norm_num)))
  have hu : (x : 𝔭.adicCompletion F) * (localUnif F 𝔭)⁻¹ ^ n ∈ 𝔭.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, l6_valued_localUnif_inv_pow]
    calc Valued.v (x : 𝔭.adicCompletion F) * WithZero.exp (n : ℤ)
        ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) := mul_le_mul_left hx _
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  have hx_eq : x = ϖ ^ n * ⟨_, hu⟩ := by
    apply Subtype.ext
    show (x : 𝔭.adicCompletion F)
      = (localUnif F 𝔭) ^ n * ((x : 𝔭.adicCompletion F) * (localUnif F 𝔭)⁻¹ ^ n)
    rw [inv_pow, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero n hϖ0), mul_one]
  rw [hx_eq]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖmem n)

private noncomputable abbrev l6Red (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (𝔭.adicCompletionIntegers F)ˣ →*
      ((𝔭.adicCompletionIntegers F) ⧸
        (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ n)ˣ :=
  Units.map (Ideal.Quotient.mk
    ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ n)).toMonoidHom

private noncomputable def l6EtaBar (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (χ : (𝔭.adicCompletionIntegers F)ˣ →* ℂˣ) (c : ℕ)
    (hχ : ∀ r : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-(c : ℤ)) → χ r = 1) :
    ((𝔭.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)ˣ →* ℂˣ :=
  MonoidHom.liftOfRightInverse (l6Red F 𝔭 c) (unitQuotLift (𝔭.adicCompletionIntegers F) c)
    (fun w => unitQuotLift_spec (𝔭.adicCompletionIntegers F) c w)
    ⟨χ, fun r hr => by
      rw [MonoidHom.mem_ker] at hr ⊢
      refine hχ r ?_
      have h : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)
            (r : 𝔭.adicCompletionIntegers F)
          = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)
            1 := by
        rw [map_one]
        exact congrArg Units.val hr
      simpa using valued_coe_sub_le_of_mk_eq F 𝔭 h⟩

private theorem l6EtaBar_apply (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (χ : (𝔭.adicCompletionIntegers F)ˣ →* ℂˣ) (c : ℕ)
    (hχ : ∀ r : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-(c : ℤ)) → χ r = 1)
    (r : (𝔭.adicCompletionIntegers F)ˣ) :
    l6EtaBar F 𝔭 χ c hχ (l6Red F 𝔭 c r) = χ r :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ r

private theorem l6_theta_congr (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (θ : AddChar (𝔭.adicCompletion F) ℂ) (c d L : ℕ)
    (hL : L = c + d)
    (hθ : ∀ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp (d : ℤ) → θ y = 1)
    (x y : 𝔭.adicCompletionIntegers F)
    (hxy : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c) x
      = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c) y) :
    θ ((x : 𝔭.adicCompletion F) * (localUnif F 𝔭)⁻¹ ^ L)
      = θ ((y : 𝔭.adicCompletion F) * (localUnif F 𝔭)⁻¹ ^ L) := by
  have hv : Valued.v (((x : 𝔭.adicCompletion F) - y) * (localUnif F 𝔭)⁻¹ ^ L)
      ≤ WithZero.exp (d : ℤ) := by
    rw [map_mul, l6_valued_localUnif_inv_pow]
    calc Valued.v ((x : 𝔭.adicCompletion F) - y) * WithZero.exp (L : ℤ)
        ≤ WithZero.exp (-(c : ℤ)) * WithZero.exp (L : ℤ) :=
          mul_le_mul_left (valued_coe_sub_le_of_mk_eq F 𝔭 hxy) _
      _ = WithZero.exp (d : ℤ) := by
          rw [← WithZero.exp_add]
          congr 1
          omega
  calc θ ((x : 𝔭.adicCompletion F) * (localUnif F 𝔭)⁻¹ ^ L)
      = θ ((y : 𝔭.adicCompletion F) * (localUnif F 𝔭)⁻¹ ^ L
          + ((x : 𝔭.adicCompletion F) - y) * (localUnif F 𝔭)⁻¹ ^ L) := by
        congr 1
        ring
    _ = θ ((y : 𝔭.adicCompletion F) * (localUnif F 𝔭)⁻¹ ^ L) := by
        rw [AddChar.map_add_eq_mul, hθ _ hv, mul_one]

private noncomputable def l6Sec (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (c : ℕ) :
    (𝔭.adicCompletionIntegers F) ⧸ (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c
      → 𝔭.adicCompletionIntegers F :=
  Function.surjInv (Ideal.Quotient.mk_surjective
    (I := (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c))

private theorem l6Sec_spec (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (a : (𝔭.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)
      (l6Sec F 𝔭 c a) = a :=
  Function.surjInv_eq _ a

private noncomputable def l6PsiBar (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (θ : AddChar (𝔭.adicCompletion F) ℂ) (c d L : ℕ)
    (hL : L = c + d)
    (hθ : ∀ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp (d : ℤ) → θ y = 1) :
    AddChar ((𝔭.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c) ℂ where
  toFun a := θ (((l6Sec F 𝔭 c a : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)
    * (localUnif F 𝔭)⁻¹ ^ L)
  map_zero_eq_one' := by
    show θ (((l6Sec F 𝔭 c 0 : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)
      * (localUnif F 𝔭)⁻¹ ^ L) = 1
    rw [l6_theta_congr F 𝔭 θ c d L hL hθ (l6Sec F 𝔭 c 0) 0 (by rw [l6Sec_spec, RingHom.map_zero]),
      ZeroMemClass.coe_zero, zero_mul, AddChar.map_zero_eq_one]
  map_add_eq_mul' a b := by
    show θ (((l6Sec F 𝔭 c (a + b) : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)
        * (localUnif F 𝔭)⁻¹ ^ L)
      = θ (((l6Sec F 𝔭 c a : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)
          * (localUnif F 𝔭)⁻¹ ^ L)
        * θ (((l6Sec F 𝔭 c b : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)
          * (localUnif F 𝔭)⁻¹ ^ L)
    rw [l6_theta_congr F 𝔭 θ c d L hL hθ (l6Sec F 𝔭 c (a + b)) (l6Sec F 𝔭 c a + l6Sec F 𝔭 c b)
        (by rw [l6Sec_spec, RingHom.map_add, l6Sec_spec, l6Sec_spec]),
      AddMemClass.coe_add, add_mul]
    exact AddChar.map_add_eq_mul θ _ _

private theorem l6PsiBar_mk (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (θ : AddChar (𝔭.adicCompletion F) ℂ) (c d L : ℕ)
    (hL : L = c + d)
    (hθ : ∀ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp (d : ℤ) → θ y = 1)
    (x : 𝔭.adicCompletionIntegers F) :
    l6PsiBar F 𝔭 θ c d L hL hθ
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c) x)
      = θ ((x : 𝔭.adicCompletion F) * (localUnif F 𝔭)⁻¹ ^ L) := by
  show θ (((l6Sec F 𝔭 c (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c) x) :
        𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) * (localUnif F 𝔭)⁻¹ ^ L) = _
  exact l6_theta_congr F 𝔭 θ c d L hL hθ _ x (l6Sec_spec F 𝔭 c _)

private theorem l6PsiBar_isPrimitive (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (θ : AddChar (𝔭.adicCompletion F) ℂ) (c d L : ℕ)
    (hL : L = c + d)
    (hθ : ∀ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp (d : ℤ) → θ y = 1)
    (hθ' : ∃ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp ((d : ℤ) + 1) ∧ θ y ≠ 1) :
    (l6PsiBar F 𝔭 θ c d L hL hθ).IsPrimitive := by
  intro a ha hma
  obtain ⟨y, hyv, hθy⟩ := hθ'
  obtain ⟨x₀, hx₀a⟩ : ∃ x₀ : 𝔭.adicCompletionIntegers F,
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c) x₀ = a :=
    ⟨l6Sec F 𝔭 c a, l6Sec_spec F 𝔭 c a⟩
  have hx₀v : ¬ Valued.v ((x₀ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)
      ≤ WithZero.exp (-(c : ℤ)) := fun h =>
    ha (by
      rw [← hx₀a, Ideal.Quotient.eq_zero_iff_mem]
      exact l6_mem_maximalIdeal_pow_of_valued_le F 𝔭 c x₀ h)
  have hx₀0 : ((x₀ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) ≠ 0 := fun h =>
    hx₀v (by
      rw [h, map_zero]
      exact zero_le')
  have hy0 : y ≠ 0 := fun h => hθy (by rw [h, AddChar.map_zero_eq_one])
  have hw : Valued.v ((localUnif F 𝔭)⁻¹ ^ L) = WithZero.exp (L : ℤ) :=
    l6_valued_localUnif_inv_pow F 𝔭 L
  have hw0 : (localUnif F 𝔭)⁻¹ ^ L ≠ 0 := fun h => by
    rw [h, map_zero] at hw
    exact WithZero.exp_ne_zero hw.symm

  obtain ⟨kx, hkx⟩ : ∃ k : ℤ,
      Valued.v ((x₀ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) = WithZero.exp k :=
    ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx₀0)).symm⟩
  obtain ⟨ky, hky⟩ : ∃ k : ℤ, Valued.v y = WithZero.exp k :=
    ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hy0)).symm⟩
  have hkx' : -(c : ℤ) < kx := by
    rw [hkx, not_le, WithZero.exp_lt_exp] at hx₀v
    exact hx₀v
  have hky' : ky ≤ (d : ℤ) + 1 := by rwa [hky, WithZero.exp_le_exp] at hyv

  obtain ⟨b, hbdef⟩ : ∃ b : 𝔭.adicCompletion F, b = y * ((localUnif F 𝔭)⁻¹ ^ L)⁻¹
      * ((x₀ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)⁻¹ := ⟨_, rfl⟩
  have hb : b ∈ 𝔭.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hbdef, map_mul, map_mul, map_inv₀, map_inv₀,
      hky, hw, hkx, ← WithZero.exp_neg, ← WithZero.exp_neg, ← WithZero.exp_add,
      ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

  apply hθy
  have h1 := DFunLike.congr_fun hma
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c) ⟨b, hb⟩)
  rw [AddChar.mulShift_apply, AddChar.one_apply] at h1
  have h2 : a * Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)
        ⟨b, hb⟩
      = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)
          (x₀ * ⟨b, hb⟩) := by
    rw [← hx₀a]
    exact (RingHom.map_mul
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c))
      x₀ ⟨b, hb⟩).symm
  rw [h2, l6PsiBar_mk F 𝔭 θ c d L hL hθ (x₀ * ⟨b, hb⟩)] at h1
  have h3 : (((x₀ * ⟨b, hb⟩ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F))
      * (localUnif F 𝔭)⁻¹ ^ L = y := by
    rw [MulMemClass.coe_mul]
    show ((x₀ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) * b * (localUnif F 𝔭)⁻¹ ^ L = y
    rw [hbdef]
    calc ((x₀ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)
            * (y * ((localUnif F 𝔭)⁻¹ ^ L)⁻¹
              * ((x₀ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)⁻¹)
            * (localUnif F 𝔭)⁻¹ ^ L
          = y * (((x₀ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)
              * ((x₀ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)⁻¹)
            * (((localUnif F 𝔭)⁻¹ ^ L)⁻¹ * (localUnif F 𝔭)⁻¹ ^ L) := by ring
      _ = y := by rw [mul_inv_cancel₀ hx₀0, inv_mul_cancel₀ hw0, mul_one, mul_one]
  rw [h3] at h1
  exact h1

private theorem l6EtaBar_fix (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (χ : (𝔭.adicCompletionIntegers F)ˣ →* ℂˣ) (c : ℕ)
    (hχ : ∀ r : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-(c : ℤ)) → χ r = 1)
    (hprim : ∃ r : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-((c : ℤ) - 1)) ∧ χ r ≠ 1)
    (y : (𝔭.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)
    (hy : ¬ IsUnit y) :
    ∃ r : ((𝔭.adicCompletionIntegers F) ⧸
        (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)ˣ,
      l6EtaBar F 𝔭 χ c hχ r ≠ 1
        ∧ (r : (𝔭.adicCompletionIntegers F) ⧸
            (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c) * y = y := by
  obtain ⟨r, hrv, hrχ⟩ := hprim
  refine ⟨l6Red F 𝔭 c r, by rwa [l6EtaBar_apply], ?_⟩
  set yt : 𝔭.adicCompletionIntegers F := l6Sec F 𝔭 c y
  have hyt : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c) yt
      = y := l6Sec_spec F 𝔭 c y
  have hytm : yt ∈ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hy (by
      rw [← hyt]
      exact hu.map _)
  have hmem : ((r : 𝔭.adicCompletionIntegers F) - 1) * yt
      ∈ (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c := by
    refine l6_mem_maximalIdeal_pow_of_valued_le F 𝔭 c _ ?_
    rw [show ((((r : 𝔭.adicCompletionIntegers F) - 1) * yt : 𝔭.adicCompletionIntegers F)
          : 𝔭.adicCompletion F)
        = (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          * ((yt : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) from rfl, map_mul]
    calc Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          * Valued.v ((yt : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)
        ≤ WithZero.exp (-((c : ℤ) - 1)) * WithZero.exp (-1 : ℤ) :=
          mul_le_mul' hrv (valued_coe_le_exp_neg_one_of_mem_maximalIdeal F 𝔭 hytm)
      _ = WithZero.exp (-(c : ℤ)) := by
          rw [← WithZero.exp_add]
          congr 1
          ring
  rw [← hyt, show ((l6Red F 𝔭 c r : ((𝔭.adicCompletionIntegers F) ⧸
        (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)ˣ)
          : (𝔭.adicCompletionIntegers F) ⧸
            (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)
      = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)
          (r : 𝔭.adicCompletionIntegers F) from rfl,
    ← map_mul, Ideal.Quotient.eq]
  have e : (r : 𝔭.adicCompletionIntegers F) * yt - yt
      = ((r : 𝔭.adicCompletionIntegers F) - 1) * yt := by ring
  rw [e]
  exact hmem

private theorem l6_level_c_sum_ne_zero (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (χ : (𝔭.adicCompletionIntegers F)ˣ →* ℂˣ) (c : ℕ)
    (hχ : ∀ r : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-(c : ℤ)) → χ r = 1)
    (hprim : ∃ r : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-((c : ℤ) - 1)) ∧ χ r ≠ 1)
    (θ : AddChar (𝔭.adicCompletion F) ℂ) (d : ℕ)
    (hθ : ∀ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp (d : ℤ) → θ y = 1)
    (hθ' : ∃ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp ((d : ℤ) + 1) ∧ θ y ≠ 1)
    (L : ℕ) (hL : L = c + d)
    [Fintype ((𝔭.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)]
    [Fintype ((𝔭.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)ˣ] :
    ∑ a : ((𝔭.adicCompletionIntegers F) ⧸
        (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)ˣ,
      ((l6EtaBar F 𝔭 χ c hχ a : ℂˣ) : ℂ) * l6PsiBar F 𝔭 θ c d L hL hθ a ≠ 0 :=
  l6_gaussSum_ne_zero (l6EtaBar F 𝔭 χ c hχ) (l6PsiBar F 𝔭 θ c d L hL hθ)
    (l6PsiBar_isPrimitive F 𝔭 θ c d L hL hθ hθ') (l6EtaBar_fix F 𝔭 χ c hχ hprim)

private theorem l6_level_sum_ne_zero (F : Type) [Field F] [NumberField F]
    (𝔭 : HeightOneSpectrum (𝓞 F)) (χ : (𝔭.adicCompletionIntegers F)ˣ →* ℂˣ) (c : ℕ)
    (hχ : ∀ r : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-(c : ℤ)) → χ r = 1)
    (hprim : ∃ r : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-((c : ℤ) - 1)) ∧ χ r ≠ 1)
    (θ : AddChar (𝔭.adicCompletion F) ℂ) (d : ℕ)
    (hθ : ∀ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp (d : ℤ) → θ y = 1)
    (hθ' : ∃ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp ((d : ℤ) + 1) ∧ θ y ≠ 1)
    (L : ℕ) (hL : L = c + d)
    [Fintype ((𝔭.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ L)ˣ] :
    ∑ w : ((𝔭.adicCompletionIntegers F) ⧸
        (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ L)ˣ,
      ((χ (unitQuotLift (𝔭.adicCompletionIntegers F) L w) : ℂˣ) : ℂ) *
        θ ((((unitQuotLift (𝔭.adicCompletionIntegers F) L w : (𝔭.adicCompletionIntegers F)ˣ) :
                𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) *
              (localUnif F 𝔭)⁻¹ ^ L) ≠ 0 := by

  haveI : Finite ((𝔭.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c) := l6_finite_quotient F 𝔭 c
  letI : Fintype ((𝔭.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c) := Fintype.ofFinite _
  letI : Fintype ((𝔭.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)ˣ := Fintype.ofFinite _

  have hcL : c ≤ L := by omega
  let π : ((𝔭.adicCompletionIntegers F) ⧸
        (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ L)ˣ →*
      ((𝔭.adicCompletionIntegers F) ⧸
        (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)ˣ :=
    Units.map (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F))
        hcL)).toMonoidHom
  have hπred : ∀ r : (𝔭.adicCompletionIntegers F)ˣ, π (l6Red F 𝔭 L r) = l6Red F 𝔭 c r :=
    fun r => Units.ext rfl
  have hπ : Function.Surjective π := by
    intro a
    obtain ⟨r, hr⟩ :=
      units_map_quotient_maximalIdeal_pow_surjective (𝔭.adicCompletionIntegers F) c a
    exact ⟨l6Red F 𝔭 L r, by rw [hπred]; exact hr⟩

  have hsummand : ∀ w : ((𝔭.adicCompletionIntegers F) ⧸
        (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ L)ˣ,
      ((l6EtaBar F 𝔭 χ c hχ (π w) : ℂˣ) : ℂ) * l6PsiBar F 𝔭 θ c d L hL hθ (π w)
        = ((χ (unitQuotLift (𝔭.adicCompletionIntegers F) L w) : ℂˣ) : ℂ) *
          θ ((((unitQuotLift (𝔭.adicCompletionIntegers F) L w : (𝔭.adicCompletionIntegers F)ˣ) :
                𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) *
              (localUnif F 𝔭)⁻¹ ^ L) := by
    intro w
    have hw : l6Red F 𝔭 L (unitQuotLift (𝔭.adicCompletionIntegers F) L w) = w :=
      unitQuotLift_spec (𝔭.adicCompletionIntegers F) L w
    have e1 : π w = l6Red F 𝔭 c (unitQuotLift (𝔭.adicCompletionIntegers F) L w) :=
      (congrArg π hw).symm.trans (hπred _)
    have e0 : ((l6Red F 𝔭 c (unitQuotLift (𝔭.adicCompletionIntegers F) L w) :
          ((𝔭.adicCompletionIntegers F) ⧸
            (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)ˣ) :
            (𝔭.adicCompletionIntegers F) ⧸
              (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)
        = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ c)
            ((unitQuotLift (𝔭.adicCompletionIntegers F) L w : (𝔭.adicCompletionIntegers F)ˣ) :
              𝔭.adicCompletionIntegers F) := rfl
    have e3 : ((l6EtaBar F 𝔭 χ c hχ
            (l6Red F 𝔭 c (unitQuotLift (𝔭.adicCompletionIntegers F) L w)) : ℂˣ) : ℂ)
        = ((χ (unitQuotLift (𝔭.adicCompletionIntegers F) L w) : ℂˣ) : ℂ) :=
      congrArg Units.val (l6EtaBar_apply F 𝔭 χ c hχ _)
    have e4 : l6PsiBar F 𝔭 θ c d L hL hθ
          (l6Red F 𝔭 c (unitQuotLift (𝔭.adicCompletionIntegers F) L w))
        = θ ((((unitQuotLift (𝔭.adicCompletionIntegers F) L w : (𝔭.adicCompletionIntegers F)ˣ) :
                𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) *
              (localUnif F 𝔭)⁻¹ ^ L) :=
      (congrArg (l6PsiBar F 𝔭 θ c d L hL hθ) e0).trans
        (l6PsiBar_mk F 𝔭 θ c d L hL hθ _)
    exact (congrArg (fun a => ((l6EtaBar F 𝔭 χ c hχ a : ℂˣ) : ℂ)
        * l6PsiBar F 𝔭 θ c d L hL hθ a) e1).trans (congr (congrArg HMul.hMul e3) e4)
  have hsum : (∑ w : ((𝔭.adicCompletionIntegers F) ⧸
        (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ L)ˣ,
      ((χ (unitQuotLift (𝔭.adicCompletionIntegers F) L w) : ℂˣ) : ℂ) *
        θ ((((unitQuotLift (𝔭.adicCompletionIntegers F) L w : (𝔭.adicCompletionIntegers F)ˣ) :
                𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) *
              (localUnif F 𝔭)⁻¹ ^ L))
      = ∑ w : ((𝔭.adicCompletionIntegers F) ⧸
          (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F)) ^ L)ˣ,
        ((l6EtaBar F 𝔭 χ c hχ (π w) : ℂˣ) : ℂ) * l6PsiBar F 𝔭 θ c d L hL hθ (π w) :=
    Finset.sum_congr rfl (fun w _ => (hsummand w).symm)
  rw [hsum]
  exact l6_sum_comp_ne_zero π hπ
    (fun a => ((l6EtaBar F 𝔭 χ c hχ a : ℂˣ) : ℂ) * l6PsiBar F 𝔭 θ c d L hL hθ a)
    (l6_level_c_sum_ne_zero F 𝔭 χ c hχ hprim θ d hθ hθ' L hL)

private theorem l6_leg (F : Type) [Field F] [NumberField F]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (χ : (𝔭.adicCompletionIntegers F)ˣ →* ℂˣ)
    (c : ℕ) (_hc : 1 ≤ c)
    (hχ : ∀ r : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-(c : ℤ)) → χ r = 1)
    (hprim : ∃ r : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-((c : ℤ) - 1)) ∧ χ r ≠ 1)
    (θ : AddChar (𝔭.adicCompletion F) ℂ) (d : ℕ)
    (hθ : ∀ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp (d : ℤ) → θ y = 1)
    (hθ' : ∃ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp ((d : ℤ) + 1) ∧ θ y ≠ 1)
    (𝔣₀ : Ideal (𝓞 F)) (hL : HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀ = c + d)
    [Fintype (AutomorphicForm.GaussTwist.LocalGaussFactor F 𝔣₀ 𝔭)] :
    ∑ w : AutomorphicForm.GaussTwist.LocalGaussFactor F 𝔣₀ 𝔭,
      ((χ (AutomorphicForm.GaussTwist.unitQuotLift (𝔭.adicCompletionIntegers F)
          (HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀) w) : ℂˣ) : ℂ) *
        θ ((((AutomorphicForm.GaussTwist.unitQuotLift (𝔭.adicCompletionIntegers F)
                (HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀) w : (𝔭.adicCompletionIntegers F)ˣ) :
                𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) *
              (AutomorphicForm.GaussTwist.gaussUnif F 𝔭)⁻¹ ^ HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀) ≠ 0 :=
  l6_level_sum_ne_zero F 𝔭 χ c hχ hprim θ d hθ hθ' (HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀) hL

end L6Descent

private theorem leg_L6_local_gauss (F : Type) [Field F] [NumberField F]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (χ : (𝔭.adicCompletionIntegers F)ˣ →* ℂˣ)
    (c : ℕ) (hc : 1 ≤ c)
    (hχ : ∀ r : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-(c : ℤ)) → χ r = 1)
    (hprim : ∃ r : (𝔭.adicCompletionIntegers F)ˣ,
      Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
          ≤ WithZero.exp (-((c : ℤ) - 1)) ∧ χ r ≠ 1)
    (θ : AddChar (𝔭.adicCompletion F) ℂ) (d : ℕ)
    (hθ : ∀ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp (d : ℤ) → θ y = 1)
    (hθ' : ∃ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp ((d : ℤ) + 1) ∧ θ y ≠ 1)
    (𝔣₀ : Ideal (𝓞 F)) (hL : HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀ = c + d)
    [Fintype (AutomorphicForm.GaussTwist.LocalGaussFactor F 𝔣₀ 𝔭)] :
    ∑ w : AutomorphicForm.GaussTwist.LocalGaussFactor F 𝔣₀ 𝔭,
      ((χ (AutomorphicForm.GaussTwist.unitQuotLift (𝔭.adicCompletionIntegers F)
          (HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀) w) : ℂˣ) : ℂ) *
        θ ((((AutomorphicForm.GaussTwist.unitQuotLift (𝔭.adicCompletionIntegers F)
                (HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀) w : (𝔭.adicCompletionIntegers F)ˣ) :
                𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) *
              (AutomorphicForm.GaussTwist.gaussUnif F 𝔭)⁻¹ ^ HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀) ≠ 0 := by
  exact l6_leg F 𝔭 χ c hc hχ hprim θ d hθ hθ' 𝔣₀ hL

private theorem leg_L6b_factor (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣₀ : Ideal (𝓞 F)) (α : F) (tf : FiniteAdeleRing (𝓞 F) F) :
    ∑ u : AutomorphicForm.GaussTwist.GaussIndex F 𝔣₀,
        AutomorphicForm.GaussTwist.gaussWt F η 𝔣₀ u *
          NumberField.StandardAddChar.stdAddChar F (algebraMap F (AdeleRing (𝓞 F) F) α *
            gsolFinAdele F (tf * AutomorphicForm.GaussTwist.adeleOn
              (AutomorphicForm.GaussTwist.modulusPrimes F 𝔣₀) (AutomorphicForm.GaussTwist.gaussY F 𝔣₀ u)))
      = ∏ 𝔭 : AutomorphicForm.GaussTwist.modulusPrimes F 𝔣₀,
          ∑ w : AutomorphicForm.GaussTwist.LocalGaussFactor F 𝔣₀ 𝔭.1,
            ((gsolEtaLoc F η 𝔭.1 (AutomorphicForm.GaussTwist.unitQuotLift (𝔭.1.adicCompletionIntegers F)
                (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀) w) : ℂˣ) : ℂ) *
              NumberField.StandardAddChar.psiLocal F 𝔭.1
                ((algebraMap F (𝔭.1.adicCompletion F) α * tf 𝔭.1) *
                  ((((AutomorphicForm.GaussTwist.unitQuotLift (𝔭.1.adicCompletionIntegers F)
                        (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀) w :
                        (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F) :
                        𝔭.1.adicCompletion F) *
                    (AutomorphicForm.GaussTwist.gaussUnif F 𝔭.1)⁻¹ ^
                      HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀)) := by
  exact l6b_main F η 𝔣₀ α tf

namespace GsolGlue

open IsDedekindDomain NumberField AutomorphicForm

private theorem glue_left_invariant (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Φ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    R.toFun (globalPoints (𝓞 F) F γ * g) = R.toFun g :=
  R.left_invariant γ g

private theorem glue_rat_unipotent (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (β : F) (g : AdelicGL2 (𝓞 F) F) :
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g := by
  rw [← WhittakerTranslate.globalPoints_unipotentGL2 F β]
  exact hleft _ g

private theorem glue_cusp (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Φ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ R.toFun 0 g = 0 :=
  (whittakerCoefficient_zero_eq_constantTerm F pins ψ R.toFun g).trans (R.smoothCusp.1.2 g)

private theorem glue_continuous_unipotentGL2 (F : Type) [Field F] [NumberField F] :
    Continuous fun t : AdeleRing (𝓞 F) F => (unipotentGL2 t : AdelicGL2 (𝓞 F) F) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop
  · have hinv : ∀ s : AdeleRing (𝓞 F) F,
        ((unipotentGL2 s)⁻¹ : AdelicGL2 (𝓞 F) F) = unipotentGL2 (-s) := fun s =>
      inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
    simp_rw [hinv]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop

private theorem glue_continuous_slice (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    Continuous (fun x : AdeleRing (𝓞 F) F => φ (unipotentGL2 x * g)) :=
  hφ.comp ((glue_continuous_unipotentGL2 F).mul continuous_const)

private theorem glue_exists_ne_zero_of_hasSum {ι : Type} (f : ι → ℂ) (s : ℂ) (hf : HasSum f s)
    (hs : s ≠ 0) : ∃ i, f i ≠ 0 := by
  by_contra h
  have h0 : f = fun _ => (0 : ℂ) := funext fun i => Classical.byContradiction fun hi => h ⟨i, hi⟩
  rw [h0] at hf
  exact hs (hf.unique hasSum_zero)

private theorem glue_z_ne_zero (F : Type) [Field F] [NumberField F] (α : F) (hα : α ≠ 0)
    (tf : FiniteAdeleRing (𝓞 F) F) (𝔭 : HeightOneSpectrum (𝓞 F)) (htf : tf 𝔭 ≠ 0) :
    algebraMap F (𝔭.adicCompletion F) α * tf 𝔭 ≠ 0 :=
  mul_ne_zero ((map_ne_zero (algebraMap F (𝔭.adicCompletion F))).mpr hα) htf

private theorem glue_adeleOn_apply (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) (w : HeightOneSpectrum (𝓞 F)) :
    GaussTwist.adeleOn S y w = if w ∈ S then y w else 0 := rfl

private theorem glue_adeleOn_support (F : Type) [Field F] [NumberField F] (𝔣₀ : Ideal (𝓞 F))
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (hS : GaussTwist.modulusPrimes F 𝔣₀ = S₀)
    (u : GaussTwist.GaussIndex F 𝔣₀) (𝔮 : HeightOneSpectrum (𝓞 F)) (h𝔮 : 𝔮 ∉ S₀) :
    GaussTwist.adeleOn (GaussTwist.modulusPrimes F 𝔣₀) (GaussTwist.gaussY F 𝔣₀ u) 𝔮 = 0 := by
  subst hS
  rw [glue_adeleOn_apply, if_neg h𝔮]

end GsolGlue

private theorem leg_left_invariant (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Φ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    R.toFun (globalPoints (𝓞 F) F γ * g) = R.toFun g := by
  exact GsolGlue.glue_left_invariant F pins Φ R γ g

private theorem leg_rat_unipotent (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (β : F) (g : AdelicGL2 (𝓞 F) F) :
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g := by
  exact GsolGlue.glue_rat_unipotent F φ hleft β g

private theorem leg_cusp (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Φ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ R.toFun 0 g = 0 := by
  exact GsolGlue.glue_cusp F pins Φ R ψ g

private theorem leg_continuous_slice (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    Continuous (fun x : AdeleRing (𝓞 F) F => φ (unipotentGL2 x * g)) := by
  exact GsolGlue.glue_continuous_slice F φ hφ g

private theorem leg_exists_ne_zero_of_hasSum {ι : Type} (f : ι → ℂ) (s : ℂ) (hf : HasSum f s)
    (hs : s ≠ 0) : ∃ i, f i ≠ 0 := by
  exact GsolGlue.glue_exists_ne_zero_of_hasSum f s hf hs

private theorem leg_z_ne_zero (F : Type) [Field F] [NumberField F] (α : F) (hα : α ≠ 0)
    (tf : FiniteAdeleRing (𝓞 F) F) (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (htf : tf 𝔭 ≠ 0) :
    algebraMap F (𝔭.adicCompletion F) α * tf 𝔭 ≠ 0 := by
  exact GsolGlue.glue_z_ne_zero F α hα tf 𝔭 htf

private theorem leg_adeleOn_support (F : Type) [Field F] [NumberField F] (𝔣₀ : Ideal (𝓞 F))
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hS : AutomorphicForm.GaussTwist.modulusPrimes F 𝔣₀ = S₀)
    (u : AutomorphicForm.GaussTwist.GaussIndex F 𝔣₀) (𝔮 : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (h𝔮 : 𝔮 ∉ S₀) :
    AutomorphicForm.GaussTwist.adeleOn (AutomorphicForm.GaussTwist.modulusPrimes F 𝔣₀)
      (AutomorphicForm.GaussTwist.gaussY F 𝔣₀ u) 𝔮 = 0 := by
  exact GsolGlue.glue_adeleOn_support F 𝔣₀ S₀ hS u 𝔮 h𝔮

private theorem leg_L7_comb_zero (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣₀ : Ideal (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h3 : ∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F pins ψ φ α g)
    (hzero : AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣₀ φ = fun _ => (0 : ℂ))
    (α : F) (m : AdelicGL2 (𝓞 F) F) :
    ∑ u : AutomorphicForm.GaussTwist.GaussIndex F 𝔣₀, AutomorphicForm.GaussTwist.gaussWt F η 𝔣₀ u *
        whittakerCoefficient F pins ψ φ α (m * AutomorphicForm.GaussTwist.gaussTrans F 𝔣₀ u) = 0 := by
  have hcomb := whittakerCoefficient_comb_aux F pins ψ (AutomorphicForm.GaussTwist.gaussWt F η 𝔣₀)
    (AutomorphicForm.GaussTwist.gaussTrans F 𝔣₀) φ h3 α m
  have hfun : (fun x : AdelicGL2 (𝓞 F) F => ∑ v : AutomorphicForm.GaussTwist.GaussIndex F 𝔣₀,
      AutomorphicForm.GaussTwist.gaussWt F η 𝔣₀ v * φ (x * AutomorphicForm.GaussTwist.gaussTrans F 𝔣₀ v))
      = fun _ => (0 : ℂ) := hzero
  rw [hfun, whittakerCoefficient_zero] at hcomb
  exact hcomb.symm

private theorem leg_L7_term (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g)
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (𝔣₀ : Ideal (𝓞 F))
    (hS : AutomorphicForm.GaussTwist.modulusPrimes F 𝔣₀ = S₀)
    (m : AdelicGL2 (𝓞 F) F) (tf : FiniteAdeleRing (𝓞 F) F) (α : F)
    (hconj : ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ 𝔮, 𝔮 ∉ S₀ → y 𝔮 = 0) →
      m * AutomorphicForm.GaussTwist.finLift (unipotentGL2 y)
        = unipotentGL2 (gsolFinAdele F (tf * y)) * m)
    (u : AutomorphicForm.GaussTwist.GaussIndex F 𝔣₀) :
    AutomorphicForm.GaussTwist.gaussWt F η 𝔣₀ u *
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F))
          (NumberField.StandardAddChar.stdAddChar F) φ α (m * AutomorphicForm.GaussTwist.gaussTrans F 𝔣₀ u)
      = AutomorphicForm.GaussTwist.gaussWt F η 𝔣₀ u *
          NumberField.StandardAddChar.stdAddChar F (algebraMap F (AdeleRing (𝓞 F) F) α *
            gsolFinAdele F (tf * AutomorphicForm.GaussTwist.adeleOn (AutomorphicForm.GaussTwist.modulusPrimes F 𝔣₀)
              (AutomorphicForm.GaussTwist.gaussY F 𝔣₀ u))) *
          whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F))
            (NumberField.StandardAddChar.stdAddChar F) φ α m := by
  have hmt : m * AutomorphicForm.GaussTwist.gaussTrans F 𝔣₀ u
      = unipotentGL2 (gsolFinAdele F (tf * AutomorphicForm.GaussTwist.adeleOn
          (AutomorphicForm.GaussTwist.modulusPrimes F 𝔣₀) (AutomorphicForm.GaussTwist.gaussY F 𝔣₀ u))) * m :=
    hconj (AutomorphicForm.GaussTwist.adeleOn (AutomorphicForm.GaussTwist.modulusPrimes F 𝔣₀)
      (AutomorphicForm.GaussTwist.gaussY F 𝔣₀ u)) (fun 𝔮 h𝔮 => leg_adeleOn_support F 𝔣₀ S₀ hS u 𝔮 h𝔮)
  rw [hmt, leg_L3_translate F D U gen _
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar F) φ hφ α _ m]
  ring

private theorem leg_L7_local (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣₀ : Ideal (𝓞 F))
    (𝔭 : AutomorphicForm.GaussTwist.modulusPrimes F 𝔣₀) (c d : ℕ)
    (hmult : HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀ = c + d) (hc : 1 ≤ c)
    (htriv : ∀ r : (𝔭.1.adicCompletionIntegers F)ˣ,
        Valued.v (((r : 𝔭.1.adicCompletionIntegers F) : 𝔭.1.adicCompletion F) - 1)
            ≤ WithZero.exp (-(c : ℤ)) →
          gsolEtaLoc F η 𝔭.1 r = 1)
    (hprim : ∃ r : (𝔭.1.adicCompletionIntegers F)ˣ,
        Valued.v (((r : 𝔭.1.adicCompletionIntegers F) : 𝔭.1.adicCompletion F) - 1)
            ≤ WithZero.exp (-((c : ℤ) - 1)) ∧
          gsolEtaLoc F η 𝔭.1 r ≠ 1)
    (α : F) (tf : FiniteAdeleRing (𝓞 F) F)
    (hlev : (∀ y : 𝔭.1.adicCompletion F, Valued.v y ≤ WithZero.exp (d : ℤ) →
          NumberField.StandardAddChar.psiLocal F 𝔭.1 (algebraMap F (𝔭.1.adicCompletion F) α * tf 𝔭.1 * y) = 1) ∧
        ∃ y : 𝔭.1.adicCompletion F, Valued.v y ≤ WithZero.exp ((d : ℤ) + 1) ∧
          NumberField.StandardAddChar.psiLocal F 𝔭.1 (algebraMap F (𝔭.1.adicCompletion F) α * tf 𝔭.1 * y) ≠ 1) :
    ∑ w : AutomorphicForm.GaussTwist.LocalGaussFactor F 𝔣₀ 𝔭.1,
      ((gsolEtaLoc F η 𝔭.1 (AutomorphicForm.GaussTwist.unitQuotLift (𝔭.1.adicCompletionIntegers F)
          (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀) w) : ℂˣ) : ℂ) *
        NumberField.StandardAddChar.psiLocal F 𝔭.1
          ((algebraMap F (𝔭.1.adicCompletion F) α * tf 𝔭.1) *
            ((((AutomorphicForm.GaussTwist.unitQuotLift (𝔭.1.adicCompletionIntegers F)
                  (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀) w :
                  (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F) :
                  𝔭.1.adicCompletion F) *
              (AutomorphicForm.GaussTwist.gaussUnif F 𝔭.1)⁻¹ ^ HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣₀)) ≠ 0 := by
  have hθ : ∀ y : 𝔭.1.adicCompletion F, Valued.v y ≤ WithZero.exp (d : ℤ) →
      ((NumberField.StandardAddChar.psiLocal F 𝔭.1).compAddMonoidHom
        (AddMonoidHom.mulLeft (algebraMap F (𝔭.1.adicCompletion F) α * tf 𝔭.1))) y = 1 := by
    intro y hy
    simp only [AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_mulLeft]
    exact hlev.1 y hy
  have hθ' : ∃ y : 𝔭.1.adicCompletion F, Valued.v y ≤ WithZero.exp ((d : ℤ) + 1) ∧
      ((NumberField.StandardAddChar.psiLocal F 𝔭.1).compAddMonoidHom
        (AddMonoidHom.mulLeft (algebraMap F (𝔭.1.adicCompletion F) α * tf 𝔭.1))) y ≠ 1 := by
    obtain ⟨y, hy, hy1⟩ := hlev.2
    refine ⟨y, hy, ?_⟩
    simp only [AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_mulLeft]
    exact hy1
  have h := leg_L6_local_gauss F 𝔭.1 (gsolEtaLoc F η 𝔭.1) c hc htriv hprim
    ((NumberField.StandardAddChar.psiLocal F 𝔭.1).compAddMonoidHom
      (AddMonoidHom.mulLeft (algebraMap F (𝔭.1.adicCompletion F) α * tf 𝔭.1)))
    d hθ hθ' 𝔣₀ hmult
  simp only [AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_mulLeft] at h
  exact h

private theorem leg_L7_tail (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h3 : ∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F
      (productionPinsOf F D U gen (adelicBox F)) (NumberField.StandardAddChar.stdAddChar F) φ α g)
    (hφ : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g)
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (𝔣₀ : Ideal (𝓞 F))
    (cexp d : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ)
    (hS : AutomorphicForm.GaussTwist.modulusPrimes F 𝔣₀ = S₀)
    (hmult : ∀ 𝔭 ∈ S₀, HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀ = cexp 𝔭 + d 𝔭)
    (hc : ∀ 𝔭 ∈ S₀, 1 ≤ cexp 𝔭)
    (htriv : ∀ 𝔭 ∈ S₀, ∀ r : (𝔭.adicCompletionIntegers F)ˣ,
        Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
            ≤ WithZero.exp (-(cexp 𝔭 : ℤ)) →
          gsolEtaLoc F η 𝔭 r = 1)
    (hprim : ∀ 𝔭 ∈ S₀, ∃ r : (𝔭.adicCompletionIntegers F)ˣ,
        Valued.v (((r : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) - 1)
            ≤ WithZero.exp (-((cexp 𝔭 : ℤ) - 1)) ∧
          gsolEtaLoc F η 𝔭 r ≠ 1)
    (m : AdelicGL2 (𝓞 F) F) (tf : FiniteAdeleRing (𝓞 F) F) (α : F)
    (hα : whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F))
      (NumberField.StandardAddChar.stdAddChar F) φ α m ≠ 0)
    (hconj : ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ 𝔮, 𝔮 ∉ S₀ → y 𝔮 = 0) →
      m * AutomorphicForm.GaussTwist.finLift (unipotentGL2 y)
        = unipotentGL2 (gsolFinAdele F (tf * y)) * m)
    (hlev : ∀ 𝔭 ∈ S₀,
      (∀ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp (d 𝔭 : ℤ) →
          NumberField.StandardAddChar.psiLocal F 𝔭 (algebraMap F (𝔭.adicCompletion F) α * tf 𝔭 * y) = 1) ∧
        ∃ y : 𝔭.adicCompletion F, Valued.v y ≤ WithZero.exp ((d 𝔭 : ℤ) + 1) ∧
          NumberField.StandardAddChar.psiLocal F 𝔭 (algebraMap F (𝔭.adicCompletion F) α * tf 𝔭 * y) ≠ 1) :
    ∃ g : AdelicGL2 (𝓞 F) F, AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣₀ φ g ≠ 0 := by
  by_contra hnone
  have hzero : AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣₀ φ = fun _ => (0 : ℂ) := by
    funext g
    by_contra hg
    exact hnone ⟨g, hg⟩
  have h0 := leg_L7_comb_zero F (productionPinsOf F D U gen (adelicBox F))
    (NumberField.StandardAddChar.stdAddChar F) η 𝔣₀ φ h3 hzero α m
  simp only [leg_L7_term F D U gen η φ hφ S₀ 𝔣₀ hS m tf α hconj] at h0
  rw [← Finset.sum_mul] at h0

  have hG := (mul_eq_zero.1 h0).resolve_right hα
  rw [leg_L6b_factor F η 𝔣₀ α tf] at hG
  obtain ⟨𝔭, -, h𝔭0⟩ := Finset.prod_eq_zero_iff.1 hG
  have h𝔭S : 𝔭.1 ∈ S₀ := by
    rw [← hS]
    exact 𝔭.2
  exact leg_L7_local F η 𝔣₀ 𝔭 (cexp 𝔭.1) (d 𝔭.1) (hmult _ h𝔭S) (hc _ h𝔭S) (htriv _ h𝔭S) (hprim _ h𝔭S)
    α tf (hlev _ h𝔭S) h𝔭0

end GSolLegs

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Ψ)
    (hR : IsBoundedGenuineCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      (NumberField.StandardAddChar.stdAddChar F) Ψ R)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F)) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) :
    ∃ 𝔣₀ : Ideal (𝓞 F), 𝔣₀ ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus F η 𝔣₀ ∧
      ∃ g : AdelicGL2 (𝓞 F) F, AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣₀ R.toFun g ≠ 0 := by
  obtain ⟨𝔣', h𝔣', hmod'⟩ := leg_L0_nonzero_modulus F η 𝔣 hmod
  obtain ⟨cexp, htriv, hprim⟩ := leg_L1_conductor F η 𝔣' h𝔣' hmod'

  obtain ⟨S₀, hS₀⟩ : ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)),
      S = (AutomorphicForm.GaussTwist.modulusPrimes F 𝔣').filter (fun 𝔭 => 1 ≤ cexp 𝔭) := ⟨_, rfl⟩
  have hmemS : ∀ 𝔭, 𝔭 ∈ S₀ ↔ 𝔭 ∈ AutomorphicForm.GaussTwist.modulusPrimes F 𝔣' ∧ 1 ≤ cexp 𝔭 := by
    intro 𝔭
    rw [hS₀]
    exact Finset.mem_filter

  have hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      R.toFun (globalPoints (𝓞 F) F γ * g) = R.toFun g :=
    fun γ g => leg_left_invariant F _ _ R γ g
  have hright : ∀ g : AdelicGL2 (𝓞 F) F,
      ∀ k ∈ levelOne (𝓞 F) F Ψ.level ⊓ finiteAdelicGL2Subgroup F, R.toFun (g * k) = R.toFun g :=
    fun g k hk => R.level_invariant g k hk
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  obtain ⟨m, hm, hmB⟩ := leg_L2_point F Ψ.level Ψ.level_ne_bot S₀ R.toFun hleft hright g₀ hg₀

  have hψ := NumberField.StandardAddChar.isGlobalAddChar_stdAddChar F
  have hcont := leg_continuous_slice F R.toFun hR.isBoundedGenuineFn.continuous m
  have hsum := hR.summable_whittakerCoefficient m
  have hS := hasSum_whittakerCoefficient F _ _ _ _ hψ R.toFun m hcont hsum
  obtain ⟨α, hα⟩ := leg_exists_ne_zero_of_hasSum _ _ hS hm
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hα (leg_cusp F _ _ R _ m)

  obtain ⟨tf, htf, hconj⟩ := leg_L3b_conj F S₀ m hmB
  have hrat := leg_rat_unipotent F R.toFun hleft
  have hlat := leg_L4_lattice F _ _ _ Ψ.level S₀ R.toFun hrat hright m tf hconj α hα
  obtain ⟨d, hlev⟩ := leg_L5_level F S₀ (fun 𝔭 => algebraMap F (𝔭.adicCompletion F) α * tf 𝔭)
    (fun 𝔭 h𝔭 => leg_z_ne_zero F α hα0 tf 𝔭 (htf 𝔭 h𝔭)) hlat

  obtain ⟨𝔣₀, h𝔣₀def⟩ : ∃ I : Ideal (𝓞 F), I = ∏ 𝔭 ∈ S₀, 𝔭.asIdeal ^ (cexp 𝔭 + d 𝔭) := ⟨_, rfl⟩
  have harith := leg_L1b_arith F S₀ (fun 𝔭 => cexp 𝔭 + d 𝔭)
    (fun 𝔭 h𝔭 => (((hmemS 𝔭).1 h𝔭).2).trans (Nat.le_add_right _ _))
  obtain ⟨h𝔣₀, hS, hmult⟩ : 𝔣₀ ≠ ⊥ ∧ AutomorphicForm.GaussTwist.modulusPrimes F 𝔣₀ = S₀ ∧
      ∀ 𝔭 ∈ S₀, HeckeCharacter.idealMultiplicity F 𝔭 𝔣₀ = cexp 𝔭 + d 𝔭 := by
    rw [h𝔣₀def]
    exact harith
  refine ⟨𝔣₀, h𝔣₀, ?_, ?_⟩
  · refine leg_L1b_admits F η 𝔣' h𝔣' hmod' cexp htriv 𝔣₀ ?_
    intro 𝔭 h𝔭
    by_cases hc : 1 ≤ cexp 𝔭
    · have hm𝔭 := hmult 𝔭 ((hmemS 𝔭).2 ⟨h𝔭, hc⟩)
      omega
    · omega
  · exact leg_L7_tail F _ _ _ η R.toFun hR.whittakerCoefficientIntegrable hrat S₀ 𝔣₀ cexp d hS hmult
      (fun 𝔭 h𝔭 => ((hmemS 𝔭).1 h𝔭).2)
      (fun 𝔭 h𝔭 => htriv 𝔭 ((hmemS 𝔭).1 h𝔭).1)
      (fun 𝔭 h𝔭 => hprim 𝔭 ((hmemS 𝔭).1 h𝔭).1 ((hmemS 𝔭).1 h𝔭).2)
      m tf α hα hconj hlev

end S_LanglandsTunnell_exists_admitsModulus_gaussSumFn_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_exists_admitsModulus_gaussSumFn_ne_zero (solution)
