-- Prove2me | solution 1 for NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4cfa27ac-2f2e-5aca-86fe-e3172d0732f7

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer
import Theorems.Thm_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm P2MW.S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.AutomorphicForm Topology"
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "adelicMaximalCompact mem_adelicMaximalCompact_iff maximalCompactHaar AdelicGL2 centralScalar unipotentGL2 mem_borelSubgroup_iff adelicBorel exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant exists_mem_adelicBorel_mul_eq"
p2m_open "AutomorphicForm"

namespace IwasawaCoord

variable (K : Type) [Field K] [NumberField K]

scoped instance : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

scoped instance secondCountableTopology_borel : SecondCountableTopology (adelicBorel (𝓞 K) K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

scoped instance secondCountableTopology_maxCpt : SecondCountableTopology (adelicMaximalCompact K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

theorem isClosed_adelicBorel : IsClosed (adelicBorel (𝓞 K) K : Set (AdelicGL2 (𝓞 K) K)) := by
  have : (adelicBorel (𝓞 K) K : Set (AdelicGL2 (𝓞 K) K)) =
      (fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0) ⁻¹' {0} := by
    ext g; exact mem_borelSubgroup_iff _
  rw [this]
  exact isClosed_singleton.preimage ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 1 0)

scoped instance locallyCompactSpace_borel : LocallyCompactSpace (adelicBorel (𝓞 K) K) := (isClosed_adelicBorel K).locallyCompactSpace

abbrev L := adelicBorel (𝓞 K) K × adelicMaximalCompact K

scoped instance action : MulAction (L K) (AdelicGL2 (𝓞 K) K) where
  smul l g := (l.1 : AdelicGL2 (𝓞 K) K) * g * ((l.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹
  one_smul g := by
    change ((1 : adelicBorel (𝓞 K) K) : AdelicGL2 (𝓞 K) K) * g * (((1 : adelicMaximalCompact K)) : AdelicGL2 (𝓞 K) K)⁻¹ = g
    simp
  mul_smul l l' g := by
    change ((l * l').1 : AdelicGL2 (𝓞 K) K) * g * (((l * l').2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹ =
      (l.1 : AdelicGL2 (𝓞 K) K) * ((l'.1 : AdelicGL2 (𝓞 K) K) * g * ((l'.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹) *
        ((l.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev]
    group

theorem smul_def (l : L K) (g : AdelicGL2 (𝓞 K) K) :
    l • g = (l.1 : AdelicGL2 (𝓞 K) K) * g * ((l.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹ := rfl

scoped instance continuousSMul : ContinuousSMul (L K) (AdelicGL2 (𝓞 K) K) := by
  refine ⟨?_⟩
  change Continuous fun p : L K × AdelicGL2 (𝓞 K) K =>
    (p.1.1 : AdelicGL2 (𝓞 K) K) * p.2 * ((p.1.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹
  exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_snd).mul
    (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv

theorem exists_smul_one_eq (g : AdelicGL2 (𝓞 K) K) : ∃ l : L K, l • (1 : AdelicGL2 (𝓞 K) K) = g := by
  obtain ⟨b, k, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K g
  refine ⟨(⟨b, hb⟩, ⟨k, mem_adelicMaximalCompact_iff.mpr ⟨hk1, hk2⟩⟩⁻¹), ?_⟩
  rw [smul_def]
  simp

scoped instance isPretransitive : MulAction.IsPretransitive (L K) (AdelicGL2 (𝓞 K) K) := by
  refine ⟨fun g₁ g₂ => ?_⟩
  obtain ⟨l₁, h₁⟩ := exists_smul_one_eq K g₁
  obtain ⟨l₂, h₂⟩ := exists_smul_one_eq K g₂
  exact ⟨l₂ * l₁⁻¹, by rw [← h₁, ← h₂, mul_smul, inv_smul_smul]⟩

abbrev BK := {k : adelicMaximalCompact K // (k : AdelicGL2 (𝓞 K) K) ∈ adelicBorel (𝓞 K) K}

scoped instance compactSpace_BK : CompactSpace (BK K) := by
  refine isCompact_iff_compactSpace.mp ?_
  exact ((isClosed_adelicBorel K).preimage continuous_subtype_val).isCompact

def toStab (k : BK K) : L K := (⟨(k.1 : AdelicGL2 (𝓞 K) K), k.2⟩, k.1)

theorem continuous_toStab : Continuous (toStab K) :=
  ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).prodMk continuous_subtype_val

theorem stabilizer_eq_range : (MulAction.stabilizer (L K) (1 : AdelicGL2 (𝓞 K) K) : Set (L K)) = Set.range (toStab K) := by
  ext l
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, smul_def, mul_one, mul_inv_eq_one]
  constructor
  · intro h
    refine ⟨⟨l.2, ?_⟩, ?_⟩
    · rw [← h]; exact l.1.2
    · refine Prod.ext (Subtype.ext ?_) rfl
      exact h.symm
  · rintro ⟨k, rfl⟩; rfl

theorem isCompact_stabilizer : IsCompact (MulAction.stabilizer (L K) (1 : AdelicGL2 (𝓞 K) K) : Set (L K)) := by
  rw [stabilizer_eq_range]; exact isCompact_range (continuous_toStab K)

theorem map_smul_adelicGLHaar (l : L K) :
    (adelicGLHaar (Fin 2) (𝓞 K) K).map (fun g : AdelicGL2 (𝓞 K) K => l • g) = adelicGLHaar (Fin 2) (𝓞 K) K := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  have : (fun g : AdelicGL2 (𝓞 K) K => l • g) =
      (fun g => (l.1 : AdelicGL2 (𝓞 K) K) * g) ∘ (fun g => g * ((l.2 : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)⁻¹) := by
    funext g; rw [Function.comp_apply, smul_def, mul_assoc]
  rw [this, ← Measure.map_map (measurable_const_mul _) (measurable_mul_const _), map_mul_right_eq_self,
    map_mul_left_eq_self]

theorem isInvInvariant_of_compactSpace {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [μ.IsHaarMeasure] : μ.IsInvInvariant := by

  haveI : μ.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have h := Measure.map_right_mul_eq_modularCharacterFun_smul μ g
    have huniv : (μ.map (· * g)) Set.univ = μ Set.univ := by
      rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
    have hc : Measure.modularCharacterFun g = 1 := by
      have h2 := congrArg (fun ν : Measure H => ν Set.univ) h
      simp only [huniv] at h2
      have hne : μ Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
      have htop : μ Set.univ ≠ ∞ := measure_ne_top μ _
      have : (Measure.modularCharacterFun g : ℝ≥0∞) = 1 := by
        rw [← ENNReal.mul_left_inj hne htop, one_mul]; exact h2.symm
      exact_mod_cast this
    rw [h, hc, one_smul]

  have h := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have huniv : μ.inv Set.univ = μ Set.univ := by
    rw [Measure.inv_def, Measure.map_apply measurable_inv MeasurableSet.univ, Set.preimage_univ]
  have hc : Measure.haarScalarFactor μ.inv μ = 1 := by
    have h2 := congrArg (fun ν : Measure H => ν Set.univ) h
    simp only [huniv] at h2
    have hne : μ Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    have htop : μ Set.univ ≠ ∞ := measure_ne_top μ _
    have : (Measure.haarScalarFactor μ.inv μ : ℝ≥0∞) = 1 := by
      rw [← ENNReal.mul_left_inj hne htop, one_mul]; exact h2.symm
    exact_mod_cast this
  refine ⟨?_⟩
  rw [h, hc, one_smul]

scoped instance isInvInvariant_maximalCompactHaar : (maximalCompactHaar K).IsInvInvariant :=
  isInvInvariant_of_compactSpace (maximalCompactHaar K)

def borelHaar : Measure (adelicBorel (𝓞 K) K) := Measure.haar

scoped instance : (borelHaar K).IsHaarMeasure := by unfold borelHaar; infer_instance

scoped instance sigmaFinite_borelHaar : SigmaFinite (borelHaar K) := by
  haveI : SigmaCompactSpace (adelicBorel (𝓞 K) K) := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

scoped instance sigmaFinite_maximalCompactHaar : SigmaFinite (maximalCompactHaar K) := inferInstance

def LHaar : Measure (L K) := (borelHaar K).prod (maximalCompactHaar K)

scoped instance : (LHaar K).IsHaarMeasure := by unfold LHaar; infer_instance

theorem exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa' :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ φ : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(adelicAddHaar (𝓞 K) K) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  obtain ⟨c₁, hc₁top, hc₁⟩ :=
    MeasureTheory.Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer (LHaar K)
      (X := AdelicGL2 (𝓞 K) K) (1 : AdelicGL2 (𝓞 K) K) (isCompact_stabilizer K) μ (map_smul_adelicGLHaar K)
  have hc₁0 : c₁ ≠ 0 := by
    intro h0
    have : μ Set.univ = 0 := by rw [hc₁, h0, zero_smul]; rfl
    exact isOpen_univ.measure_ne_zero μ Set.univ_nonempty this

  obtain ⟨c₂, hc₂0, hc₂top, hc₂⟩ :=
    AutomorphicForm.exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant K (borelHaar K)
  refine ⟨c₁ * c₂, mul_ne_zero hc₁0 hc₂0, ENNReal.mul_ne_top hc₁top hc₂top, fun φ hφ => ?_⟩

  have hsm : Measurable fun l : L K => l • (1 : AdelicGL2 (𝓞 K) K) :=
    (continuous_id.smul continuous_const).measurable
  have hF : Measurable fun g : AdelicGL2 (𝓞 K) K => ∫⁻ k, φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    refine Measurable.lintegral_prod_right ?_
    exact hφ.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).measurable
  calc ∫⁻ g, φ g ∂μ = c₁ * ∫⁻ l, φ (l • (1 : AdelicGL2 (𝓞 K) K)) ∂(LHaar K) := by
        rw [hc₁, lintegral_smul_measure, lintegral_map hφ hsm, smul_eq_mul]
    _ = c₁ * ∫⁻ b, ∫⁻ k, φ ((b : AdelicGL2 (𝓞 K) K) * ((k : AdelicGL2 (𝓞 K) K))⁻¹) ∂(maximalCompactHaar K) ∂(borelHaar K) := by
        congr 1
        rw [LHaar, lintegral_prod _ (show Measurable (fun l : L K => φ (l • (1 : AdelicGL2 (𝓞 K) K))) from hφ.comp hsm).aemeasurable]
        refine lintegral_congr fun b => lintegral_congr fun k => ?_
        rw [smul_def, mul_one]
    _ = c₁ * ∫⁻ b, ∫⁻ k, φ ((b : AdelicGL2 (𝓞 K) K) * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) ∂(borelHaar K) := by
        congr 1
        refine lintegral_congr fun b => ?_
        have hψ : Measurable fun k : adelicMaximalCompact K => φ ((b : AdelicGL2 (𝓞 K) K) * (k : AdelicGL2 (𝓞 K) K)) :=
          hφ.comp (continuous_const.mul continuous_subtype_val).measurable
        calc ∫⁻ k, φ ((b : AdelicGL2 (𝓞 K) K) * ((k : AdelicGL2 (𝓞 K) K))⁻¹) ∂(maximalCompactHaar K)
            = ∫⁻ k, φ ((b : AdelicGL2 (𝓞 K) K) * (k : AdelicGL2 (𝓞 K) K)) ∂((maximalCompactHaar K).inv) := by
              rw [Measure.inv_def, lintegral_map hψ measurable_inv]
              rfl
          _ = _ := by rw [Measure.IsInvInvariant.inv_eq_self]
    _ = c₁ * (c₂ * ∫⁻ x, ∫⁻ u, ∫⁻ t, (∫⁻ k, φ (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t *
          (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
          ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(adelicAddHaar (𝓞 K) K)) := by
        rw [hc₂ _ hF]
    _ = _ := by
        rw [mul_assoc]
        congr 2
        refine lintegral_congr fun x => lintegral_congr fun u => lintegral_congr fun t => ?_
        rw [lintegral_mul_const _ ?_]
        exact hφ.comp (continuous_const.mul continuous_subtype_val).measurable

end IwasawaCoord
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.AutomorphicForm.IwasawaCoord"

end AutomorphicForm
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.AutomorphicForm.IwasawaCoord P2MW.S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.AutomorphicForm"

end
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.AutomorphicForm.IwasawaCoord P2MW.S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa.AutomorphicForm"

theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ φ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (AutomorphicForm.unipotentGL2 x * AutomorphicForm.centralScalar (𝓞 K) K u * NumberField.AdelicLevel.diagOne t *
                  (k : AutomorphicForm.AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(AutomorphicForm.maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K) :=
  AutomorphicForm.IwasawaCoord.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa' K

end S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
end P2MW
export P2MW.S_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa (solution)
