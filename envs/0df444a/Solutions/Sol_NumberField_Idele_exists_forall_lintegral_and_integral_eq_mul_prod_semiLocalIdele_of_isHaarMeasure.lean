-- Prove2me | solution 1 for NumberField.Idele.exists_forall_lintegral_and_integral_eq_mul_prod_semiLocalIdele_of_isHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d9d7fd2b-33c7-546c-bf8b-0638f539d072

import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Theorems.Thm_NumberField_Idele_exists_forall_lintegral_eq_mul_lintegral_mul_prod_lintegral_semiLocalIdele_of_isHaarMeasure
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_forall_lintegral_and_integral_eq_mul_prod_semiLocalIdele_of_isHaarMeasure
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero"
p2m_attr_erase "simp" "LanglandsTunnell.LDatum.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel

namespace ArchcBochnerEngine

open MeasureTheory Set

theorem integrable_and_integral_eq_of_forall_lintegral
    {Ω A ι : Type*} {B : ι → Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace A] [∀ i, MeasurableSpace (B i)]
    (μ : Measure Ω) (α : Measure A) [SigmaFinite α] (β : ∀ i, Measure (B i)) [∀ i, SigmaFinite (β i)]
    (qa : Ω → A) (hqa : Measurable qa) (qb : ∀ i, Ω → B i) (hqb : ∀ i, Measurable (qb i))
    (P : Set Ω) (hP : MeasurableSet P)
    (H : ∀ (g : A → ℝ≥0∞) (f : ∀ i, B i → ℝ≥0∞), Measurable g → (∀ i, Measurable (f i)) →
      ∫⁻ ω, g (qa ω) * (∏ i, f i (qb i ω)) * P.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ =
        (∫⁻ a, g a ∂α) * ∏ i, ∫⁻ b, f i b ∂(β i))
    (g : A → ℂ) (f : ∀ i, B i → ℂ) (hg : Integrable g α) (hf : ∀ i, Integrable (f i) (β i)) :
    Integrable (fun ω => g (qa ω) * (∏ i, f i (qb i ω)) * P.indicator (fun _ => (1 : ℂ)) ω) μ ∧
    ∫ ω, g (qa ω) * (∏ i, f i (qb i ω)) * P.indicator (fun _ => (1 : ℂ)) ω ∂μ =
      (∫ a, g a ∂α) * ∏ i, ∫ b, f i b ∂(β i) := by
  classical

  set π : Ω → A × (∀ i, B i) := fun ω => (qa ω, fun i => qb i ω) with hπdef
  have hπ : Measurable π := hqa.prodMk (measurable_pi_lambda _ fun i => hqb i)
  have key : α.prod (Measure.pi β) = Measure.map π (μ.restrict P) := by
    refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
      (D := univ.pi '' univ.pi fun i => {s : Set (B i) | MeasurableSet s})
      MeasurableSpace.generateFrom_measurableSet generateFrom_pi MeasurableSpace.isPiSystem_measurableSet
      isPiSystem_pi α.toFiniteSpanningSetsIn
      (Measure.FiniteSpanningSetsIn.pi fun i => (β i).toFiniteSpanningSetsIn) ?_
    intro s hs t ht
    obtain ⟨t, ht, rfl⟩ := ht
    have ht' : ∀ i, MeasurableSet (t i) := fun i => ht i (mem_univ i)
    have hst : MeasurableSet (s ×ˢ univ.pi t) := hs.prod (MeasurableSet.univ_pi ht')
    rw [Measure.map_apply hπ hst, Measure.restrict_apply (hπ hst), Measure.pi_pi,
      ← lintegral_indicator_one ((hπ hst).inter hP)]
    have hind : (fun ω => (π ⁻¹' (s ×ˢ univ.pi t) ∩ P).indicator (1 : Ω → ℝ≥0∞) ω) =
        fun ω => s.indicator (fun _ => (1 : ℝ≥0∞)) (qa ω) *
          (∏ i, (t i).indicator (fun _ => (1 : ℝ≥0∞)) (qb i ω)) * P.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
      funext ω
      by_cases hω : ω ∈ π ⁻¹' (s ×ˢ univ.pi t) ∩ P
      · rw [indicator_of_mem hω]
        obtain ⟨⟨h1, h2⟩, h3⟩ := hω
        rw [indicator_of_mem h1, indicator_of_mem h3, Finset.prod_eq_one fun i _ => indicator_of_mem (h2 i (mem_univ i)) _]
        simp
      · rw [indicator_of_notMem hω]
        simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ_pi, not_and_or, not_forall] at hω
        rcases hω with (h1 | ⟨i, hi⟩) | h3
        · rw [indicator_of_notMem h1]; simp
        · rw [Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)]; simp
        · rw [indicator_of_notMem h3]; simp
    rw [hind, H _ _ (measurable_const.indicator hs) (fun i => measurable_const.indicator (ht' i))]
    have h1 : ∫⁻ a, s.indicator (fun _ => (1 : ℝ≥0∞)) a ∂α = α s := by
      rw [lintegral_indicator hs, setLIntegral_const, one_mul]
    have h2 : ∀ i, ∫⁻ b, (t i).indicator (fun _ => (1 : ℝ≥0∞)) b ∂(β i) = β i (t i) := fun i => by
      rw [lintegral_indicator (ht' i), setLIntegral_const, one_mul]
    rw [h1]
    congr 1
    exact Finset.prod_congr rfl fun i _ => h2 i

  set F : A × (∀ i, B i) → ℂ := fun p => g p.1 * ∏ i, f i (p.2 i) with hFdef
  have hFint : Integrable F (α.prod (Measure.pi β)) := hg.mul_prod (Integrable.fintype_prod_dep hf)
  have hFval : ∫ p, F p ∂(α.prod (Measure.pi β)) = (∫ a, g a ∂α) * ∏ i, ∫ b, f i b ∂(β i) := by
    rw [hFdef, integral_prod_mul g (fun b : ∀ i, B i => ∏ i, f i (b i)), integral_fintype_prod_eq_prod]

  have hcomp : (fun ω => g (qa ω) * (∏ i, f i (qb i ω)) * P.indicator (fun _ => (1 : ℂ)) ω) =
      P.indicator (F ∘ π) := by
    funext ω
    by_cases hω : ω ∈ P
    · rw [indicator_of_mem hω, indicator_of_mem hω, mul_one]; rfl
    · rw [indicator_of_notMem hω, indicator_of_notMem hω, mul_zero]
  rw [key] at hFint hFval
  have hFint' : Integrable (F ∘ π) (μ.restrict P) :=
    (integrable_map_measure hFint.aestronglyMeasurable hπ.aemeasurable).mp hFint
  refine ⟨?_, ?_⟩
  · rw [hcomp, integrable_indicator_iff hP]
    exact hFint'
  · rw [hcomp, integral_indicator hP, ← hFval, integral_map hπ.aemeasurable hFint.aestronglyMeasurable]
    rfl

end ArchcBochnerEngine

namespace ArchcIB

open NumberField IsDedekindDomain AutomorphicForm

theorem secondCountableTopology_infiniteAdeleRing (L : Type) [Field L] [NumberField L] :
    SecondCountableTopology (InfiniteAdeleRing L) := by
  haveI : SecondCountableTopology (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology L
  exact (isEmbedding_prodMkLeft (0 : FiniteAdeleRing (𝓞 L) L)).secondCountableTopology

theorem secondCountableTopology_units {M : Type*} [Monoid M] [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : M ≃ₜ Mᵐᵒᵖ).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem sigmaFinite_arch (L : Type) [Field L] [NumberField L]
    (νa : @Measure (InfiniteAdeleRing L)ˣ (borel (InfiniteAdeleRing L)ˣ))
    (hνa : @Measure.IsHaarMeasure (InfiniteAdeleRing L)ˣ _ _ (borel (InfiniteAdeleRing L)ˣ) νa) :
    @SigmaFinite (InfiniteAdeleRing L)ˣ (borel (InfiniteAdeleRing L)ˣ) νa := by
  letI : MeasurableSpace (InfiniteAdeleRing L)ˣ := borel _
  haveI : BorelSpace (InfiniteAdeleRing L)ˣ := ⟨rfl⟩
  haveI := secondCountableTopology_infiniteAdeleRing L
  haveI : SecondCountableTopology (InfiniteAdeleRing L)ˣ := secondCountableTopology_units
  haveI : LocallyCompactSpace (InfiniteAdeleRing L)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI := hνa
  infer_instance

theorem sigmaFinite_semiLocal (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (μ : @Measure (L ⊗[K] v.adicCompletion K)ˣ (TransversalMeasure.semiLocalUnitsBorel K L v))
    (hμ : @Measure.IsHaarMeasure (L ⊗[K] v.adicCompletion K)ˣ _ _ (TransversalMeasure.semiLocalUnitsBorel K L v) μ) :
    @SigmaFinite (L ⊗[K] v.adicCompletion K)ˣ (TransversalMeasure.semiLocalUnitsBorel K L v) μ := by
  letI : MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ := TransversalMeasure.semiLocalUnitsBorel K L v
  haveI : BorelSpace (L ⊗[K] v.adicCompletion K)ˣ := ⟨rfl⟩
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  haveI := locallyCompactSpace_tensor K L (v.adicCompletion K)
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  haveI : SecondCountableTopology (L ⊗[K] v.adicCompletion K) := (semiLocalHomeomorph K L v).secondCountableTopology
  haveI : SecondCountableTopology (L ⊗[K] v.adicCompletion K)ˣ := secondCountableTopology_units
  haveI : LocallyCompactSpace (L ⊗[K] v.adicCompletion K)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI := hμ
  infer_instance

end ArchcIB

set_option synthInstance.maxHeartbeats 400000 in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (ν : Measure (AdeleRing (𝓞 L) L)ˣ)
    [ν.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    ∃ (νa : @Measure (InfiniteAdeleRing L)ˣ (borel (InfiniteAdeleRing L)ˣ))
      (νf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ),
      @Measure.IsHaarMeasure (InfiniteAdeleRing L)ˣ _ _ (borel (InfiniteAdeleRing L)ˣ) νa ∧
      (∀ v, (νf v).IsHaarMeasure ∧
        νf v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) = 1) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : (InfiniteAdeleRing L)ˣ → ℝ≥0∞)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞),
        @Measurable _ _ (borel (InfiniteAdeleRing L)ˣ) _ g →
        (∀ v ∈ S, Measurable (f v)) →
        ∫⁻ t, g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
            (∏ v ∈ S, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂ν =
          c * (∫⁻ x, g x ∂νa) * ∏ v ∈ S, ∫⁻ x, f v x ∂(νf v)) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : (InfiniteAdeleRing L)ˣ → ℂ)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℂ),
        Integrable g νa →
        (∀ v ∈ S, Integrable (f v) (νf v)) →
        Integrable (fun t : (AdeleRing (𝓞 L) L)ˣ =>
            g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
              (∏ v ∈ S, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
              Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
                  AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                    AutomorphicForm.TransversalMeasure.integralUnits K L v}
                (fun _ => (1 : ℂ)) t) ν ∧
        ∫ t, g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
            (∏ v ∈ S, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℂ)) t ∂ν =
          ((c.toReal : ℝ) : ℂ) * (∫ x, g x ∂νa) * ∏ v ∈ S, ∫ x, f v x ∂(νf v) := by
  classical
  obtain ⟨c, hc0, hcT, νa, νf, hνa, hνf, hlin⟩ :=
    NumberField.Idele.exists_forall_lintegral_eq_mul_lintegral_mul_prod_lintegral_semiLocalIdele_of_isHaarMeasure K L ν
  refine ⟨c, hc0, hcT, νa, νf, hνa, hνf, hlin, fun S g f hg hf => ?_⟩
  letI instA : MeasurableSpace (InfiniteAdeleRing L)ˣ := borel _
  haveI : BorelSpace (InfiniteAdeleRing L)ˣ := ⟨rfl⟩
  haveI : SigmaFinite νa := ArchcIB.sigmaFinite_arch L νa hνa
  haveI hσf : ∀ i : ↥S, SigmaFinite (νf i.1) := fun i => ArchcIB.sigmaFinite_semiLocal K L i.1 (νf i.1) (hνf i.1).1

  have hαc : ((c.toNNReal • νa : Measure (InfiniteAdeleRing L)ˣ)) = (c : ℝ≥0∞) • νa := by
    show ((c.toNNReal : ℝ≥0∞)) • νa = c • νa
    rw [ENNReal.coe_toNNReal hcT]
  have harch : Measurable fun t : (AdeleRing (𝓞 L) L)ˣ =>
      Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t :=
    (Continuous.units_map _ continuous_fst).measurable
  have hqb : ∀ i : ↥S, Measurable fun t : (AdeleRing (𝓞 L) L)ˣ =>
      AutomorphicForm.TransversalMeasure.semiLocalIdele K L i.1 t := by
    intro i
    letI : MeasurableSpace (L ⊗[K] (i.1).adicCompletion K)ˣ :=
      AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel K L i.1
    haveI : BorelSpace (L ⊗[K] (i.1).adicCompletion K)ˣ := ⟨rfl⟩
    refine Continuous.measurable ?_
    unfold AutomorphicForm.TransversalMeasure.semiLocalIdele
    refine (Continuous.units_map _ ?_).comp (Continuous.units_map _ continuous_snd)
    exact (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) i.1).symm.continuous.comp
      (continuous_pi fun w : (i.1).Extension (𝓞 L) => AdelicLevel.continuous_finAdeleEval (𝓞 L) L w.1)
  have hP : MeasurableSet {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
        AutomorphicForm.TransversalMeasure.integralUnits K L v} :=
    ((NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
      K L).2.2.2.1 S).measurableSet

  have H : ∀ (g' : (InfiniteAdeleRing L)ˣ → ℝ≥0∞)
      (f' : ∀ i : ↥S, (L ⊗[K] (i.1).adicCompletion K)ˣ → ℝ≥0∞),
      Measurable g' → (∀ i, Measurable (f' i)) →
      ∫⁻ t, g' (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
          (∏ i : ↥S, f' i (AutomorphicForm.TransversalMeasure.semiLocalIdele K L i.1 t)) *
          Set.indicator {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
              AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                AutomorphicForm.TransversalMeasure.integralUnits K L v} (fun _ => (1 : ℝ≥0∞)) t ∂ν =
        (∫⁻ a, g' a ∂(c.toNNReal • νa)) * ∏ i : ↥S, ∫⁻ b, f' i b ∂(νf i.1) := by
    intro g' f' hg' hf'
    let F : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞ :=
      fun v => if h : v ∈ S then f' ⟨v, h⟩ else fun _ => 1
    have hFi : ∀ i : ↥S, F i.1 = f' i := fun i => by
      simp only [F, dif_pos i.2]
    have hF : ∀ v ∈ S, Measurable (F v) := fun v hv => by
      rw [hFi ⟨v, hv⟩]; exact hf' ⟨v, hv⟩
    have h1 := hlin S g' F hg' hF
    simp only [← Finset.prod_coe_sort S] at h1
    simp only [← hFi]
    rw [hαc, lintegral_smul_measure, smul_eq_mul]
    convert h1 using 3
  have key := ArchcBochnerEngine.integrable_and_integral_eq_of_forall_lintegral ν (c.toNNReal • νa)
    (fun i : ↥S => νf i.1)
    (fun t : (AdeleRing (𝓞 L) L)ˣ => Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t)
    harch (fun (i : ↥S) (t : (AdeleRing (𝓞 L) L)ˣ) => AutomorphicForm.TransversalMeasure.semiLocalIdele K L i.1 t)
    hqb _ hP H g (fun i : ↥S => f i.1) (by rw [hαc]; exact hg.smul_measure hcT) (fun i => hf i.1 i.2)
  obtain ⟨hint, hval⟩ := key
  have hfun : (fun t : (AdeleRing (𝓞 L) L)ˣ =>
      g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
        (∏ v ∈ S, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
        Set.indicator {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
            AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
              AutomorphicForm.TransversalMeasure.integralUnits K L v} (fun _ => (1 : ℂ)) t) =
      fun t : (AdeleRing (𝓞 L) L)ˣ =>
        g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
        (∏ i : ↥S, f i.1 (AutomorphicForm.TransversalMeasure.semiLocalIdele K L i.1 t)) *
        Set.indicator {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
            AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
              AutomorphicForm.TransversalMeasure.integralUnits K L v} (fun _ => (1 : ℂ)) t := by
    funext t
    rw [← Finset.prod_coe_sort S]
  refine ⟨by rw [hfun]; exact hint, ?_⟩
  rw [hfun, hval, ← Finset.prod_coe_sort S, hαc, integral_smul_measure, Complex.real_smul]

end S_NumberField_Idele_exists_forall_lintegral_and_integral_eq_mul_prod_semiLocalIdele_of_isHaarMeasure
end P2MW
export P2MW.S_NumberField_Idele_exists_forall_lintegral_and_integral_eq_mul_prod_semiLocalIdele_of_isHaarMeasure (solution)
