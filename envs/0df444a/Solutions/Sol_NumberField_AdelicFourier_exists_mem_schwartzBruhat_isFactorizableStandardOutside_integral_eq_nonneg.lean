-- Prove2me | solution 1 for NumberField.AdelicFourier.exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2b11fb48-1891-56c1-ac93-ba900c5b6257

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicFourier
import Theorems.Thm_NumberField_AdelicFourier_inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq
import Theorems.Thm_NumberField_AdelicFourier_exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod
import Theorems.Thm_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one
import Theorems.Thm_NumberField_AdelicFourier_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one_eq_of_level_zero
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat
import Theorems.Thm_AutomorphicForm_exists_localComponents_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_integral_fourierChar_trace_mul_prod_eq_prod_integral_fourierChar_trace_single_mul
import Theorems.Thm_NumberField_AdelicFourier_map_ringEquiv_mixedSpace_pi_eq_volume
import Theorems.Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg
p2m_attr_erase "instance" "instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

noncomputable section

namespace Ws1
namespace C6F

open scoped Classical
open NumberField.AdelicFourier AutomorphicForm Topology

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

variable (F : Type) [Field F] [NumberField F]

open NumberField.InfinitePlace

noncomputable scoped instance instMeasurableSpaceCompletion (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
scoped instance instBorelSpaceCompletion (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩

namespace ArchBridge

noncomputable def isoR {w : InfinitePlace F} (hw : w.IsReal) : w.Completion ≃ᵐ ℝ :=
  (Completion.isometryEquivRealOfIsReal hw).toHomeomorph.toMeasurableEquiv

noncomputable def isoC {w : InfinitePlace F} (hw : w.IsComplex) : w.Completion ≃ᵐ ℂ :=
  (Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.toMeasurableEquiv

noncomputable def μ23 (w : InfinitePlace F) : Measure w.Completion :=
  if hw : w.IsReal then Measure.map (Completion.ringEquivRealOfIsReal hw).symm volume
  else Measure.map (Completion.ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm volume

theorem measurePreserving_isoR {w : InfinitePlace F} (hw : w.IsReal) : MeasurePreserving (isoR F hw) (μ23 F w) volume := by
  refine ⟨(isoR F hw).measurable, ?_⟩
  rw [μ23, dif_pos hw]
  exact (isoR F hw).map_map_symm

theorem measurePreserving_isoC {w : InfinitePlace F} (hw : ¬ w.IsReal) :
    MeasurePreserving (isoC F (not_isReal_iff_isComplex.mp hw)) (μ23 F w) volume := by
  refine ⟨(isoC F _).measurable, ?_⟩
  rw [μ23, dif_neg hw]
  exact (isoC F _).map_map_symm

scoped instance sigmaFinite_μ23 (w : InfinitePlace F) : SigmaFinite (μ23 F w) := by
  by_cases hw : w.IsReal
  · rw [μ23, dif_pos hw]; exact (isoR F hw).symm.sigmaFinite_map
  · rw [μ23, dif_neg hw]; exact (isoC F (not_isReal_iff_isComplex.mp hw)).symm.sigmaFinite_map

noncomputable scoped instance instMeasurableSpaceInfiniteAdeleRing : MeasurableSpace (InfiniteAdeleRing F) := MeasurableSpace.pi

theorem measurable_ringEquiv_mixedSpace : Measurable (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  set eqv : {w : InfinitePlace F // ¬ w.IsReal} ≃ {w : InfinitePlace F // w.IsComplex} :=
    Equiv.subtypeEquivRight (p := fun w : InfinitePlace F => ¬ w.IsReal) (q := fun w : InfinitePlace F => w.IsComplex)
      (fun w => not_isReal_iff_isComplex) with heqv
  have h1 := measurePreserving_piEquivPiSubtypeProd (μ23 F) (fun w : InfinitePlace F => w.IsReal)
  have h2a : MeasurePreserving (fun (a : (r : {w : InfinitePlace F // w.IsReal}) → (r.1).Completion) (r : {w : InfinitePlace F // w.IsReal}) => isoR F r.2 (a r))
      (Measure.pi fun r : {w : InfinitePlace F // w.IsReal} => μ23 F r.1) (Measure.pi fun _ => (volume : Measure ℝ)) :=
    measurePreserving_pi _ _ (fun r => measurePreserving_isoR F r.2)
  have h2b : MeasurePreserving (fun (a : (r : {w : InfinitePlace F // ¬ w.IsReal}) → (r.1).Completion) (r : {w : InfinitePlace F // ¬ w.IsReal}) => isoC F (not_isReal_iff_isComplex.mp r.2) (a r))
      (Measure.pi fun r : {w : InfinitePlace F // ¬ w.IsReal} => μ23 F r.1) (Measure.pi fun _ => (volume : Measure ℂ)) :=
    measurePreserving_pi _ _ (fun r => measurePreserving_isoC F r.2)
  have h3b := measurePreserving_piCongrLeft (fun _ : {w : InfinitePlace F // w.IsComplex} => (volume : Measure ℂ)) eqv
  have h3 := (MeasurePreserving.id (Measure.pi fun _ : {w : InfinitePlace F // w.IsReal} => (volume : Measure ℝ))).prod h3b
  have h := ((h3.comp (h2a.prod h2b)).comp h1).measurable
  convert h using 1
  all_goals try rfl

theorem measurePreserving_ringEquiv_mixedSpace :
    MeasurePreserving (InfiniteAdeleRing.ringEquiv_mixedSpace F) (Measure.pi (μ23 F)) volume :=
  ⟨measurable_ringEquiv_mixedSpace F, NumberField.AdelicFourier.map_ringEquiv_mixedSpace_pi_eq_volume F⟩

noncomputable def σ (v : mixedEmbedding.mixedSpace F) : InfiniteAdeleRing F :=
  fun w => if hw : w.IsReal then (isoR F hw).symm (v.1 ⟨w, hw⟩)
    else (isoC F (not_isReal_iff_isComplex.mp hw)).symm (v.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩)

theorem ringEquiv_σ (v : mixedEmbedding.mixedSpace F) : InfiniteAdeleRing.ringEquiv_mixedSpace F (σ F v) = v := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine Prod.ext ?_ ?_
  · funext r
    show isoR F r.2 (σ F v r.1) = v.1 r
    simp only [σ, dif_pos r.2, MeasurableEquiv.apply_symm_apply]
  · funext c
    have hc : ¬ (c.1).IsReal := not_isReal_iff_isComplex.mpr c.2
    show isoC F c.2 (σ F v c.1) = v.2 c
    simp only [σ, dif_neg hc, MeasurableEquiv.apply_symm_apply]

theorem measurable_σ : Measurable (σ F) := by
  refine measurable_pi_iff.mpr fun w => ?_
  by_cases hw : w.IsReal
  · have : (fun v : mixedEmbedding.mixedSpace F => σ F v w) = fun v => (isoR F hw).symm (v.1 ⟨w, hw⟩) := by
      funext v; simp only [σ, dif_pos hw]
    rw [this]
    exact (isoR F hw).symm.measurable.comp ((measurable_pi_apply _).comp measurable_fst)
  · have : (fun v : mixedEmbedding.mixedSpace F => σ F v w)
        = fun v => (isoC F (not_isReal_iff_isComplex.mp hw)).symm (v.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩) := by
      funext v; simp only [σ, dif_neg hw]
    rw [this]
    exact (isoC F _).symm.measurable.comp ((measurable_pi_apply _).comp measurable_snd)

noncomputable def ρM : InfiniteAdeleRing F ≃ᵐ mixedEmbedding.mixedSpace F where
  toFun := InfiniteAdeleRing.ringEquiv_mixedSpace F
  invFun := σ F
  left_inv x := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ringEquiv_σ F _)
  right_inv := ringEquiv_σ F
  measurable_toFun := measurable_ringEquiv_mixedSpace F
  measurable_invFun := measurable_σ F

theorem integral_comp_ringEquiv_mixedSpace (f : mixedEmbedding.mixedSpace F → ℂ) :
    ∫ x, f (InfiniteAdeleRing.ringEquiv_mixedSpace F x) ∂(Measure.pi (μ23 F)) = ∫ u, f u ∂volume :=
  (measurePreserving_ringEquiv_mixedSpace F).integral_comp' (f := ρM F) f

end ArchBridge
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg.Ws1.C6F.ArchBridge"

open ArchBridge in

theorem arch_factor
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ) (gw : (w : InfinitePlace F) → w.Completion → ℂ)
    (hg : ∀ x : InfiniteAdeleRing F, g (InfiniteAdeleRing.ringEquiv_mixedSpace F x) = ∏ w, gw w (x w))
    (hgc : ∀ w, Continuous (gw w)) (hgs : ∀ w, HasCompactSupport (gw w)) :
    ∃ Bi : (w : InfinitePlace F) → w.Completion → ℂ, ∀ y : InfiniteAdeleRing F,
      fourierIntegral
          (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
          MeasureTheory.volume (g : mixedEmbedding.mixedSpace F → ℂ) (InfiniteAdeleRing.ringEquiv_mixedSpace F y)
        = ∏ w, Bi w (y w) := by
  obtain ⟨a, ha, hψa⟩ := NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ
  set ρ := InfiniteAdeleRing.ringEquiv_mixedSpace F with hρ
  set χ : InfiniteAdeleRing F → ℂ := fun z =>
    (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (ρ z)) : ℂ) with hχ
  set a' : InfiniteAdeleRing F := algebraMap F (InfiniteAdeleRing F) a⁻¹ with ha'
  have hψx : ∀ x : InfiniteAdeleRing F, ψ (x, 0) = χ (a' * x) := by
    intro x
    have := hψa (a' * x)
    rw [← mul_assoc, ha', ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul] at this
    exact this
  refine ⟨fun w t => ∫ z, χ (Pi.single w (-(z * (a' w * t)))) * gw w z ∂(μ23 F w), fun y => ?_⟩
  rw [fourierIntegral_def, ← integral_comp_ringEquiv_mixedSpace]
  have hintegrand : ∀ x : InfiniteAdeleRing F,
      (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp ρ.symm.toAddMonoidHom)) (-(ρ x * ρ y)) * g (ρ x)
        = χ (-(x * (a' * y))) * ∏ w, gw w (x w) := by
    intro x
    have e1 : (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp ρ.symm.toAddMonoidHom)) (-(ρ x * ρ y))
        = ψ (ρ.symm (-(ρ x * ρ y)), 0) := rfl
    rw [hg, e1, map_neg, map_mul, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, hψx]
    congr 2
    ring
  refine (integral_congr_ae (Filter.Eventually.of_forall hintegrand)).trans ?_
  exact NumberField.AdelicFourier.integral_fourierChar_trace_mul_prod_eq_prod_integral_fourierChar_trace_single_mul F (μ23 F) gw (a' * y)

section Param

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

def rawOf (z : (v : ↥S) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :
    (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F :=
  fun v => if h : v ∈ S then z ⟨v, h⟩ else (1 : v.adicCompletion F)

theorem rawOf_of_mem (z : (v : ↥S) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : rawOf F S z v = z ⟨v, hv⟩ := by
  unfold rawOf; rw [dif_pos hv]

theorem rawOf_of_not_mem (z : (v : ↥S) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : rawOf F S z v = 1 := by
  unfold rawOf; rw [dif_neg hv]

theorem rawOf_eventually (z : (v : ↥S) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :
    ∀ᶠ v in Filter.cofinite, rawOf F S z v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hS : ∀ᶠ v in Filter.cofinite, v ∉ (S : Set (HeightOneSpectrum (𝓞 F))) := S.finite_toSet.compl_mem_cofinite
  refine hS.mono fun v hv => ?_
  rw [rawOf_of_not_mem F S z hv]
  exact one_mem _

def finOf (z : (v : ↥S) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨rawOf F S z, rawOf_eventually F S z⟩

theorem finOf_apply (z : (v : ↥S) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) (v : HeightOneSpectrum (𝓞 F)) :
    (finOf F S z : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) v = rawOf F S z v := rfl

theorem continuous_finOf : Continuous (finOf F S) := by
  set T : Set (HeightOneSpectrum (𝓞 F)) := (↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ with hTdef
  have hT : Filter.cofinite ≤ Filter.principal T :=
    Filter.le_principal_iff.mpr (by rw [hTdef, Filter.mem_cofinite, compl_compl]; exact S.finite_toSet)
  let Y := RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (Filter.principal T)
  let g : ((v : ↥S) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) → Y := fun z =>
    ⟨rawOf F S z, by
      rw [Filter.eventually_principal]
      intro v hv
      have hvS : v ∉ S := hv
      show rawOf F S z v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      rw [rawOf_of_not_mem F S z hvS]; exact one_mem _⟩
  have hraw : Continuous (rawOf F S) := by
    refine continuous_pi fun v => ?_
    by_cases hv : v ∈ S
    · have : (fun z : (v : ↥S) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F => rawOf F S z v)
          = fun z => z ⟨v, hv⟩ := by
        funext z; exact rawOf_of_mem F S z hv
      rw [this]; exact continuous_apply _
    · have : (fun z : (v : ↥S) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F => rawOf F S z v)
          = fun _ => 1 := by
        funext z; exact rawOf_of_not_mem F S z hv
      rw [this]; exact continuous_const
  have hg : Continuous g := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact hraw
  have hfac : finOf F S = RestrictedProduct.inclusion _ _ hT ∘ g := by
    funext z; rfl
  rw [hfac]
  exact (RestrictedProduct.continuous_inclusion hT).comp hg

abbrev Param : Type :=
  ((w : InfinitePlace F) → w.Completion) × ((v : ↥S) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)

def adOf (p : Param F S) : AdeleRing (𝓞 F) F := (p.1, finOf F S p.2)

theorem continuous_adOf : Continuous (adOf F S) :=
  continuous_fst.prodMk ((continuous_finOf F S).comp continuous_snd)

def invP (p : Param F S) : Param F S := (fun w => (p.1 w)⁻¹, fun v => (p.2 v)⁻¹)

def nz : Set (Param F S) := {p | (∀ w, p.1 w ≠ 0) ∧ ∀ v, p.2 v ≠ 0}

theorem isOpen_nz : IsOpen (nz F S) := by
  have h1 : IsOpen {p : Param F S | ∀ w, p.1 w ≠ 0} := by
    have : {p : Param F S | ∀ w, p.1 w ≠ 0} = ⋂ w, (fun p : Param F S => p.1 w) ⁻¹' {0}ᶜ := by
      ext p; simp
    rw [this]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_compl_singleton.preimage ((continuous_apply w).comp continuous_fst)
  have h2 : IsOpen {p : Param F S | ∀ v, p.2 v ≠ 0} := by
    have : {p : Param F S | ∀ v, p.2 v ≠ 0} = ⋂ v, (fun p : Param F S => p.2 v) ⁻¹' {0}ᶜ := by
      ext p; simp
    rw [this]
    exact isOpen_iInter_of_finite fun v =>
      isOpen_compl_singleton.preimage ((continuous_apply v).comp continuous_snd)
  have : nz F S = {p : Param F S | ∀ w, p.1 w ≠ 0} ∩ {p : Param F S | ∀ v, p.2 v ≠ 0} := by
    ext p; simp [nz]
  rw [this]; exact h1.inter h2

theorem continuousOn_invP : ContinuousOn (invP F S) (nz F S) := by
  refine ContinuousOn.prodMk ?_ ?_
  · refine continuousOn_pi.mpr fun w => ?_
    exact (continuousOn_inv₀.comp ((continuous_apply w).comp continuous_fst).continuousOn
      fun p hp => hp.1 w)
  · refine continuousOn_pi.mpr fun v => ?_
    exact (continuousOn_inv₀.comp ((continuous_apply v).comp continuous_snd).continuousOn
      fun p hp => hp.2 v)

def Φ (p : Param F S) : AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
  (adOf F S p, MulOpposite.op (adOf F S (invP F S p)))

theorem continuousOn_Φ : ContinuousOn (Φ F S) (nz F S) :=
  (continuous_adOf F S).continuousOn.prodMk
    (MulOpposite.continuous_op.comp_continuousOn ((continuous_adOf F S).comp_continuousOn (continuousOn_invP F S)))

def π (a : (AdeleRing (𝓞 F) F)ˣ) : Param F S :=
  (fun w => ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w,
    fun v => ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)

theorem fst_apply_ne_zero (a : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  intro h0
  have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.1 w) a.mul_inv
  change ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 at h
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem snd_apply_ne_zero (a : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ≠ 0 := by
  intro h0
  have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.2 v) a.mul_inv
  change ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 at h
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem fst_apply_inv (a : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = (((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w)⁻¹ :=
  eq_inv_of_mul_eq_one_right (congrArg (fun x : AdeleRing (𝓞 F) F => x.1 w) a.mul_inv)

theorem snd_apply_inv (a : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = (((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)⁻¹ :=
  eq_inv_of_mul_eq_one_right (congrArg (fun x : AdeleRing (𝓞 F) F => x.2 v) a.mul_inv)

theorem π_mem_nz (a : (AdeleRing (𝓞 F) F)ˣ) : π F S a ∈ nz F S :=
  ⟨fun w => fst_apply_ne_zero F a w, fun v => snd_apply_ne_zero F a v.1⟩

theorem adOf_π {a : (AdeleRing (𝓞 F) F)ˣ} (ha : NumberField.Idele.partAt F S a = a) :
    adOf F S (π F S a) = ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := by
  refine Prod.ext rfl (Subtype.ext (funext fun v => ?_))
  show rawOf F S (fun v : ↥S => ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) v
    = ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
  by_cases hv : v ∈ S
  · rw [rawOf_of_mem F S _ hv]
  · rw [rawOf_of_not_mem F S _ hv]
    have h := NumberField.Idele.partAt_snd_of_not_mem F S a hv
    rw [ha] at h
    exact h.symm

theorem adOf_invP_π {a : (AdeleRing (𝓞 F) F)ˣ} (ha : NumberField.Idele.partAt F S a = a) :
    adOf F S (invP F S (π F S a)) = ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := by
  have ha' : NumberField.Idele.partAt F S a⁻¹ = a⁻¹ := by rw [map_inv, ha]
  rw [← adOf_π F S ha']
  unfold adOf invP π
  congr 1
  · funext w; exact (fst_apply_inv F a w).symm
  · congr 1; funext v; exact (snd_apply_inv F a v).symm

theorem Φ_π {a : (AdeleRing (𝓞 F) F)ˣ} (ha : NumberField.Idele.partAt F S a = a) :
    Φ F S (π F S a) = Units.embedProduct (AdeleRing (𝓞 F) F) a := by
  unfold Φ
  rw [adOf_π F S ha, adOf_invP_π F S ha]
  rfl

end Param
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg.Ws1.C6F.ArchBridge"

omit [NumberField F] in

theorem isCompact_closedBall_completion (w : InfinitePlace F) (x : w.Completion) (r : ℝ) :
    IsCompact (Metric.closedBall x r) := by
  have he : Metric.closedBall x r
      = InfinitePlace.Completion.extensionEmbedding w ⁻¹'
          Metric.closedBall (InfinitePlace.Completion.extensionEmbedding w x) r := by
    ext z
    simp only [Metric.mem_closedBall, Set.mem_preimage]
    rw [(InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq]
  rw [he]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
    (isCompact_closedBall _ r)

theorem isCompact_finiteBox (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (C : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)) (hC : ∀ v ∈ S, IsCompact (C v)) :
    IsCompact {x : FiniteAdeleRing (𝓞 F) F |
      (∀ v ∈ S, x v ∈ C v) ∧ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
  classical
  set T : Set (HeightOneSpectrum (𝓞 F)) := (↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ with hTdef
  have hT : Filter.cofinite ≤ Filter.principal T :=
    Filter.le_principal_iff.mpr (by rw [hTdef, Filter.mem_cofinite, compl_compl]; exact S.finite_toSet)
  set D : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F) := fun v =>
    if v ∈ S then C v else (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hDdef
  have hD : ∀ v, IsCompact (D v) := fun v => by
    by_cases hv : v ∈ S
    · rw [hDdef]; simp only [if_pos hv]; exact hC v hv
    · rw [hDdef]; simp only [if_neg hv]
      haveI : CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
        inferInstanceAs (CompactSpace (v.adicCompletionIntegers F))
      exact isCompact_iff_compactSpace.mpr inferInstance
  have hPD : IsCompact (Set.univ.pi D) := isCompact_univ_pi hD
  let Y := RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (Filter.principal T)
  set s : Set Y := ((↑) : Y → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) ⁻¹' Set.univ.pi D with hsdef
  have hs : IsCompact s := by
    rw [(RestrictedProduct.isEmbedding_coe_of_principal).isCompact_iff]
    have himg : ((↑) : Y → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) '' s = Set.univ.pi D := by
      refine Set.Subset.antisymm (Set.image_preimage_subset _ _) fun f hf => ?_
      have hfT : ∀ᶠ v in Filter.principal T, f v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        rw [Filter.eventually_principal]
        intro v hv
        have hvS : v ∉ S := hv
        have := hf v (Set.mem_univ v)
        rw [hDdef] at this; simp only [if_neg hvS] at this
        exact this
      exact ⟨⟨f, hfT⟩, hf, rfl⟩
    rw [himg]; exact hPD
  have himage : RestrictedProduct.inclusion (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hT '' s
      = {x : FiniteAdeleRing (𝓞 F) F |
          (∀ v ∈ S, x v ∈ C v) ∧ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have := hy v (Set.mem_univ v)
        rw [hDdef] at this; simp only [if_pos hv] at this
        exact this
      · have := hy v (Set.mem_univ v)
        rw [hDdef] at this; simp only [if_neg hv] at this
        exact this
    · rintro ⟨h1, h2⟩
      have hxT : ∀ᶠ v in Filter.principal T, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        rw [Filter.eventually_principal]; exact fun v hv => h2 v hv
      refine ⟨⟨fun v => x v, hxT⟩, fun v _ => ?_, ?_⟩
      · by_cases hv : v ∈ S
        · show x v ∈ D v
          rw [hDdef]; simp only [if_pos hv]; exact h1 v hv
        · show x v ∈ D v
          rw [hDdef]; simp only [if_neg hv]; exact h2 v hv
      · rfl
  rw [← himage]
  exact hs.image (RestrictedProduct.continuous_inclusion hT)

theorem isCompact_inv_image {K : Type*} [Field K] [TopologicalSpace K] [ContinuousInv₀ K]
    {C : Set K} (hC : IsCompact C) (h0 : (0 : K) ∉ C) : IsCompact ((fun x : K => x⁻¹) '' C) :=
  hC.image_of_continuousOn (continuousOn_inv₀.mono fun _ hx h => h0 (h ▸ hx))

theorem exists_box_subset (S : Finset (HeightOneSpectrum (𝓞 F))) (N : Set (AdeleRing (𝓞 F) F)ˣ) (hN : IsOpen N)
    (a₀ : (AdeleRing (𝓞 F) F)ˣ) (ha₀N : a₀ ∈ N)
    (ha₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1) :
    ∃ (U : ∀ w : InfinitePlace F, Set w.Completion) (V : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)),
      (∀ w, IsOpen (U w)) ∧ (∀ w, ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ∈ U w) ∧
      (∀ w, (0 : w.Completion) ∉ closure (U w)) ∧ (∀ w, IsCompact (closure (U w))) ∧
      (∀ v ∈ S, IsOpen (V v)) ∧ (∀ v ∈ S, IsClosed (V v)) ∧ (∀ v ∈ S, IsCompact (V v)) ∧
      (∀ v ∈ S, ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ V v) ∧ (∀ v ∈ S, (0 : v.adicCompletion F) ∉ V v) ∧
      ∀ a : (AdeleRing (𝓞 F) F)ˣ, NumberField.Idele.partAt F S a = a →
        (∀ w, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ∈ U w) →
        (∀ v ∈ S, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ V v) → a ∈ N := by

  have ha₀fix : NumberField.Idele.partAt F S a₀ = a₀ := by
    refine Units.ext (Prod.ext (NumberField.Idele.partAt_fst F S a₀) (Subtype.ext (funext fun v => ?_)))
    by_cases hv : v ∈ S
    · exact NumberField.Idele.partAt_snd_of_mem F S a₀ hv
    · exact (NumberField.Idele.partAt_snd_of_not_mem F S a₀ hv).trans (ha₀ v hv).symm

  obtain ⟨O, hO, hNO⟩ := (Units.isInducing_embedProduct (M := AdeleRing (𝓞 F) F)).isOpen_iff.mp hN
  set W : Set (Param F S) := nz F S ∩ Φ F S ⁻¹' O with hWdef
  have hW : IsOpen W := (continuousOn_Φ F S).isOpen_inter_preimage (isOpen_nz F S) hO
  have hmemW : ∀ a : (AdeleRing (𝓞 F) F)ˣ, NumberField.Idele.partAt F S a = a → (π F S a ∈ W ↔ a ∈ N) := by
    intro a ha
    rw [hWdef, Set.mem_inter_iff, Set.mem_preimage, Φ_π F S ha, ← hNO, Set.mem_preimage]
    exact ⟨fun h => h.2, fun h => ⟨π_mem_nz F S a, h⟩⟩
  have hp₀ : π F S a₀ ∈ W := (hmemW a₀ ha₀fix).mpr ha₀N

  obtain ⟨u₁, u₂, hu₁, hu₂, hpu₁, hpu₂, hprod⟩ := isOpen_prod_iff.mp hW _ _ hp₀
  obtain ⟨I₁, t₁, ht₁, hI₁⟩ := isOpen_pi_iff.mp hu₁ _ hpu₁
  obtain ⟨I₂, t₂, ht₂, hI₂⟩ := isOpen_pi_iff.mp hu₂ _ hpu₂

  set r : InfinitePlace F → ℝ := fun w => ‖((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ / 2 with hrdef
  have hr : ∀ w, 0 < r w := fun w => half_pos (norm_pos_iff.mpr (fst_apply_ne_zero F a₀ w))
  set U : ∀ w : InfinitePlace F, Set w.Completion := fun w =>
    (if w ∈ I₁ then t₁ w else Set.univ) ∩ Metric.ball (((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w) (r w)
    with hUdef

  have hball : ∀ v : ↥S, ∃ ε : ℝ, 0 < ε ∧ ε ≤ ‖((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ ∧
      Metric.ball (((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) ε ⊆ (if v ∈ I₂ then t₂ v else Set.univ) := by
    intro v
    have hnorm : 0 < ‖((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ :=
      norm_pos_iff.mpr (snd_apply_ne_zero F a₀ v)
    by_cases hv : v ∈ I₂
    · obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp (ht₂ v hv).1 _ (ht₂ v hv).2
      refine ⟨min ε ‖((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖, lt_min hε hnorm, min_le_right _ _, ?_⟩
      rw [if_pos hv]
      exact (Metric.ball_subset_ball (min_le_left _ _)).trans hsub
    · exact ⟨_, hnorm, le_rfl, by rw [if_neg hv]; exact Set.subset_univ _⟩
  choose ε hε hεle hεsub using hball
  set V : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F) := fun v =>
    if hv : v ∈ S then Metric.ball (((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) (ε ⟨v, hv⟩) else Set.univ
    with hVdef
  have hVS : ∀ v (hv : v ∈ S), V v = Metric.ball (((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) (ε ⟨v, hv⟩) :=
    fun v hv => by rw [hVdef]; simp only [dif_pos hv]
  refine ⟨U, V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro w
    refine IsOpen.inter ?_ Metric.isOpen_ball
    by_cases hw : w ∈ I₁
    · simp only [if_pos hw]; exact (ht₁ w hw).1
    · simp only [if_neg hw]; exact isOpen_univ
  ·
    intro w
    refine ⟨?_, Metric.mem_ball_self (hr w)⟩
    by_cases hw : w ∈ I₁
    · simp only [if_pos hw]; exact (ht₁ w hw).2
    · simp only [if_neg hw]; exact Set.mem_univ _
  ·
    intro w h0
    have hsub : closure (U w) ⊆ Metric.closedBall (((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w) (r w) :=
      (closure_mono Set.inter_subset_right).trans Metric.closure_ball_subset_closedBall
    have h := hsub h0
    rw [Metric.mem_closedBall, dist_zero_left] at h
    have := hr w
    rw [hrdef] at h this
    simp only at h
    linarith [norm_nonneg (((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w)]
  ·
    intro w
    exact (isCompact_closedBall_completion F w _ (r w)).of_isClosed_subset isClosed_closure
      ((closure_mono Set.inter_subset_right).trans Metric.closure_ball_subset_closedBall)
  · intro v hv; rw [hVS v hv]; exact Metric.isOpen_ball
  · intro v hv; rw [hVS v hv]; exact IsUltrametricDist.isClosed_ball _ _
  · intro v hv; rw [hVS v hv]
    exact (isCompact_closedBall _ _).of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
      Metric.ball_subset_closedBall
  · intro v hv; rw [hVS v hv]; exact Metric.mem_ball_self (hε ⟨v, hv⟩)
  · intro v hv h0
    rw [hVS v hv, Metric.mem_ball, dist_zero_left] at h0
    exact (lt_irrefl _) (h0.trans_le (hεle ⟨v, hv⟩))
  ·
    intro a ha hU hV
    refine (hmemW a ha).mp (hprod ⟨hI₁ ?_, hI₂ ?_⟩)
    · intro w hw
      have h := (hU w).1
      simp only [if_pos (Finset.mem_coe.mp hw)] at h
      exact h
    · intro v hv
      have h := hV v v.2
      rw [hVS v v.2] at h
      have h' := hεsub v h
      simp only [if_pos (Finset.mem_coe.mp hv)] at h'
      exact h'

theorem idelicHaar_box (S : Finset (HeightOneSpectrum (𝓞 F)))
    (K : ∀ w : InfinitePlace F, Set w.Completion) (hK : ∀ w, IsCompact (K w)) (hK0 : ∀ w, (0 : w.Completion) ∉ K w)
    (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)) (hC : ∀ v ∈ S, IsCompact (C v))
    (hC0 : ∀ v ∈ S, (0 : v.adicCompletion F) ∉ C v) :
    letI := NumberField.Idele.ideleBorel F
    NumberField.Idele.idelicHaar F {a : (AdeleRing (𝓞 F) F)ˣ |
        (∀ w, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ∈ K w) ∧
        (∀ v ∈ S, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ C v) ∧
        a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S)} < ⊤ := by
  classical

  set E : Set (AdeleRing (𝓞 F) F) := {x | (∀ w, x.1 w ∈ K w) ∧
      ((∀ v ∈ S, x.2 v ∈ C v) ∧ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x.2 v ∈ v.adicCompletionIntegers F)}
    with hEdef
  set E' : Set (AdeleRing (𝓞 F) F) := {x | (∀ w, x.1 w ∈ (fun z : w.Completion => z⁻¹) '' K w) ∧
      ((∀ v ∈ S, x.2 v ∈ (fun z : v.adicCompletion F => z⁻¹) '' C v) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x.2 v ∈ v.adicCompletionIntegers F)} with hE'def
  have hE : IsCompact E := by
    have : E = (Set.univ.pi fun w : InfinitePlace F => K w) ×ˢ {x : FiniteAdeleRing (𝓞 F) F |
        (∀ v ∈ S, x v ∈ C v) ∧ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
      ext x; constructor
      · rintro ⟨h1, h2⟩; exact ⟨fun w _ => h1 w, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨fun w => h1 w (Set.mem_univ _), h2⟩
    rw [this]
    exact (isCompact_univ_pi hK).prod (isCompact_finiteBox F S C hC)
  have hE' : IsCompact E' := by
    have : E' = (Set.univ.pi fun w : InfinitePlace F => (fun z : w.Completion => z⁻¹) '' K w) ×ˢ
        {x : FiniteAdeleRing (𝓞 F) F | (∀ v ∈ S, x v ∈ (fun z : v.adicCompletion F => z⁻¹) '' C v) ∧
          ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
      ext x; constructor
      · rintro ⟨h1, h2⟩; exact ⟨fun w _ => h1 w, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨fun w => h1 w (Set.mem_univ _), h2⟩
    rw [this]
    exact (isCompact_univ_pi fun w => isCompact_inv_image (hK w) (hK0 w)).prod
      (isCompact_finiteBox F S _ fun v hv => isCompact_inv_image (hC v hv) (hC0 v hv))
  have hcpt : IsCompact ((Units.embedProduct (AdeleRing (𝓞 F) F)) ⁻¹' (E ×ˢ (MulOpposite.op '' E'))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hE.prod (hE'.image MulOpposite.continuous_op))
  refine (measure_mono ?_).trans_lt hcpt.measure_lt_top
  rintro a ⟨h1, h2, h3⟩
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff] at h3
  simp only [Finset.mem_coe] at h3
  have hinv1 : ∀ w : InfinitePlace F, ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      = (((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w)⁻¹ := fun w => by
    have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.1 w) a.mul_inv
    exact eq_inv_of_mul_eq_one_right h
  have hinv2 : ∀ v : HeightOneSpectrum (𝓞 F), ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
      = (((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)⁻¹ := fun v => by
    have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.2 v) a.mul_inv
    exact eq_inv_of_mul_eq_one_right h
  refine ⟨⟨h1, h2, fun v hv => (h3 v hv).1⟩, ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), ⟨?_, ?_, ?_⟩, rfl⟩
  · intro w; rw [hinv1]; exact ⟨_, h1 w, rfl⟩
  · intro v hv; rw [hinv2]; exact ⟨_, h2 v hv, rfl⟩
  · intro v hv; exact (h3 v hv).2

omit [NumberField F] in

theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.mpr ⟨continuous_pi fun w => ?_, continuous_pi fun w => ?_⟩
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp (continuous_apply _)

theorem exists_norm_le_schwartz (g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖g z‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := g.decay 0 0
  refine ⟨C, hCpos.le, fun z => ?_⟩
  have h := hC z
  rwa [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h

theorem indicator_one_eq_zero_or_one {X : Type*} (s : Set X) (x : X) :
    s.indicator (fun _ => (1 : ℂ)) x = 0 ∨ s.indicator (fun _ => (1 : ℂ)) x = 1 := by
  by_cases hx : x ∈ s
  · exact Or.inr (Set.indicator_of_mem hx _)
  · exact Or.inl (Set.indicator_of_notMem hx _)

theorem prod_eq_zero_or_one {ι : Type*} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, f i = 0 ∨ f i = 1) :
    (∏ i ∈ s, f i) = 0 ∨ (∏ i ∈ s, f i) = 1 := by
  by_cases h : ∀ i ∈ s, f i = 1
  · exact Or.inr (Finset.prod_eq_one h)
  · push Not at h
    obtain ⟨i, hi, hne⟩ := h
    exact Or.inl (Finset.prod_eq_zero hi ((hf i hi).resolve_right hne))

theorem prod_eq_ofReal_prod_re {ι : Type*} (s : Finset ι) (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im = 0) :
    (∏ i ∈ s, z i) = ((∏ i ∈ s, (z i).re : ℝ) : ℂ) := by
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun i hi => Complex.ext (by simp) (by simp [hz i hi])

end Ws1.C6F
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg.Ws1.C6F.ArchBridge P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg.Ws1 P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg.Ws1.C6F"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg.Ws1.C6F.ArchBridge P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg.Ws1"

end
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg.Ws1.C6F.ArchBridge P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg.Ws1 P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg.Ws1.C6F"

theorem solution
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hψS : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ r : v.adicCompletionIntegers F,
      ψ (@id (AdeleRing (𝓞 F) F) ((0 : InfiniteAdeleRing F),
        AdelicDock.splice (𝓞 F) F v 0 (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r))) = 1)
    (a₀ : (AdeleRing (𝓞 F) F)ˣ)
    (ha₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1)
    (N : Set (AdeleRing (𝓞 F) F)ˣ) (hN : IsOpen N) (ha₀N : a₀ ∈ N) :
    ∃ (B : AdeleRing (𝓞 F) F → ℂ) (μ : (AdeleRing (𝓞 F) F)ˣ → ℝ),
      B ∈ NumberField.AdelicFourier.schwartzBruhat F ∧
      (∃ (Bi : (w : InfinitePlace F) → w.Completion → ℂ) (Bf : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ),
        IsFactorizableStandardOutside B S Bi Bf) ∧
      (∀ a : (AdeleRing (𝓞 F) F)ˣ, (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * ψ (((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F)) = (μ a : ℂ)) ∧
      Measurable[NumberField.Idele.ideleBorel F] μ ∧ (∀ a, 0 ≤ μ a) ∧ (∃ M₀ : ℝ, ∀ a, μ a ≤ M₀) ∧
      (∀ a, NumberField.Idele.partAt F S a = a → a ∉ N → μ a = 0) ∧
      Integrable μ (NumberField.Idele.sPartMeasure F S) ∧ 0 < ∫ a, μ a ∂(NumberField.Idele.sPartMeasure F S) := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F

  obtain ⟨ψv, nψ, θr, θc, hlev, hnontriv, hfin, hprod, hθr, hθc, harchψ⟩ :=
    AutomorphicForm.exists_localComponents_of_isGlobalAddChar F ψ hψ
  set S' : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ hfin.toFinset with hS'

  obtain ⟨U, V, hUo, ha₀U, hU0, hUc, hVo, hVcl, hVk, ha₀V, hV0, hbox⟩ :=
    Ws1.C6F.exists_box_subset F S N hN a₀ ha₀N ha₀
  obtain ⟨g, gw, hg, hgc, hgs, hgU, hgre, hgpos⟩ :=
    NumberField.AdelicFourier.exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod F
      (fun w => ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w) U hUo ha₀U

  set hloc : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ := fun v =>
    if v ∈ S then (V v).indicator (fun _ => (1 : ℂ))
    else {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v (z * y) = 1}.indicator
      fun _ => (1 : ℂ) with hhloc
  set Tfin : FiniteAdeleRing (𝓞 F) F → ℂ := fun x =>
    (∏ v ∈ S', hloc v (x v)) *
      (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0) with hTfin

  have hsplice_cont : ∀ v : HeightOneSpectrum (𝓞 F),
      Continuous (fun t : v.adicCompletion F => AdelicDock.splice (𝓞 F) F v 0 t) := by
    intro v
    set Tv : Set (HeightOneSpectrum (𝓞 F)) := ({v} : Set (HeightOneSpectrum (𝓞 F)))ᶜ with hTvdef
    have hTv : Filter.cofinite ≤ Filter.principal Tv :=
      Filter.le_principal_iff.mpr (by rw [hTvdef, Filter.mem_cofinite, compl_compl]; exact Set.finite_singleton v)
    let Y := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal Tv)
    let gY : v.adicCompletion F → Y := fun t =>
      ⟨Function.update (⇑(0 : FiniteAdeleRing (𝓞 F) F)) v t, by
        rw [Filter.eventually_principal]
        intro w hw
        have hwv : w ≠ v := hw
        show Function.update (⇑(0 : FiniteAdeleRing (𝓞 F) F)) v t w ∈ (w.adicCompletionIntegers F : Set (w.adicCompletion F))
        rw [Function.update_of_ne hwv]
        exact zero_mem _⟩
    have hgY : Continuous gY := by
      rw [RestrictedProduct.continuous_rng_of_principal]
      exact continuous_const.update v continuous_id
    have hfac : (fun t : v.adicCompletion F => AdelicDock.splice (𝓞 F) F v 0 t)
        = RestrictedProduct.inclusion _ _ hTv ∘ gY := by
      funext t; rfl
    rw [hfac]
    exact (RestrictedProduct.continuous_inclusion hTv).comp hgY
  have hψv_eq : ∀ (v : HeightOneSpectrum (𝓞 F)) (t : v.adicCompletion F),
      ψv v t = ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) (AdelicDock.splice (𝓞 F) F v 0 t)) := by
    intro v t
    rw [hprod, finprod_eq_single _ v fun v' hv' => by
      rw [AdelicDock.splice_apply_of_ne (𝓞 F) F v 0 t hv']
      exact AddChar.map_zero_eq_one _]
    rw [AdelicDock.splice_apply_self]
  have hψv_cont : ∀ v : HeightOneSpectrum (𝓞 F), Continuous (ψv v) := by
    intro v
    have : (ψv v : v.adicCompletion F → ℂ) = fun t =>
        ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) (AdelicDock.splice (𝓞 F) F v 0 t)) := by
      funext t; exact hψv_eq v t
    rw [this]
    exact hψ.continuous.comp ((continuous_const.prodMk continuous_id).comp (hsplice_cont v))
  have hψv_unr : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ z : v.adicCompletion F,
      z ∈ v.adicCompletionIntegers F → ψv v z = 1 := by
    intro v hv z hz
    rw [hψv_eq]
    exact hψS v hv ⟨z, hz⟩
  have hL : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      IsOpen {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v (z * y) = 1} ∧
      IsCompact {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v (z * y) = 1} := by
    intro v hv
    letI : MeasurableSpace (v.adicCompletion F) := borel _
    haveI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
    haveI : LocallyCompactSpace (v.adicCompletion F) := locallyCompact_of_proper
    obtain ⟨x, -, hx⟩ := hnontriv v
    obtain ⟨hO, hK, -⟩ :=
      NumberField.AdelicFourier.fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one F v
        MeasureTheory.Measure.addHaar (ψv v) (hψv_cont v) (hψv_unr v hv) ⟨x, hx⟩
    exact ⟨hO, hK⟩

  have hind_lc : ∀ {X : Type} [TopologicalSpace X] (s : Set X), IsOpen s → IsClosed s →
      IsLocallyConstant (s.indicator fun _ => (1 : ℂ)) := by
    intro X _ s hso hsc
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ s
    · exact ⟨s, hso, hx, fun x' hx' => by rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]⟩
    · exact ⟨sᶜ, hsc.isOpen_compl, hx, fun x' hx' => by
        rw [Set.indicator_of_notMem (show x' ∉ s from hx'), Set.indicator_of_notMem hx]⟩
  have hloc_lc : ∀ v ∈ S', IsLocallyConstant (hloc v) := by
    intro v _
    by_cases hvS : v ∈ S
    · simp only [hhloc, if_pos hvS]; exact hind_lc _ (hVo v hvS) (hVcl v hvS)
    · simp only [hhloc, if_neg hvS]; exact hind_lc _ (hL v hvS).1 (hL v hvS).2.isClosed
  have hloc_cs : ∀ v ∈ S', HasCompactSupport (hloc v) := by
    intro v _
    by_cases hvS : v ∈ S
    · simp only [hhloc, if_pos hvS]
      exact HasCompactSupport.intro (hVk v hvS) fun y hy => Set.indicator_of_notMem hy _
    · simp only [hhloc, if_neg hvS]
      exact HasCompactSupport.intro (hL v hvS).2 fun y hy => Set.indicator_of_notMem hy _
  have hTfin_lc_cs : IsLocallyConstant Tfin ∧ HasCompactSupport Tfin := by
    refine NumberField.AdelicFourier.isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
      F S' hloc (fun v hv => ?_) (fun v hv => ?_)
    · exact hloc_lc v hv
    · exact hloc_cs v hv

  set T : AdeleRing (𝓞 F) F → ℂ := fun x => g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * Tfin x.2 with hT
  have hTmem : T ∈ NumberField.AdelicFourier.pureTensorSet F :=
    NumberField.AdelicFourier.tensor_mem_pureTensorSet g Tfin hTfin_lc_cs.1 hTfin_lc_cs.2
  set B : AdeleRing (𝓞 F) F → ℂ := NumberField.AdelicFourier.fourierIntegral ψ (adelicAddHaar (𝓞 F) F) T with hB
  set c₀ : ℝ := ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal) ^ 2 with hc₀
  set μf : (AdeleRing (𝓞 F) F)ˣ → ℝ := fun a => c₀ * (T ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).re with hμf

  have hρc : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := Ws1.C6F.continuous_ringEquiv_mixedSpace F
  have hTfin_cont : Continuous Tfin := hTfin_lc_cs.1.continuous
  have hT_cont : Continuous T :=
    (g.continuous.comp (hρc.comp continuous_fst)).mul (hTfin_cont.comp continuous_snd)
  have hloc01 : ∀ (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F), hloc v y = 0 ∨ hloc v y = 1 := by
    intro v y
    by_cases hv : v ∈ S
    · simp only [hhloc, if_pos hv]; exact Ws1.C6F.indicator_one_eq_zero_or_one _ _
    · simp only [hhloc, if_neg hv]; exact Ws1.C6F.indicator_one_eq_zero_or_one _ _
  have hTfin01 : ∀ x, Tfin x = 0 ∨ Tfin x = 1 := by
    intro x
    simp only [hTfin]
    rcases Ws1.C6F.prod_eq_zero_or_one S' (fun v => hloc v (x v)) (fun v _ => hloc01 v (x v)) with h0 | h1
    · exact Or.inl (by rw [h0, zero_mul])
    · rw [h1, one_mul]
      by_cases hc : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' → x v ∈ v.adicCompletionIntegers F
      · exact Or.inr (if_pos hc)
      · exact Or.inl (if_neg hc)
  have hgreal : ∀ y : InfiniteAdeleRing F,
      g (InfiniteAdeleRing.ringEquiv_mixedSpace F y) = ((∏ w, (gw w (y w)).re : ℝ) : ℂ) := fun y => by
    rw [hg y]; exact Ws1.C6F.prod_eq_ofReal_prod_re _ _ fun w _ => (hgre w (y w)).1
  have hgre_nonneg : ∀ y : InfiniteAdeleRing F, 0 ≤ ∏ w, (gw w (y w)).re := fun y =>
    Finset.prod_nonneg fun w _ => (hgre w (y w)).2
  have hTval : ∀ x, T x = ((∏ w, (gw w (x.1 w)).re : ℝ) : ℂ) * Tfin x.2 := fun x => by
    simp only [hT]; rw [hgreal]
  have hT_im : ∀ x, (T x).im = 0 := by
    intro x
    rw [hTval]
    rcases hTfin01 x.2 with h | h
    · rw [h, mul_zero, Complex.zero_im]
    · rw [h, mul_one, Complex.ofReal_im]
  have hT_re_nonneg : ∀ x, 0 ≤ (T x).re := by
    intro x
    rw [hTval]
    rcases hTfin01 x.2 with h | h
    · rw [h, mul_zero, Complex.zero_re]
    · rw [h, mul_one, Complex.ofReal_re]; exact hgre_nonneg x.1
  obtain ⟨Cg, hCg0, hCg⟩ := Ws1.C6F.exists_norm_le_schwartz F g
  have hT_bound : ∀ x, ‖T x‖ ≤ Cg := by
    intro x
    have hx : T x = g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * Tfin x.2 := by simp only [hT]
    rw [hx, norm_mul]
    rcases hTfin01 x.2 with h | h
    · rw [h, norm_zero, mul_zero]; exact hCg0
    · rw [h, norm_one, mul_one]; exact hCg _
  have hc₀nn : 0 ≤ c₀ := by rw [hc₀]; positivity

  have hT_ne : ∀ a : (AdeleRing (𝓞 F) F)ˣ, T ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ≠ 0 →
      (∀ w, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ∈ U w) ∧
      (∀ v ∈ S, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ V v) := by
    intro a hne
    simp only [hT] at hne
    obtain ⟨hg0, hf0⟩ := mul_ne_zero_iff.mp hne
    refine ⟨fun w => ?_, fun v hv => ?_⟩
    · rw [hg] at hg0
      have hw := (Finset.prod_ne_zero_iff.mp hg0) w (Finset.mem_univ w)
      exact hgU w (subset_tsupport _ (Function.mem_support.mpr hw))
    · simp only [hTfin] at hf0
      obtain ⟨hp0, -⟩ := mul_ne_zero_iff.mp hf0
      have hvS' : v ∈ S' := by rw [hS']; exact Finset.mem_union_left _ hv
      have h1 := (Finset.prod_ne_zero_iff.mp hp0) v hvS'
      simp only [hhloc, if_pos hv] at h1
      exact Set.mem_of_indicator_ne_zero h1
  have hInt : Integrable μf (NumberField.Idele.sPartMeasure F S) := by
    letI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ := NumberField.Idele.ideleBorel F
    haveI : BorelSpace (AdeleRing (𝓞 F) F)ˣ := NumberField.Idele.borelSpace_ideleBorel F
    haveI := NumberField.Idele.isHaarMeasure_idelicHaar F
    have hμc : Continuous μf :=
      continuous_const.mul (Complex.continuous_re.comp (hT_cont.comp Units.continuous_val))
    have hμ_nonneg : ∀ a, 0 ≤ μf a := fun a => mul_nonneg hc₀nn (hT_re_nonneg _)
    have hμ_le : ∀ a, μf a ≤ c₀ * Cg := fun a =>
      mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans (hT_bound _)) hc₀nn
    set US : Set (AdeleRing (𝓞 F) F)ˣ :=
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ) with hUSdef
    have hUSo : IsOpen US := NumberField.Idele.isOpen_unitIdelesOutside F _
    change Integrable μf (Measure.map (NumberField.Idele.partAt F S) ((NumberField.Idele.idelicHaar F).restrict US))
    refine (integrable_map_measure hμc.aestronglyMeasurable (NumberField.Idele.measurable_partAt F S).aemeasurable).mpr ?_
    set BOX : Set (AdeleRing (𝓞 F) F)ˣ := {a |
      (∀ w, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ∈ closure (U w)) ∧
      (∀ v ∈ S, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ V v) ∧
      a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S)} with hBOXdef
    have hBOXfin : NumberField.Idele.idelicHaar F BOX < ⊤ :=
      Ws1.C6F.idelicHaar_box F S (fun w => closure (U w)) hUc hU0 V hVk hV0
    have hBOXmeas : MeasurableSet BOX := by
      have h1 : IsClosed {a : (AdeleRing (𝓞 F) F)ˣ |
          ∀ w, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ∈ closure (U w)} := by
        have : {a : (AdeleRing (𝓞 F) F)ˣ | ∀ w, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ∈ closure (U w)}
            = ⋂ w, (fun a : (AdeleRing (𝓞 F) F)ˣ => ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w) ⁻¹' closure (U w) := by
          ext a; simp
        rw [this]
        exact isClosed_iInter fun w => isClosed_closure.preimage
          ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val))
      have h2 : IsClosed {a : (AdeleRing (𝓞 F) F)ˣ |
          ∀ v ∈ S, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ V v} := by
        have : {a : (AdeleRing (𝓞 F) F)ˣ | ∀ v ∈ S, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ V v}
            = ⋂ v, ⋂ (_ : v ∈ S), (fun a : (AdeleRing (𝓞 F) F)ˣ => ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) ⁻¹' V v := by
          ext a; simp
        rw [this]
        exact isClosed_iInter fun v => isClosed_iInter fun hv => (hVcl v hv).preimage
          ((RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val))
      have : BOX = {a : (AdeleRing (𝓞 F) F)ˣ | ∀ w, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ∈ closure (U w)}
          ∩ {a : (AdeleRing (𝓞 F) F)ˣ | ∀ v ∈ S, ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ V v} ∩ US := by
        ext a; simp only [hBOXdef, hUSdef, Set.mem_setOf_eq, Set.mem_inter_iff, SetLike.mem_coe, and_assoc]
      rw [this]
      exact (h1.measurableSet.inter h2.measurableSet).inter hUSo.measurableSet
    refine Integrable.mono' (g := BOX.indicator fun _ => c₀ * Cg) ?_
      ((hμc.comp (NumberField.Idele.continuous_partAt F S)).aestronglyMeasurable) ?_
    · refine IntegrableOn.integrable_indicator (integrableOn_const ?_) hBOXmeas
      exact ((Measure.restrict_apply_le _ _).trans_lt hBOXfin).ne
    · rw [ae_restrict_iff' hUSo.measurableSet]
      refine ae_of_all _ fun a haUS => ?_
      rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hμ_nonneg _)]
      by_cases h0 : μf (NumberField.Idele.partAt F S a) = 0
      · rw [h0]; exact Set.indicator_nonneg (fun _ _ => mul_nonneg hc₀nn hCg0) _
      · have hne : T ((NumberField.Idele.partAt F S a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ≠ 0 := by
          intro hz; apply h0; simp only [hμf, hz, Complex.zero_re, mul_zero]
        obtain ⟨hU, hV⟩ := hT_ne _ hne
        have haBOX : a ∈ BOX := by
          refine ⟨fun w => subset_closure ?_, fun v hv => ?_, haUS⟩
          · have := hU w
            rwa [NumberField.Idele.partAt_fst] at this
          · have := hV v hv
            rwa [NumberField.Idele.partAt_snd_of_mem F S a hv] at this
        rw [Set.indicator_of_mem haBOX]
        exact hμ_le _
  refine ⟨B, μf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
    haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
    exact NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat F (adelicAddHaar (𝓞 F) F) hψ
      (NumberField.AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet hTmem)
  ·
    haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
    haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
    letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
    haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
    letI : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F) := fun v => borel _
    haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F) := fun v => ⟨rfl⟩
    haveI : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) := fun v => locallyCompact_of_proper
    set ν : Measure (FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
    set μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F) := fun v => Measure.addHaar with hμv

    obtain ⟨Bi₀, hBi₀⟩ := Ws1.C6F.arch_factor F ψ hψ g gw hg hgc hgs

    have hsplit := fun x : AdeleRing (𝓞 F) F =>
      NumberField.AdelicFourier.fourierIntegral_pureTensor_eq F (adelicAddHaar (𝓞 F) F) ν hψ.continuous
        (NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ) g hTfin_lc_cs.1 hTfin_lc_cs.2 x

    have hScof : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v ∉ (S : Set (HeightOneSpectrum (𝓞 F))) :=
      S.finite_toSet.compl_mem_cofinite
    have hunr' : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v z = 1 :=
      hScof.mono fun v hv => hψv_unr v hv
    have hψf_cont : Continuous (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) :=
      hψ.continuous.comp (continuous_const.prodMk continuous_id)
    have hα := fun w : FiniteAdeleRing (𝓞 F) F =>
      NumberField.AdelicFourier.inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq F ν μv
        (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) hψf_cont
        ψv hψv_cont (fun x => hprod x) hunr' S' hloc hloc_lc hloc_cs w

    have hLO : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' →
        {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v (z * y) = 1}
          = (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      intro v hv
      have hvS : v ∉ S := fun h => hv (by rw [hS']; exact Finset.mem_union_left _ h)
      have hn : nψ v = 0 := by
        by_contra hne
        exact hv (by rw [hS']; exact Finset.mem_union_right _ (hfin.mem_toFinset.mpr hne))
      obtain ⟨x, hx, hx1⟩ := hnontriv v
      rw [hn, zero_add] at hx
      exact NumberField.AdelicFourier.setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one_eq_of_level_zero F v
        (ψv v) (hψv_unr v hvS) ⟨x, hx, hx1⟩

    have hF3 : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ w : v.adicCompletion F,
        NumberField.AdelicFourier.fourierIntegral (ψv v) (μv v)
            ({y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v (z * y) = 1}.indicator
              fun _ => (1 : ℂ)) w
          = ((μv v).real {y : v.adicCompletion F | ∀ z : v.adicCompletion F,
                z ∈ v.adicCompletionIntegers F → ψv v (z * y) = 1} : ℂ) *
            (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) w := by
      intro v hv w
      obtain ⟨x, -, hx⟩ := hnontriv v
      exact (NumberField.AdelicFourier.fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one F v
        (μv v) (ψv v) (hψv_cont v) (hψv_unr v hv) ⟨x, hx⟩).2.2 w

    have hSS' : S ⊆ S' := by rw [hS']; exact Finset.subset_union_left
    have hnOpos : 0 < ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) := by
      rw [Measure.real, ENNReal.toReal_pos_iff]
      exact ⟨(AdelicBox.isOpen_integralFiniteAdeles F).measure_pos ν ⟨0, fun v => zero_mem _⟩,
        (AdelicBox.isCompact_integralFiniteAdeles F).measure_lt_top⟩
    have hnO0 : ((ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hnOpos.ne'
    set Lset : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F) := fun v =>
      {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v (z * y) = 1} with hLset
    set Bf₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ := fun v t =>
      (((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ))⁻¹ *
        NumberField.AdelicFourier.fourierIntegral (ψv v) (μv v) (hloc v) t with hBf₀
    set κ : ℂ := ∏ v ∈ S' \ S, ((((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ))⁻¹ *
      ((μv v).real (Lset v) : ℂ)) with hκ
    set C₁ : ℂ := ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ) /
          (((ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume : ℝ) : ℂ)
            * ((ν (AdelicBox.integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)) with hC₁
    set K : ℂ := C₁ * ((ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℝ) : ℂ) * κ with hK
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
    refine ⟨fun w t => (if w = w₀ then K else 1) * Bi₀ w t, Bf₀, fun x => ?_⟩

    have hI : ∀ y : FiniteAdeleRing (𝓞 F) F,
        (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' →
            ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v (z * y v) = 1 then (1 : ℂ) else 0)
          = if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' → y v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0 := by
      intro y
      refine if_congr ⟨fun h v hv => ?_, fun h v hv => ?_⟩ rfl rfl
      · have h' : y v ∈ Lset v := h v hv
        rw [hLset] at h'; simp only at h'; rw [hLO v hv] at h'; exact h'
      · have h' : y v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := h v hv
        rw [← hLO v hv] at h'; exact h'
    have hFf : ∀ y : FiniteAdeleRing (𝓞 F) F,
        NumberField.AdelicFourier.fourierIntegral
            (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν Tfin y
          = ((ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℝ) : ℂ) * (((∏ v ∈ S, Bf₀ v (y v)) *
              ∏ v ∈ S' \ S, ((((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ))⁻¹ *
                (((μv v).real (Lset v) : ℂ) *
                  (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (y v)))) *
            (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' → y v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) := by
      intro y
      have h := hα y
      rw [inv_mul_eq_iff_eq_mul₀ hnO0] at h
      simp only [hTfin]
      rw [h, hI y, ← Finset.union_sdiff_of_subset hSS', Finset.prod_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset hSS']
      congr 3
      refine Finset.prod_congr rfl fun v hv => ?_
      have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
      simp only [hhloc, if_neg hvS]
      rw [hF3 v hvS]

    have hBx : B x = C₁ *
        NumberField.AdelicFourier.fourierIntegral
          (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
          MeasureTheory.volume (g : mixedEmbedding.mixedSpace F → ℂ) (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) *
        NumberField.AdelicFourier.fourierIntegral
          (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν Tfin x.2 := by
      simp only [hB, hT]
      exact hsplit x
    have hBi : (∏ w, (if w = w₀ then K else 1) * Bi₀ w (x.1 w)) = K * ∏ w, Bi₀ w (x.1 w) := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
      simp
    rw [hBx, hBi₀ x.1, hFf x.2]
    by_cases hx : x ∈ integralOutside S
    ·
      have hxS : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x.2 v ∈ v.adicCompletionIntegers F := hx
      rw [Set.indicator_of_mem hx]
      dsimp only
      rw [hBi, if_pos fun v hv => hxS v fun h => hv (hSS' h)]
      have hind : ∀ v ∈ S' \ S,
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x.2 v) = 1 :=
        fun v hv => Set.indicator_of_mem (hxS v (Finset.mem_sdiff.mp hv).2) _
      have hsd : (∏ v ∈ S' \ S, ((((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ))⁻¹ *
          (((μv v).real (Lset v) : ℂ) *
            (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x.2 v)))) = κ := by
        rw [hκ]
        exact Finset.prod_congr rfl fun v hv => by rw [hind v hv, mul_one]
      rw [hsd, hK]
      ring
    ·
      rw [Set.indicator_of_notMem hx]
      simp only [integralOutside, Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨v, hvS, hxv⟩ := hx
      by_cases hvS' : v ∈ S'
      · have hv : v ∈ S' \ S := Finset.mem_sdiff.mpr ⟨hvS', hvS⟩
        rw [Finset.prod_eq_zero hv (by rw [Set.indicator_of_notMem hxv, mul_zero, mul_zero])]
        simp
      · rw [if_neg fun h => hxv (h v hvS')]
        simp
  ·
    intro a
    haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
    haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
    have h1 : (∫ x, B x * ψ (((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F))
        = NumberField.AdelicFourier.fourierIntegral ψ (adelicAddHaar (𝓞 F) F) B
            (-(((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))) := by
      rw [NumberField.AdelicFourier.fourierIntegral_def]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show B x * ψ (((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x)
        = ψ (-(x * -(((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)))) * B x
      rw [mul_neg, neg_neg, mul_comm x (((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)), mul_comm (B x)]
    rw [h1, hB, NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet F
      (adelicAddHaar (𝓞 F) F) hψ hTmem, neg_neg]
    simp only [hμf, hc₀]
    apply Complex.ext
    · simp [hT_im]
    · simp [hT_im]
  ·
    letI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ := NumberField.Idele.ideleBorel F
    haveI : BorelSpace (AdeleRing (𝓞 F) F)ˣ := NumberField.Idele.borelSpace_ideleBorel F
    exact (continuous_const.mul (Complex.continuous_re.comp (hT_cont.comp Units.continuous_val))).measurable
  ·
    intro a
    exact mul_nonneg hc₀nn (hT_re_nonneg _)
  ·
    refine ⟨c₀ * Cg, fun a => mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans (hT_bound _)) hc₀nn⟩
  ·
    intro a ha haN
    by_contra hμ
    have hne : T ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ≠ 0 := by
      intro h0; apply hμ; simp only [hμf, h0, Complex.zero_re, mul_zero]
    obtain ⟨hU, hV⟩ := hT_ne a hne
    exact haN (hbox a ha hU hV)
  ·
    exact hInt
  ·
    letI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ := NumberField.Idele.ideleBorel F
    haveI : BorelSpace (AdeleRing (𝓞 F) F)ˣ := NumberField.Idele.borelSpace_ideleBorel F
    haveI := NumberField.Idele.isHaarMeasure_idelicHaar F
    have hμc : Continuous μf :=
      continuous_const.mul (Complex.continuous_re.comp (hT_cont.comp Units.continuous_val))
    have hμ_nonneg : ∀ a, 0 ≤ μf a := fun a => mul_nonneg hc₀nn (hT_re_nonneg _)
    set US : Set (AdeleRing (𝓞 F) F)ˣ :=
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ) with hUSdef
    have hUSo : IsOpen US := NumberField.Idele.isOpen_unitIdelesOutside F _
    have hInt' : Integrable (μf ∘ NumberField.Idele.partAt F S) ((NumberField.Idele.idelicHaar F).restrict US) :=
      (integrable_map_measure hμc.aestronglyMeasurable
        (NumberField.Idele.measurable_partAt F S).aemeasurable).mp hInt
    change 0 < ∫ a, μf a ∂(Measure.map (NumberField.Idele.partAt F S) ((NumberField.Idele.idelicHaar F).restrict US))
    rw [integral_map (NumberField.Idele.measurable_partAt F S).aemeasurable hμc.aestronglyMeasurable]
    refine (integral_pos_iff_support_of_nonneg (fun a => hμ_nonneg _) hInt').mpr ?_

    have ha₀US : a₀ ∈ US := by
      rw [hUSdef, SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff,
        IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
      intro v hv
      have hv' : v ∉ S := fun h => hv (Finset.mem_coe.mpr h)
      refine ⟨?_, ?_⟩
      · change ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F
        rw [ha₀ v hv']; exact one_mem _
      · change ((a₀⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F
        rw [Ws1.C6F.snd_apply_inv, ha₀ v hv', inv_one]; exact one_mem _
    have ha₀fix : NumberField.Idele.partAt F S a₀ = a₀ := by
      refine Units.ext (Prod.ext (NumberField.Idele.partAt_fst F S a₀) (Subtype.ext (funext fun v => ?_)))
      by_cases hv : v ∈ S
      · exact NumberField.Idele.partAt_snd_of_mem F S a₀ hv
      · exact (NumberField.Idele.partAt_snd_of_not_mem F S a₀ hv).trans (ha₀ v hv).symm
    have hprod1 : (∏ v ∈ S', hloc v ((((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v)) = 1 := by
      refine Finset.prod_eq_one fun v _ => ?_
      by_cases hvS : v ∈ S
      · simp only [hhloc, if_pos hvS]; exact Set.indicator_of_mem (ha₀V v hvS) _
      · simp only [hhloc, if_neg hvS]
        have hmem : (((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v ∈
            {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v (z * y) = 1} := by
          intro z hz
          rw [ha₀ v hvS, mul_one]
          exact hψv_unr v hvS z hz
        exact Set.indicator_of_mem hmem _
    have hite : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' →
        (((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v ∈ v.adicCompletionIntegers F := by
      intro v hv
      have hvS : v ∉ S := fun h => hv (by rw [hS']; exact Finset.mem_union_left _ h)
      rw [ha₀ v hvS]; exact one_mem _
    have hTfin₀ : Tfin (((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) = 1 := by
      simp only [hTfin]
      rw [hprod1, one_mul, if_pos hite]
    have hc₀pos : 0 < c₀ := by
      rw [hc₀]
      exact pow_pos (ENNReal.toReal_pos (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne) 2
    have hpos₀ : 0 < μf a₀ := by
      simp only [hμf]
      refine mul_pos hc₀pos ?_
      rw [hTval, hTfin₀, mul_one, Complex.ofReal_re]
      exact Finset.prod_pos fun w _ => hgpos w
    have hWo : IsOpen {a : (AdeleRing (𝓞 F) F)ˣ | 0 < μf (NumberField.Idele.partAt F S a)} :=
      isOpen_lt continuous_const (hμc.comp (NumberField.Idele.continuous_partAt F S))
    calc (0 : ENNReal) < NumberField.Idele.idelicHaar F
          ({a : (AdeleRing (𝓞 F) F)ˣ | 0 < μf (NumberField.Idele.partAt F S a)} ∩ US) :=
          (hWo.inter hUSo).measure_pos _ ⟨a₀, by rw [Set.mem_setOf_eq, ha₀fix]; exact hpos₀, ha₀US⟩
      _ ≤ ((NumberField.Idele.idelicHaar F).restrict US) (Function.support (μf ∘ NumberField.Idele.partAt F S)) := by
          rw [Measure.restrict_apply' hUSo.measurableSet]
          exact measure_mono fun a ha => ⟨ne_of_gt ha.1, ha.2⟩

end S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg
end P2MW
export P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg (solution)
