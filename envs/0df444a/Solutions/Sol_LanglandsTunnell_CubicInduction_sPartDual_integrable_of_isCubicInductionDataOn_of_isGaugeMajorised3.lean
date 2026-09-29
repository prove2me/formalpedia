-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/f0fd08ce-edab-570b-bb07-b3ac4d043b61

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_Idele_integrable_sPartMeasure_of_norm_le_mul_prod
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isArchZeta31ConvergentAbove_dualWhittakerFn3_whittakerArch_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar
import Theorems.Thm_LanglandsTunnell_CubicInduction_aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn
import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3.LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal NumberField.TateGlobal NumberField.AdelicLevel"

open scoped NNReal ENNReal

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsArchCompAt TateLocal.addCharLevel TateLocal.localBorel TateLocal.selfDualHaarAt TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.modulus TateLocal.modulus_mul signEpsilon HeckeTate.heckeDatum CubicInduction.exists_isArchZeta31ConvergentAbove_dualWhittakerFn3_whittakerArch_of_isCubicInductionDataOn CubicInduction.exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn CubicInduction.psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar CubicInduction.aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "CubicInductionData IsCubicInductionDataOn IsGL3PsiWhittakerFn gl3CyclicSubspace transposeInv3 psiLoc AdelicGL embedMat2 iotaGL coe_iotaGL componentAtN archComponentN componentAt3 archComponent3 LocalGL3 IsRamifiedIn IsBadPlace inducedLevelAt diagUnitGL2 diagHom_apply lowerUnipotent21 dualWhittakerFn3 weylPrime3 archRoot₁ archRoot₂ archRootSum IsGaugeMajorised3 localZeta31 localZeta30 IsLocalZeta31ConvergentAbove archZeta30 archZetaDual31 IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove exists_isArchZeta31ConvergentAbove_dualWhittakerFn3_whittakerArch_of_isCubicInductionDataOn exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn"
namespace SPartArchAnte
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section LocalUnits

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

variable (w : HeightOneSpectrum (𝓞 ℚ))

theorem borelSpace_loc : BorelSpace (w.adicCompletion ℚ) := borelSpace_localBorel ℚ w

attribute [local instance] borelSpace_loc

theorem borelSpace_locUnits : BorelSpace (w.adicCompletion ℚ)ˣ := by
  refine ⟨?_⟩
  have h : (inferInstance : TopologicalSpace (w.adicCompletion ℚ)ˣ) =
      TopologicalSpace.induced (Units.val : (w.adicCompletion ℚ)ˣ → w.adicCompletion ℚ) inferInstance :=
    Units.isEmbedding_val₀.eq_induced
  show MeasurableSpace.comap Units.val (borel (w.adicCompletion ℚ)) = borel (w.adicCompletion ℚ)ˣ
  exact ((congrArg (fun t => @borel (w.adicCompletion ℚ)ˣ t) h).trans borel_comap).symm

attribute [local instance] borelSpace_locUnits

def locMul : Measure (w.adicCompletion ℚ)ˣ :=
  Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ w))

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ w).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm w.asIdeal : ℝ≥0) ≠ 0 := by
    have h : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
    exact_mod_cast (show Ideal.absNorm w.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm w.asIdeal : ℝ≥0) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ w) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm w.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ w) : ℝ) / 2))
    • Measure.addHaarMeasure (integersPositiveCompacts ℚ w) : Measure (w.adicCompletion ℚ))).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

attribute [local instance] isAddHaarMeasure_selfDualHaarAt

theorem range_val :
    Set.range (Units.val : (w.adicCompletion ℚ)ˣ → w.adicCompletion ℚ) = ({0}ᶜ : Set (w.adicCompletion ℚ)) := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩

theorem measurableEmbedding_val :
    MeasurableEmbedding (Units.val : (w.adicCompletion ℚ)ˣ → w.adicCompletion ℚ) :=
  MeasurableEmbedding.iff_comap_eq.mpr ⟨Units.val_injective, rfl, by
    rw [range_val]
    exact (measurableSet_singleton 0).compl⟩

theorem locMul_apply (A : Set (w.adicCompletion ℚ)ˣ) :
    locMul w A = mulMeasure (selfDualHaarAt ℚ w) (Units.val '' A) :=
  (measurableEmbedding_val w).comap_apply _ _

def dens (x : w.adicCompletion ℚ) : ℝ≥0∞ := ((TateLocal.modulus x : ℝ≥0) : ℝ≥0∞)⁻¹

theorem measurable_dens : Measurable (dens w) := by
  have h : dens w = fun x => ((‖x‖₊ : ℝ≥0) : ℝ≥0∞)⁻¹ :=
    funext fun x => by rw [dens, modulus_adicCompletion_eq_nnnorm]
  rw [h]
  exact measurable_nnnorm.coe_nnreal_ennreal.inv

theorem dens_ne_zero (x : w.adicCompletion ℚ) : dens w x ≠ 0 :=
  ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top

theorem mulMeasure_apply_eq (μ : Measure (w.adicCompletion ℚ)) {A : Set (w.adicCompletion ℚ)} (hA : MeasurableSet A) :
    mulMeasure μ A = ∫⁻ x in A ∩ {0}ᶜ, dens w x ∂μ := by
  rw [mulMeasure, withDensity_apply _ hA, Measure.restrict_restrict hA]
  rfl

open scoped Pointwise in

theorem map_mul_left_selfDualHaarAt (u : (w.adicCompletion ℚ)ˣ) :
    Measure.map (fun x : w.adicCompletion ℚ => (u : w.adicCompletion ℚ) * x) (selfDualHaarAt ℚ w) =
      ((distribHaarChar (w.adicCompletion ℚ) u : ℝ≥0∞))⁻¹ • selfDualHaarAt ℚ w := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul]
  have hset : (fun x : w.adicCompletion ℚ => (u : w.adicCompletion ℚ) * x) ⁻¹' s = u⁻¹ • s := by
    ext x
    rw [Set.mem_inv_smul_set_iff, Set.mem_preimage, Units.smul_def, smul_eq_mul]
  rw [hset, ← distribHaarChar_mul (selfDualHaarAt ℚ w) u⁻¹ s, map_inv,
    ENNReal.coe_inv ((distribHaarChar_pos (A := w.adicCompletion ℚ) (g := u)).ne')]

theorem mulMeasure_preimage_mul_left (u : (w.adicCompletion ℚ)ˣ) {B : Set (w.adicCompletion ℚ)}
    (hB : MeasurableSet B) :
    mulMeasure (selfDualHaarAt ℚ w) ((fun x : w.adicCompletion ℚ => (u : w.adicCompletion ℚ) * x) ⁻¹' B) =
      mulMeasure (selfDualHaarAt ℚ w) B := by
  set T : w.adicCompletion ℚ → w.adicCompletion ℚ := fun x => (u : w.adicCompletion ℚ) * x with hT
  have hmeas : Measurable T := measurable_const_mul _
  set χ : ℝ≥0∞ := (distribHaarChar (w.adicCompletion ℚ) u : ℝ≥0∞) with hχ
  have hχ0 : χ ≠ 0 := ENNReal.coe_ne_zero.mpr (distribHaarChar_pos (A := w.adicCompletion ℚ) (g := u)).ne'
  have hχtop : χ ≠ ⊤ := ENNReal.coe_ne_top
  have hdens : ∀ x : w.adicCompletion ℚ, dens w x = χ * dens w (T x) := by
    intro x
    simp only [dens, hT, TateLocal.modulus_mul, modulus_coe_units, ENNReal.coe_mul, hχ]
    rw [ENNReal.mul_inv (Or.inl hχ0) (Or.inl hχtop), ← mul_assoc, ENNReal.mul_inv_cancel hχ0 hχtop, one_mul]
  have hB' : MeasurableSet (B ∩ {0}ᶜ) := hB.inter (measurableSet_singleton 0).compl
  rw [mulMeasure_apply_eq w _ (hmeas hB), mulMeasure_apply_eq w _ hB]
  have hpre : T ⁻¹' B ∩ {0}ᶜ = T ⁻¹' (B ∩ {0}ᶜ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, hT,
      Units.mul_right_eq_zero]
  rw [hpre]
  calc ∫⁻ x in T ⁻¹' (B ∩ {0}ᶜ), dens w x ∂(selfDualHaarAt ℚ w)
      = ∫⁻ x in T ⁻¹' (B ∩ {0}ᶜ), χ * dens w (T x) ∂(selfDualHaarAt ℚ w) :=
        setLIntegral_congr_fun (hmeas hB') fun x _ => hdens x
    _ = χ * ∫⁻ x in T ⁻¹' (B ∩ {0}ᶜ), dens w (T x) ∂(selfDualHaarAt ℚ w) :=
        lintegral_const_mul χ ((measurable_dens w).comp hmeas)
    _ = χ * ∫⁻ y in B ∩ {0}ᶜ, dens w y ∂(Measure.map T (selfDualHaarAt ℚ w)) := by
        rw [setLIntegral_map hB' (measurable_dens w) hmeas]
    _ = χ * (χ⁻¹ * ∫⁻ y in B ∩ {0}ᶜ, dens w y ∂(selfDualHaarAt ℚ w)) := by
        rw [map_mul_left_selfDualHaarAt, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    _ = ∫⁻ y in B ∩ {0}ᶜ, dens w y ∂(selfDualHaarAt ℚ w) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hχ0 hχtop, one_mul]

theorem image_val_preimage_mul_left (u : (w.adicCompletion ℚ)ˣ) (A : Set (w.adicCompletion ℚ)ˣ) :
    Units.val '' ((fun y => u * y) ⁻¹' A) =
      (fun x : w.adicCompletion ℚ => (u : w.adicCompletion ℚ) * x) ⁻¹' (Units.val '' A) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨u * y, hy, by rw [Units.val_mul]⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨u⁻¹ * z, by simpa using hz, ?_⟩
    have hzx' : (z : w.adicCompletion ℚ) = (u : w.adicCompletion ℚ) * x := hzx
    rw [Units.val_mul, hzx', ← mul_assoc, Units.inv_mul, one_mul]

theorem isMulLeftInvariant_locMul : (locMul w).IsMulLeftInvariant := by
  refine ⟨fun u => ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_const_mul u) hA, locMul_apply, locMul_apply, image_val_preimage_mul_left]
  exact mulMeasure_preimage_mul_left w u ((measurableEmbedding_val w).measurableSet_image.mpr hA)

theorem isFiniteMeasureOnCompacts_locMul : IsFiniteMeasureOnCompacts (locMul w) := by
  refine ⟨fun C hC => ?_⟩
  have hCK : IsCompact (Units.val '' C) := hC.image Units.continuous_val
  rw [locMul_apply, mulMeasure_apply_eq w _ hCK.measurableSet]
  obtain ⟨M, hM⟩ := (hC.image ((continuous_nnnorm.comp Units.continuous_coe_inv))).bddAbove
  have hle : ∀ x ∈ Units.val '' C ∩ {0}ᶜ, dens w x ≤ (M : ℝ≥0∞) := by
    rintro _ ⟨⟨u, hu, rfl⟩, -⟩
    have h1 : dens w (u : w.adicCompletion ℚ) = ((‖((u⁻¹ : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ)‖₊ : ℝ≥0) : ℝ≥0∞) := by
      rw [dens, modulus_adicCompletion_eq_nnnorm, Units.val_inv_eq_inv_val, nnnorm_inv,
        ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr u.ne_zero)]
    rw [h1]
    exact ENNReal.coe_le_coe.mpr (hM ⟨u, hu, rfl⟩)
  calc ∫⁻ x in Units.val '' C ∩ {0}ᶜ, dens w x ∂(selfDualHaarAt ℚ w)
      ≤ ∫⁻ x in Units.val '' C ∩ {0}ᶜ, (M : ℝ≥0∞) ∂(selfDualHaarAt ℚ w) := setLIntegral_mono measurable_const hle
    _ = (M : ℝ≥0∞) * selfDualHaarAt ℚ w (Units.val '' C ∩ {0}ᶜ) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top
        ((measure_mono Set.inter_subset_left).trans_lt hCK.measure_lt_top)

theorem isOpenPosMeasure_locMul : (locMul w).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  have hUo : IsOpen (Units.val '' U) := (IsOpenUnits.isOpenEmbedding_unitsVal).isOpenMap _ hU
  have hsub : Units.val '' U ∩ {0}ᶜ = Units.val '' U :=
    Set.inter_eq_self_of_subset_left (by rw [← range_val]; exact Set.image_subset_range _ _)
  rw [locMul_apply, mulMeasure_apply_eq w _ hUo.measurableSet, hsub]
  intro h0
  have hae := (lintegral_eq_zero_iff (measurable_dens w)).mp h0
  rw [Filter.EventuallyEq, ae_iff] at hae
  have huniv : {x : w.adicCompletion ℚ | ¬dens w x = (0 : (w.adicCompletion ℚ) → ℝ≥0∞) x} = Set.univ :=
    Set.eq_univ_of_forall fun x => dens_ne_zero w x
  rw [huniv, Measure.restrict_apply_univ] at hae
  exact hUo.measure_ne_zero (selfDualHaarAt ℚ w) (hne.image _) hae

theorem isHaarMeasure_locMul : (locMul w).IsHaarMeasure :=
  @Measure.IsHaarMeasure.mk _ _ _ _ _ (isFiniteMeasureOnCompacts_locMul w) (isMulLeftInvariant_locMul w)
    (isOpenPosMeasure_locMul w)

end LocalUnits

section Components

theorem componentAt3_iotaGL_diagUnitGL2 (w : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    componentAt3 (𝓞 ℚ) ℚ w (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 (M4aHerbrand.finPart w a)) := by
  refine Units.ext ?_
  ext i j
  rw [componentAt3, componentAtN, Matrix.GeneralLinearGroup.map_apply, coe_iotaGL, coe_iotaGL]
  fin_cases i <;> fin_cases j <;> simp [embedMat2]
  rfl

theorem archComponent3_iotaGL_diagUnitGL2 (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 (M4aHerbrand.infPart a)) := by
  refine Units.ext ?_
  ext i j
  rw [archComponent3, archComponentN, Matrix.GeneralLinearGroup.map_apply, coe_iotaGL, coe_iotaGL]
  fin_cases i <;> fin_cases j <;> simp [embedMat2]
  rfl

theorem diagUnitGL2_one {A : Type*} [CommRing A] : diagUnitGL2 (1 : Aˣ) = 1 := by
  rw [← diagHom_apply]
  exact map_one _

end Components

section Idele

variable {F : Type} [Field F] [NumberField F]

def archEmbed : (InfiniteAdeleRing F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def locEmbed (w : HeightOneSpectrum (𝓞 F)) : (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F w)

theorem coe_archEmbed (u : (InfiniteAdeleRing F)ˣ) :
    ((archEmbed u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = ((u : InfiniteAdeleRing F), 1) := rfl

theorem infPart_archEmbed (u : (InfiniteAdeleRing F)ˣ) : M4aHerbrand.infPart (archEmbed (F := F) u) = u :=
  Units.ext rfl

theorem finPart_archEmbed (w : HeightOneSpectrum (𝓞 F)) (u : (InfiniteAdeleRing F)ˣ) :
    M4aHerbrand.finPart w (archEmbed (F := F) u) = 1 :=
  Units.ext rfl

theorem infPart_locEmbed (w : HeightOneSpectrum (𝓞 F)) (t : (w.adicCompletion F)ˣ) :
    M4aHerbrand.infPart (locEmbed (F := F) w t) = 1 :=
  Units.ext rfl

theorem finPart_locEmbed_self (w : HeightOneSpectrum (𝓞 F)) (t : (w.adicCompletion F)ˣ) :
    M4aHerbrand.finPart w (locEmbed (F := F) w t) = t :=
  Units.ext (localUnit_apply_self (𝓞 F) F w t)

theorem finPart_locEmbed_of_ne {w w' : HeightOneSpectrum (𝓞 F)} (h : w' ≠ w) (t : (w.adicCompletion F)ˣ) :
    M4aHerbrand.finPart w' (locEmbed (F := F) w t) = 1 :=
  Units.ext (localUnit_apply_of_ne (𝓞 F) F w t h)

theorem idele_ext {a b : (AdeleRing (𝓞 F) F)ˣ} (h₁ : M4aHerbrand.infPart a = M4aHerbrand.infPart b)
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 F), M4aHerbrand.finPart w a = M4aHerbrand.finPart w b) : a = b := by
  refine Units.ext (Prod.ext ?_ ?_)
  · exact congrArg Units.val h₁
  · refine RestrictedProduct.ext (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun v => ?_
    exact congrArg Units.val (h₂ v)

theorem eq_archEmbed_mul_prod (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    (ha : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) :
    a = archEmbed (M4aHerbrand.infPart a) * ∏ w ∈ S, locEmbed w (M4aHerbrand.finPart w a) := by
  refine idele_ext ?_ fun w' => ?_
  · rw [map_mul, map_prod, infPart_archEmbed, Finset.prod_eq_one fun w _ => infPart_locEmbed w _, mul_one]
  · rw [map_mul, map_prod, finPart_archEmbed, one_mul]
    by_cases hw' : w' ∈ S
    · rw [Finset.prod_eq_single w' (fun w _ hne => finPart_locEmbed_of_ne (Ne.symm hne) _)
        (fun h => absurd hw' h), finPart_locEmbed_self]
    · rw [Finset.prod_eq_one fun w hw => finPart_locEmbed_of_ne (by rintro rfl; exact hw' hw) _]
      exact Units.ext (ha w' hw')

theorem char_eq_prod_localChar (τ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : (AdeleRing (𝓞 F) F)ˣ) (ha : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1)
    (harch : τ (archEmbed (M4aHerbrand.infPart a)) = 1) :
    ((τ a : ℂˣ) : ℂ) = ∏ w ∈ S, ((localChar τ w (M4aHerbrand.finPart w a) : ℂˣ) : ℂ) := by
  conv_lhs => rw [eq_archEmbed_mul_prod S a ha]
  rw [map_mul, harch, one_mul, map_prod, Units.coe_prod]
  rfl

theorem ideleNorm_eq_norm_mul_prod_modulus (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    (ha : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) :
    ideleNorm F a = ‖(a : AdeleRing (𝓞 F) F).1‖ * ∏ w ∈ S, ((modulus ((a : AdeleRing (𝓞 F) F).2 w) : ℝ≥0) : ℝ) := by
  rw [ideleNorm, NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F a,
    ← InfiniteAdeleRing.norm_def]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
  · exact Finset.prod_congr rfl fun w _ => by rw [modulus_adicCompletion_eq_nnnorm, coe_nnnorm]
  · intro w hw
    by_contra hwS
    exact hw (show ‖(a : AdeleRing (𝓞 F) F).2 w‖ = 1 by rw [ha w hwS, norm_one])

theorem cpow_prod_ofReal_nonneg {ι : Type*} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) (z : ℂ) :
    (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ z = ∏ i ∈ s, ((r i : ℝ) : ℂ) ^ z := by
  classical
  refine @Finset.induction_on ι (fun s => (∀ i ∈ s, 0 ≤ r i) →
      (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ z = ∏ i ∈ s, ((r i : ℝ) : ℂ) ^ z) _ s (fun _ => by simp) ?_ hr
  intro a s ha ih hr
  rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (hr a (Finset.mem_insert_self a s))
      (Finset.prod_nonneg fun i hi => hr i (Finset.mem_insert_of_mem hi)) z,
    ih fun i hi => hr i (Finset.mem_insert_of_mem hi)]

theorem ideleNorm_cpow_eq (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    (ha : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) (z : ℂ) :
    ((ideleNorm F a : ℝ) : ℂ) ^ z =
      ((‖(a : AdeleRing (𝓞 F) F).1‖ : ℝ) : ℂ) ^ z *
        ∏ w ∈ S, ((((modulus ((a : AdeleRing (𝓞 F) F).2 w) : ℝ≥0) : ℝ) : ℂ)) ^ z := by
  have h1 : (0 : ℝ) ≤ ‖(a : AdeleRing (𝓞 F) F).1‖ := by
    rw [InfiniteAdeleRing.norm_def]
    exact Finset.prod_nonneg fun v _ => pow_nonneg (norm_nonneg _) _
  have h2 : (0 : ℝ) ≤ ∏ w ∈ S, ((modulus ((a : AdeleRing (𝓞 F) F).2 w) : ℝ≥0) : ℝ) :=
    Finset.prod_nonneg fun w _ => NNReal.coe_nonneg _
  rw [ideleNorm_eq_norm_mul_prod_modulus S a ha, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg h1 h2 z,
    cpow_prod_ofReal_nonneg S (fun w => ((modulus ((a : AdeleRing (𝓞 F) F).2 w) : ℝ≥0) : ℝ))
      (fun w _ => NNReal.coe_nonneg _)]

end Idele

section Arch

def realPlace : InfinitePlace ℚ := Classical.arbitrary _

theorem archEmbed_eq_archCentralUnit (u : (InfiniteAdeleRing ℚ)ˣ) :
    archEmbed u = NumberField.AdelicVolume.archCentralUnit ℚ realPlace
      (Units.map (Pi.evalMonoidHom (fun w : InfinitePlace ℚ => w.Completion) realPlace) u) := by
  refine Units.ext (Prod.ext ?_ rfl)
  funext w
  have hw : w = realPlace := Subsingleton.elim _ _
  subst hw
  rw [NumberField.AdelicVolume.archCentralUnit_fst_self]
  rfl

theorem twist_archEmbed_eq_one (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hτ : ∀ w : InfinitePlace ℚ, w.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ τ w 0 0)
    (u : (InfiniteAdeleRing ℚ)ˣ) : τ (archEmbed u) = 1 := by
  rw [archEmbed_eq_archCentralUnit, ← archUnitHom_apply]
  have h := hτ realPlace (IsTotallyReal.isReal _)
    (Units.map (Pi.evalMonoidHom (fun w : InfinitePlace ℚ => w.Completion) realPlace) u)
  rw [archLocalChar, MonoidHom.comp_apply, mul_zero, Complex.cpow_zero, zpow_zero, mul_one] at h
  exact Units.val_eq_one.mp h

end Arch

section Integrands

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

def gDir (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (garch : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ)
    (u : (InfiniteAdeleRing ℚ)ˣ) : ℂ :=
  Warch (iotaGL (diagUnitGL2 u) * 1 * garch) * (((1 : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) u : ℂˣ) : ℂ) *
    ((‖(u : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)

theorem integral_gDir {mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ} (ν : Measure (InfiniteAdeleRing ℚ)ˣ)
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (garch : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ) :
    ∫ u, gDir Warch garch s u ∂ν = archZeta30 ν (fun h => Warch (h * garch)) 1 s 1 :=
  rfl

def hDir (w : HeightOneSpectrum (𝓞 ℚ)) (Wloc : LocalGL3 w → ℂ) (χ : (w.adicCompletion ℚ)ˣ →* ℂˣ)
    (gw : LocalGL3 w) (s : ℂ) (t : (w.adicCompletion ℚ)ˣ) : ℂ :=
  Wloc (iotaGL (diagUnitGL2 t) * gw) * ((χ t : ℂˣ) : ℂ) *
    ((TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)

theorem integral_hDir (w : HeightOneSpectrum (𝓞 ℚ)) {mT : MeasurableSpace (w.adicCompletion ℚ)ˣ}
    (μ : Measure (w.adicCompletion ℚ)ˣ) (Wloc : LocalGL3 w → ℂ) (χ : (w.adicCompletion ℚ)ˣ →* ℂˣ)
    (gw : LocalGL3 w) (s : ℂ) :
    ∫ t, hDir w Wloc χ gw s t ∂μ = localZeta30 w μ Wloc χ s gw :=
  rfl

open scoped Classical in

def gDual (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (garch : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ)
    (u : (InfiniteAdeleRing ℚ)ˣ) : ℂ :=
  (∫ y : mixedEmbedding.mixedSpace ℚ,
      dualWhittakerFn3 Warch (iotaGL (diagUnitGL2 u) *
        lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * garch)) *
    ((‖(u : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)

def archDual {mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ} (ν : Measure (InfiniteAdeleRing ℚ)ˣ)
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (garch : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ) : ℂ :=
  ∫ u, gDual Warch garch s u ∂ν

def cO (w : HeightOneSpectrum (𝓞 ℚ)) : ℂ :=
  (((selfDualHaarAt ℚ w).real (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)) : ℂ))⁻¹

def hDual (w : HeightOneSpectrum (𝓞 ℚ)) (Wloc : LocalGL3 w → ℂ) (χ : (w.adicCompletion ℚ)ˣ →* ℂˣ)
    (gw : LocalGL3 w) (s : ℂ) (t : (w.adicCompletion ℚ)ˣ) : ℂ :=
  cO w * ((∫ x : w.adicCompletion ℚ,
      dualWhittakerFn3 Wloc (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x * gw) ∂(selfDualHaarAt ℚ w)) *
    ((χ t : ℂˣ) : ℂ) * ((TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))

theorem integral_hDual (w : HeightOneSpectrum (𝓞 ℚ)) {mT : MeasurableSpace (w.adicCompletion ℚ)ˣ}
    (μ : Measure (w.adicCompletion ℚ)ˣ) (Wloc : LocalGL3 w → ℂ) (χ : (w.adicCompletion ℚ)ˣ →* ℂˣ)
    (gw : LocalGL3 w) (s : ℂ) :
    ∫ t, hDual w Wloc χ gw s t ∂μ =
      cO w * localZeta31 w μ (selfDualHaarAt ℚ w) (dualWhittakerFn3 Wloc) χ s gw :=
  integral_const_mul _ _

end Integrands

section PointwiseGeneric

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

open scoped Classical in

theorem dual_factor_one (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (Wloc : (w : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 w → ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℂ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ha : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → (a : AdeleRing (𝓞 ℚ) ℚ).2 w = 1) :
    (∫ y : mixedEmbedding.mixedSpace ℚ,
        dualWhittakerFn3 Warch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
          lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
      (∏ v ∈ S,
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
          ∫ x : v.adicCompletion ℚ,
            dualWhittakerFn3 (Wloc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
              lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g) ∂(selfDualHaarAt ℚ v))) *
      ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1) =
      gDual Warch (archComponent3 (𝓞 ℚ) ℚ g) s (M4aHerbrand.infPart a) *
        ∏ w ∈ S, hDual w (Wloc w) 1 (componentAt3 (𝓞 ℚ) ℚ w g) s (M4aHerbrand.finPart w a) := by
  simp only [gDual, hDual, cO, M4aHerbrand.coe_infPart_apply, M4aHerbrand.coe_finPart_apply,
    archComponent3_iotaGL_diagUnitGL2, componentAt3_iotaGL_diagUnitGL2, MonoidHom.one_apply, Units.val_one, mul_one]
  rw [ideleNorm_cpow_eq S a ha (s - 1)]
  simp only [Finset.prod_mul_distrib]
  ring

end PointwiseGeneric

section SFin

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

theorem secondCountableTopology_loc (w : HeightOneSpectrum (𝓞 ℚ)) : SecondCountableTopology (w.adicCompletion ℚ) := by
  haveI : Countable (WithVal (w.valuation ℚ)) := (WithVal.equiv (w.valuation ℚ)).injective.countable
  infer_instance

theorem sFinite_selfDualHaarAt (w : HeightOneSpectrum (𝓞 ℚ)) : SFinite (selfDualHaarAt ℚ w) := by
  haveI := borelSpace_loc w
  haveI := secondCountableTopology_loc w
  haveI := isAddHaarMeasure_selfDualHaarAt w
  infer_instance

end SFin

section TransposeInv

variable {A : Type*} [CommRing A]

theorem transposeInv3_mul' (g h : GL (Fin 3) A) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  apply Units.ext
  simp [transposeInv3, Matrix.transpose_mul, Matrix.mul_inv_rev]

def transposeInv3Hom (A : Type*) [CommRing A] : GL (Fin 3) A →* GL (Fin 3) A where
  toFun := transposeInv3
  map_one' := Units.ext (by simp [transposeInv3])
  map_mul' := transposeInv3_mul'

theorem transposeInv3Hom_apply (g : GL (Fin 3) A) : transposeInv3Hom A g = transposeInv3 g := rfl

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g :=
  Units.ext (Matrix.transpose_transpose _)

theorem continuous_transposeInv3 [TopologicalSpace A] :
    Continuous (transposeInv3 : GL (Fin 3) A → GL (Fin 3) A) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin 3) A => (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : GL (Fin 3) A => ((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ
    exact Units.continuous_val.matrix_transpose

end TransposeInv

section Bridge

open scoped Classical in

theorem integral_smul_map_ringEquiv_symm [MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    (c : ℝ≥0∞) (φ : InfiniteAdeleRing ℚ → ℂ) :
    ∫ x, φ x ∂(c • Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm volume) =
      c.toReal • ∫ y, φ ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) ∂volume := by
  rw [integral_smul_measure]
  congr 1
  obtain ⟨hc, hcs⟩ := (Equiv.isHomeomorph_iff (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).toEquiv).mp
    (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace ℚ)
  let eH : InfiniteAdeleRing ℚ ≃ₜ mixedEmbedding.mixedSpace ℚ :=
    ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).toEquiv, hc, hcs⟩
  have h : (⇑(InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm : mixedEmbedding.mixedSpace ℚ → InfiniteAdeleRing ℚ) =
      ⇑eH.toMeasurableEquiv.symm := by
    rw [Homeomorph.toMeasurableEquiv_symm_coe]
    rfl
  rw [h, integral_map_equiv]

end Bridge

end LanglandsTunnell.CubicInduction.SPartArchAnte

end

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3.LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3.LanglandsTunnell.CubicInduction.SPartArchAnte"

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hne : X.whittakerArch ≠ 0)
    (hatS : ∀ w ∈ S, X.whittakerLoc w 1 = 1 ∧
      (∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w), F ≠ 0 → X.whittakerLoc w ∈ gl3CyclicSubspace F) ∧
      (∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧
        ∀ k ∈ Uw, ∀ g : LocalGL3 w, X.whittakerLoc w (g * k) = X.whittakerLoc w g) ∧
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (hωcond : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsRamifiedIn K v → ∃ a ≤ inducedLevelAt K μ v,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar X.centralChar v) a)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (hArch :
      (Continuous X.whittakerArch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf X.whittakerArch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        X.whittakerArch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((X.centralChar (E z) : ℂˣ) : ℂ) * X.whittakerArch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 =
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s) ∧
          (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
          (∀ (σ₁ σ₂ : ℝ) (N : ℕ), ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
            |s.im| ^ N *
              ‖P s *
                (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                  (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C) ∧
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => X.whittakerArch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => X.whittakerArch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((X.centralChar (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul X.whittakerArch (σ.comp E) s 1 ≠ 0)
 :
    ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            (∏ v ∈ S,
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 ∫ x : v.adicCompletion ℚ,
                   dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                     lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                     ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS := by
  intro τ hτ g

  have hB : ∀ w : HeightOneSpectrum (𝓞 ℚ), @BorelSpace (w.adicCompletion ℚ)ˣ _
      (@Units.instMeasurableSpace _ _ (LanglandsTunnell.TateLocal.localBorel ℚ w)) :=
    fun w => borelSpace_locUnits w

  obtain ⟨σA, hA⟩ := LanglandsTunnell.CubicInduction.exists_isArchZeta31ConvergentAbove_dualWhittakerFn3_whittakerArch_of_isCubicInductionDataOn K hdeg ψ hψ μ hμ uR aR uC kC huR huC hlev hns D U gen S hS X hX hcont hcontW hcontW' hW hW' hne hatS hcent hωcond E hE a ha aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul hArch (archComponent3 (𝓞 ℚ) ℚ g)

  have hloc : ∀ w ∈ S, ∃ σw : ℝ,
      letI := LanglandsTunnell.TateLocal.localBorel ℚ w
      IsLocalZeta31ConvergentAbove w (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ w)))
        (selfDualHaarAt ℚ w) (dualWhittakerFn3 (X.whittakerLoc w)) 1 (componentAt3 (𝓞 ℚ) ℚ w g) σw := by
    intro w hw
    obtain ⟨hψv, -, -⟩ := LanglandsTunnell.CubicInduction.psiLoc_ne_one_and_level_clauses_of_isGlobalAddChar ψ hψ w
    have h1 : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ w (1 : (w.adicCompletion ℚ)ˣ →* ℂˣ) 0 :=
      (LanglandsTunnell.TateLocal.hasConductorExponentAt_zero_iff ℚ w).mpr fun _ _ => rfl
    obtain ⟨σ0, σ1, hconv⟩ :=
      LanglandsTunnell.CubicInduction.exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn ψ w hψv
        (X.whittakerLoc w) (hX.whittakerLoc_law w) (hatS w hw).2.2.1 (hatS w hw).2.2.2 (localChar X.centralChar w)
        (hcent w hw).1 (hcent w hw).2 1 ⟨0, h1⟩
    refine ⟨σ1, ?_⟩
    have h1inv : (1 : (w.adicCompletion ℚ)ˣ →* ℂˣ)⁻¹ = 1 := by ext; simp
    have h := (hconv (transposeInv3 (weylPrime3⁻¹ * componentAt3 (𝓞 ℚ) ℚ w g))).2
    rwa [transposeInv3_transposeInv3, mul_inv_cancel_left, h1inv] at h
  choose! σloc hσloc using hloc
  set σ₀ : ℝ := |σA| + ∑ w ∈ S, |σloc w| + 1 with hσ₀
  refine ⟨σ₀, fun s hs => ?_⟩
  have hsA : σA < s.re := by
    have h1 : σA ≤ |σA| := le_abs_self _
    have h2 : 0 ≤ ∑ w ∈ S, |σloc w| := Finset.sum_nonneg fun w _ => abs_nonneg _
    rw [hσ₀] at hs; linarith
  have hsw : ∀ w ∈ S, σloc w < s.re := by
    intro w hw
    have h1 : σloc w ≤ |σloc w| := le_abs_self _
    have h2 : |σloc w| ≤ ∑ w ∈ S, |σloc w| :=
      Finset.single_le_sum (f := fun w => |σloc w|) (fun w _ => abs_nonneg _) hw
    have h3 : 0 ≤ |σA| := abs_nonneg _
    rw [hσ₀] at hs; linarith

  have hM := LanglandsTunnell.CubicInduction.aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn K hdeg ψ hψ μ hμ uR aR uC kC huR huC hlev hns D U gen S hS X hX hcont hcontW hcontW' hW hW' hne hatS hcent hωcond E hE a ha aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul hArch τ hτ g s

  haveI hSF : SFinite ν_add := by rw [hν_add]; infer_instance
  set r : ℝ := |(a : ℝ)| ^ ((1 : ℝ) / 2) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast ha)) _
  have hbridge : ∀ φ : InfiniteAdeleRing ℚ → ℂ,
      ∫ x, φ x ∂ν_add = r • ∫ y, φ ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) ∂volume := by
    intro φ
    rw [hν_add, integral_smul_map_ringEquiv_symm, ENNReal.toReal_ofReal hr0.le]

  refine @NumberField.Idele.integrable_sPartMeasure_of_norm_le_mul_prod ℚ _ _ S mT _ ν_mul _
    (fun w => @Units.instMeasurableSpace _ _ (LanglandsTunnell.TateLocal.localBorel ℚ w)) hB
    (fun w => locMul w) (fun w _ => isHaarMeasure_locMul w) _
    (fun u => ‖gDual X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) s u‖)
    (fun w t => ‖hDual w (X.whittakerLoc w) 1 (componentAt3 (𝓞 ℚ) ℚ w g) s t‖)
    (fun u => norm_nonneg _) (fun w _ t => norm_nonneg _) ?_ ?_ ?_ ?_ ?_ ?_
  ·
    exact hM.2.1.norm
  ·
    intro w hw
    have h3 := (hM.2.2 w hw).const_mul (cO w)
    refine (h3.norm).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [hDual, MonoidHom.one_apply, Units.val_one, mul_one]
  ·
    have hI : Integrable (fun u : (InfiniteAdeleRing ℚ)ˣ => ∫ x : InfiniteAdeleRing ℚ,
        ‖dualWhittakerFn3 X.whittakerArch (iotaGL (diagUnitGL2 u) * lowerUnipotent21 x * archComponent3 (𝓞 ℚ) ℚ g) *
          (((1 : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) u : ℂˣ) : ℂ) * ((‖(u : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)‖ ∂ν_add) ν_mul :=
      (hA s hsA).integral_norm_prod_left
    refine ((hI.const_mul r⁻¹).hasFiniteIntegral).mono (Filter.Eventually.of_forall fun u => ?_)
    rw [norm_norm, Real.norm_eq_abs]
    refine le_trans ?_ (le_abs_self _)

    set fu : InfiniteAdeleRing ℚ → ℂ := fun x =>
      dualWhittakerFn3 X.whittakerArch (iotaGL (diagUnitGL2 u) * lowerUnipotent21 x * archComponent3 (𝓞 ℚ) ℚ g) with hfu
    set cu : ℂ := ((‖(u : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1) with hcu
    have h1 : (∫ y, fu ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) ∂volume) = r⁻¹ • ∫ x, fu x ∂ν_add := by
      rw [hbridge, inv_smul_smul₀ hr0.ne']
    have hone : ∀ x, ‖fu x * (((1 : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) u : ℂˣ) : ℂ) * cu‖ = ‖fu x‖ * ‖cu‖ := by
      intro x
      rw [MonoidHom.one_apply, Units.val_one, mul_one, norm_mul]
    calc ‖gDual X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) s u‖
        = ‖(∫ y, fu ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) ∂volume) * cu‖ := rfl
      _ = r⁻¹ * (‖∫ x, fu x ∂ν_add‖ * ‖cu‖) := by
          rw [h1, norm_mul, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le, mul_assoc]
      _ ≤ r⁻¹ * ((∫ x, ‖fu x‖ ∂ν_add) * ‖cu‖) := by
          gcongr
          exact norm_integral_le_integral_norm _
      _ = r⁻¹ * ∫ x, ‖fu x * (((1 : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) u : ℂˣ) : ℂ) * cu‖ ∂ν_add := by
          rw [← integral_mul_const]
          simp_rw [hone]
  ·
    intro w hw
    letI : MeasurableSpace (w.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ w
    haveI := sFinite_selfDualHaarAt w
    have hI : Integrable (fun t : (w.adicCompletion ℚ)ˣ => ∫ x : w.adicCompletion ℚ,
        ‖dualWhittakerFn3 (X.whittakerLoc w) (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ w g) *
          (((1 : (w.adicCompletion ℚ)ˣ →* ℂˣ) t : ℂˣ) : ℂ) *
            ((TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)‖ ∂(selfDualHaarAt ℚ w)) (locMul w) :=
      (hσloc w hw s (hsw w hw)).integral_norm_prod_left
    refine ((hI.const_mul ‖cO w‖).hasFiniteIntegral).mono (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_norm, Real.norm_eq_abs]
    refine le_trans ?_ (le_abs_self _)
    set ft : w.adicCompletion ℚ → ℂ := fun x =>
      dualWhittakerFn3 (X.whittakerLoc w) (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ w g) with hft
    set ct : ℂ := (((1 : (w.adicCompletion ℚ)ˣ →* ℂˣ) t : ℂˣ) : ℂ) *
      ((TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) with hct
    have hmul : ∀ x, ft x * (((1 : (w.adicCompletion ℚ)ˣ →* ℂˣ) t : ℂˣ) : ℂ) *
        ((TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) = ft x * ct := fun x => by
      rw [hct, mul_assoc]
    calc ‖hDual w (X.whittakerLoc w) 1 (componentAt3 (𝓞 ℚ) ℚ w g) s t‖
        = ‖cO w * ((∫ x, ft x ∂(selfDualHaarAt ℚ w)) * ct)‖ := by
          simp only [hDual, hft, hct, mul_assoc]
      _ = ‖cO w‖ * (‖∫ x, ft x ∂(selfDualHaarAt ℚ w)‖ * ‖ct‖) := by rw [norm_mul, norm_mul]
      _ ≤ ‖cO w‖ * ((∫ x, ‖ft x‖ ∂(selfDualHaarAt ℚ w)) * ‖ct‖) := by
          gcongr
          exact norm_integral_le_integral_norm _
      _ = ‖cO w‖ * ∫ x, ‖ft x * (((1 : (w.adicCompletion ℚ)ˣ →* ℂˣ) t : ℂˣ) : ℂ) *
            ((TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)‖ ∂(selfDualHaarAt ℚ w) := by
          rw [← integral_mul_const]
          simp_rw [hmul, norm_mul]
  ·
    exact hM.1
  ·
    intro b hb
    have hfac := dual_factor_one X.whittakerArch X.whittakerLoc S g s b hb
    have hτ1 : ‖((τ b : ℂˣ) : ℂ)‖ = 1 := hτ.2.2 b
    rw [mul_right_comm _ (((τ b : ℂˣ) : ℂ)), norm_mul, hτ1, mul_one, hfac, norm_mul, norm_prod]

end S_LanglandsTunnell_CubicInduction_sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3 (solution)
