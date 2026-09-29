-- Prove2me | solution 1 for ModularCurve.JZero.exists_pointHt_le_mul_baseHt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/534ed5bb-ca17-5f18-8365-2fab8d971e01

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicCurve_pointHt_mul_eq_add
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
import Theorems.Thm_ModularCurve_constantsAreBase_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_pointHt_le_mul_baseHt
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

noncomputable section

namespace P2MHm

section Pivot

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

theorem exists_forall_ord_le (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) :
    ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => v.ord (s i)) Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

theorem ord_pivot_le (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
  classical
  have hex := exists_forall_ord_le hr s v
  have : pivotIndex s v hr = Classical.choose hex := by rw [pivotIndex, dif_pos hex]
  rw [this]
  exact Classical.choose_spec hex j

theorem evalVec_apply (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (i : Fin r) :
    evalVec s v i = v.evalAt (s i * (s (pivotIndex s v hr))⁻¹) := by
  rw [evalVec]
  simp only [dif_pos hr]

theorem evalVec_pivot (hr : 0 < r) (s : Fin r → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) : evalVec s v (pivotIndex s v hr) = 1 := by
  rw [evalVec_apply hr, mul_inv_cancel₀ (hs _), Place.evalAt_one]

theorem evalVec_ne_zero (hr : 0 < r) (s : Fin r → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) : evalVec s v ≠ 0 := by
  intro h
  have := congrFun h (pivotIndex s v hr)
  rw [evalVec_pivot hr s hs v] at this
  exact one_ne_zero this

theorem ratio_pivot_mem (hr : 0 < r) (s : Fin r → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) (i : Fin r) :
    s i * (s (pivotIndex s v hr))⁻¹ ∈ v.toValuationSubring :=
  v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs i) (inv_ne_zero (hs _)))
    (by rw [v.ord_mul (hs i) (inv_ne_zero (hs _)), v.ord_inv]; linarith [ord_pivot_le hr s v i])

end Pivot

section AbsHeight

theorem normLogHeight_eq_of_le (E E' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : E ≤ E')
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ E'] {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) (hx : ∀ i, x i ∈ E) :
    (Module.finrank ℚ E : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hx i⟩ : E))
      = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h (hx i)⟩ : E')) :=
  (Height.inv_finrank_mul_logHeight_inclusion (K := E) (L := E') h (fun i => (⟨x i, hx i⟩ : E))).symm

theorem absLogHeight_eq_of_mem {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    (E' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E'] (h : ∀ i, x i ∈ E') :
    absLogHeight x = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h i⟩ : E')) := by
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ E' :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  haveI := finiteDimensional_adjoin_range x
  exact normLogHeight_eq_of_le _ E' hle x (fun i => IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩)

theorem absLogHeight_smul {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    {c : AlgebraicClosure ℚ} (hc : c ≠ 0) : absLogHeight (c • x) = absLogHeight x := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (insert c (Set.range x)) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun y _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral
  have hcE : c ∈ E' := IntermediateField.subset_adjoin ℚ _ (Set.mem_insert c _)
  have hx' : ∀ i, x i ∈ E' := fun i =>
    IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem c ⟨i, rfl⟩)
  have hcx : ∀ i, (c • x) i ∈ E' := fun i => by
    rw [Pi.smul_apply, smul_eq_mul]; exact mul_mem hcE (hx' i)
  rw [absLogHeight_eq_of_mem (c • x) E' hcx, absLogHeight_eq_of_mem x E' hx']
  congr 1
  convert Height.logHeight_smul_eq_logHeight (fun i => (⟨x i, hx' i⟩ : E')) (c := ⟨c, hcE⟩) ?_ using 2
  all_goals first
    | exact fun h0 => hc (by simpa using congrArg Subtype.val h0)
    | (funext i; apply Subtype.ext; simp [Pi.smul_apply, smul_eq_mul])

theorem absLogHeight_mul_eq_add {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (x : ι → AlgebraicClosure ℚ) (y : κ → AlgebraicClosure ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (e : μ ≃ ι × κ) :
    absLogHeight (fun m => x (e m).1 * y (e m).2) = absLogHeight x + absLogHeight y := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (Set.range x ∪ Set.range y) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  have hxE : ∀ i, x i ∈ E' := fun i => IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
  have hyE : ∀ j, y j ∈ E' := fun j => IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, rfl⟩)
  have hpE : ∀ m, x (e m).1 * y (e m).2 ∈ E' := fun m => mul_mem (hxE _) (hyE _)
  rw [absLogHeight_eq_of_mem _ E' hpE, absLogHeight_eq_of_mem x E' hxE, absLogHeight_eq_of_mem y E' hyE,
    ← mul_add]
  congr 1
  have hx' : (fun i => (⟨x i, hxE i⟩ : E')) ≠ 0 := by
    intro h; apply hx; funext i; simpa using congrArg Subtype.val (congrFun h i)
  have hy' : (fun j => (⟨y j, hyE j⟩ : E')) ≠ 0 := by
    intro h; apply hy; funext j; simpa using congrArg Subtype.val (congrFun h j)
  have hfun : (fun m => (⟨x (e m).1 * y (e m).2, hpE m⟩ : E'))
      = (fun q : ι × κ => (⟨x q.1, hxE q.1⟩ : E') * (⟨y q.2, hyE q.2⟩ : E')) ∘ e := by
    funext m
    apply Subtype.ext
    rfl
  rw [hfun, Height.logHeight_comp_equiv e, Height.logHeight_fun_mul_eq hx' hy']

end AbsHeight

section Eval

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem evalAt_add_of_mem (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem smul_mem_of_mem (v : Place (AlgebraicClosure ℚ) F) (a : AlgebraicClosure ℚ) {f : F}
    (hf : f ∈ v.toValuationSubring) : a • f ∈ v.toValuationSubring := by
  rw [Algebra.smul_def]
  exact mul_mem (v.algebraMap_mem' a) hf

theorem evalAt_smul_of_mem (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational)
    (a : AlgebraicClosure ℚ) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (a • f) = a * v.evalAt f := by
  rw [Algebra.smul_def, v.evalAt_mul_of_mem hv (v.algebraMap_mem' a) hf, v.evalAt_algebraMap_eq]

theorem sum_smul_mem {ι : Type} (S : Finset ι) (v : Place (AlgebraicClosure ℚ) F)
    (c : ι → AlgebraicClosure ℚ) {f : ι → F} (hf : ∀ i, f i ∈ v.toValuationSubring) :
    (∑ i ∈ S, c i • f i) ∈ v.toValuationSubring :=
  sum_mem fun i _ => smul_mem_of_mem v (c i) (hf i)

theorem evalAt_sum_smul_of_mem {ι : Type} (S : Finset ι) (v : Place (AlgebraicClosure ℚ) F)
    (hv : v.IsRational) (c : ι → AlgebraicClosure ℚ) {f : ι → F}
    (hf : ∀ i, f i ∈ v.toValuationSubring) :
    v.evalAt (∑ i ∈ S, c i • f i) = ∑ i ∈ S, c i * v.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact (v.evalAt_algebraMap_eq 0 ▸ by rw [map_zero])
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalAt_add_of_mem v hv (smul_mem_of_mem v _ (hf a)) (sum_smul_mem S v c hf),
      evalAt_smul_of_mem v hv _ (hf a), ih]

end Eval

section Linear

theorem absLogHeight_linear_le {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty ι]
    (M : κ → ι → AlgebraicClosure ℚ) (x : ι → AlgebraicClosure ℚ) :
    absLogHeight (fun j => ∑ i, M j i * x i)
      ≤ Real.log (Fintype.card ι) + absLogHeight (fun q : κ × ι => M q.1 q.2) + absLogHeight x := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (Set.range x ∪ Set.range (fun q : κ × ι => M q.1 q.2)) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  have hxE : ∀ i, x i ∈ E' := fun i => IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
  have hME : ∀ q : κ × ι, M q.1 q.2 ∈ E' := fun q => IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨q, rfl⟩)
  have hyE : ∀ j, (∑ i, M j i * x i) ∈ E' := fun j => sum_mem fun i _ => mul_mem (hME (j, i)) (hxE i)
  rw [absLogHeight_eq_of_mem _ E' hyE, absLogHeight_eq_of_mem _ E' hME, absLogHeight_eq_of_mem x E' hxE]
  have hd : (0 : ℝ) < Module.finrank ℚ E' := by exact_mod_cast Module.finrank_pos
  have hfun : (fun j => (⟨∑ i, M j i * x i, hyE j⟩ : E'))
      = fun j => ∑ i, (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E')) (j, i) * (⟨x i, hxE i⟩ : E') := by
    funext j
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [MulMemClass.coe_mul]
  have key := Height.logHeight_linearMap_apply_le (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
    (fun i => (⟨x i, hxE i⟩ : E'))
  rw [NumberField.totalWeight_eq_finrank, Nat.card_eq_fintype_card] at key
  rw [hfun]
  have hlog : 0 ≤ Real.log (Fintype.card ι : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  calc (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun j => ∑ i,
          (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E')) (j, i) * (⟨x i, hxE i⟩ : E'))
      ≤ (Module.finrank ℚ E' : ℝ)⁻¹ * ((Module.finrank ℚ E' : ℝ) * Real.log (Fintype.card ι)
          + Height.logHeight (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
          + Height.logHeight (fun i => (⟨x i, hxE i⟩ : E'))) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hd.le)
    _ = Real.log (Fintype.card ι)
          + (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
          + (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hxE i⟩ : E')) := by
        field_simp

theorem absLogHeight_nonneg {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  haveI := finiteDimensional_adjoin_range x
  unfold absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

end Linear

section Orders

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem ord_pivot_eq {r : ℕ} (hr : 0 < r) (f : Fin r → F) (hf : ∀ i, f i ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hfD : ∀ i, f i ∈ riemannRochSpace D)
    (v : Place (AlgebraicClosure ℚ) F) (hex : ∃ i, v.ord (f i) + D v = 0) :
    v.ord (f (pivotIndex f v hr)) = -D v := by
  obtain ⟨i, hi⟩ := hex
  apply le_antisymm
  · have := ord_pivot_le hr f v i; linarith
  · have := (mem_riemannRochSpace_iff.mp (hfD _) v).resolve_left (hf (pivotIndex f v hr)); linarith

theorem exists_ord_add_eq_zero_of_span {a b : ℕ} (s : Fin a → F) (u : Fin b → F) (hu : ∀ j, u j ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace D)
    (huD : ∀ j, u j ∈ riemannRochSpace D)
    (v : Place (AlgebraicClosure ℚ) F) (hbpf : ∃ j, v.ord (u j) + D v = 0) :
    ∃ i, v.ord (s i) + D v = 0 := by
  classical
  by_contra hnone
  push Not at hnone

  have hsub : ∀ i, s i ∈ riemannRochSpace (D - Finsupp.single v 1) := by
    intro i
    rw [mem_riemannRochSpace_iff]
    intro w
    rcases eq_or_ne (s i) 0 with h0 | h0
    · exact Or.inl h0
    right
    have hsi : s i ∈ riemannRochSpace D := by rw [← hsD]; exact Submodule.subset_span ⟨i, rfl⟩
    have hge := (mem_riemannRochSpace_iff.mp hsi w).resolve_left h0
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs with hvw
    · subst hvw; have := hnone i; omega
    · rw [sub_zero]; exact hge
  have hle : Submodule.span (AlgebraicClosure ℚ) (Set.range s) ≤ riemannRochSpace (D - Finsupp.single v 1) := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hsub i
  obtain ⟨j, hj⟩ := hbpf
  have huj : u j ∈ riemannRochSpace (D - Finsupp.single v 1) := by
    apply hle; rw [hsD]; exact huD j
  have := (mem_riemannRochSpace_iff.mp huj v).resolve_left (hu j)
  rw [Finsupp.sub_apply, Finsupp.single_eq_same] at this
  omega

end Orders

section EasyLin

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {a b : ℕ}

theorem evalVec_eq_smul_linear (ha : 0 < a) (hb : 0 < b) (s : Fin a → F) (u : Fin b → F)
    (hs : ∀ i, s i ≠ 0) (hu : ∀ j, u j ≠ 0)
    (M : Fin b → Fin a → AlgebraicClosure ℚ) (hM : ∀ j, ∑ i, M j i • s i = u j)
    (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational)
    (hord : v.ord (s (pivotIndex s v ha)) = v.ord (u (pivotIndex u v hb))) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ evalVec u v = c • fun j => ∑ i, M j i * evalVec s v i := by
  set k := pivotIndex s v ha with hk
  set k' := pivotIndex u v hb with hk'
  have hrs : ∀ i, s i * (s k)⁻¹ ∈ v.toValuationSubring := fun i => ratio_pivot_mem ha s hs v i
  have hus : ∀ j, u j * (s k)⁻¹ = ∑ i, M j i • (s i * (s k)⁻¹) := by
    intro j
    rw [← hM j, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_assoc]
  have hus_mem : ∀ j, u j * (s k)⁻¹ ∈ v.toValuationSubring := fun j => by
    rw [hus j]; exact sum_smul_mem _ v _ hrs

  set w : F := s k * (u k')⁻¹ with hw
  have hw0 : w ≠ 0 := mul_ne_zero (hs k) (inv_ne_zero (hu k'))
  have hword : v.ord w = 0 := by rw [hw, v.ord_mul (hs k) (inv_ne_zero (hu k')), v.ord_inv]; omega
  have hwmem : w ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hw0 hword.ge
  have hwinv : w⁻¹ = u k' * (s k)⁻¹ := by rw [hw, mul_inv, inv_inv, mul_comm]
  have hwinv_mem : w⁻¹ ∈ v.toValuationSubring := by rw [hwinv]; exact hus_mem k'
  set c := v.evalAt w with hc
  have hcne : c ≠ 0 := by
    intro h0
    have h1 : v.evalAt (w * w⁻¹) = 1 := by rw [mul_inv_cancel₀ hw0, v.evalAt_one]
    rw [v.evalAt_mul_of_mem hv hwmem hwinv_mem, ← hc, h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨c, hcne, ?_⟩
  funext j
  rw [Pi.smul_apply, smul_eq_mul, evalVec_apply hb u v j, ← hk']
  have hsplit : u j * (u k')⁻¹ = (u j * (s k)⁻¹) * w := by
    rw [hw]; field_simp [hs k, hu k']
  rw [hsplit, v.evalAt_mul_of_mem hv (hus_mem j) hwmem, ← hc, hus j, evalAt_sum_smul_of_mem _ v hv _ hrs, mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [evalVec_apply ha s v i, ← hk]

theorem pointHt_le_of_linear (ha : 0 < a) (hb : 0 < b) (s : Fin a → F) (u : Fin b → F)
    (M : Fin b → Fin a → AlgebraicClosure ℚ) (v : Place (AlgebraicClosure ℚ) F)
    {c : AlgebraicClosure ℚ} (hc : c ≠ 0) (hev : evalVec u v = c • fun j => ∑ i, M j i * evalVec s v i) :
    pointHt u v ≤ Real.log (Fintype.card (Fin a)) + absLogHeight (fun q : Fin b × Fin a => M q.1 q.2) + pointHt s v := by
  show absLogHeight (evalVec u v) ≤ _ + _ + absLogHeight (evalVec s v)
  rw [hev, absLogHeight_smul _ hc]
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  exact absLogHeight_linear_le M (evalVec s v)

end EasyLin

section RRGeneric

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ne_zero_of_notMem {D : Divisor K F} {f : F} (hf : f ∉ riemannRochSpace D) : f ≠ 0 := by
  rintro rfl; exact hf (zero_mem _)

theorem ord_eq_of_mem_notMem {D : Divisor K F} {f : F} (w : Place K F)
    (hf : f ∈ riemannRochSpace D) (hf' : f ∉ riemannRochSpace (D - Finsupp.single w 1)) :
    w.ord f + D w = 0 := by
  classical
  have hf0 := ne_zero_of_notMem hf'
  have hge : -D w ≤ w.ord f := ((mem_riemannRochSpace_iff.mp hf) w).resolve_left hf0
  have hlt : w.ord f < -D w + 1 := by
    by_contra hge'
    push Not at hge'
    apply hf'
    rw [mem_riemannRochSpace_iff]
    intro v
    by_cases hv : v = w
    · subst hv; right
      rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl]; linarith
    · rcases (mem_riemannRochSpace_iff.mp hf) v with h | h
      · exact Or.inl h
      · right
        rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hv), sub_zero]; exact h
  omega

theorem exists_index_notMem_of_span_eq {ι : Type*} (x : ι → F) {D : Divisor K F}
    (hspan : Submodule.span K (Set.range x) = riemannRochSpace D) (w : Place K F)
    (h : ∃ f ∈ riemannRochSpace D, f ∉ riemannRochSpace (D - Finsupp.single w 1)) :
    ∃ i, x i ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  by_contra hall
  push Not at hall
  obtain ⟨f, hf, hf'⟩ := h
  apply hf'
  have hle : Submodule.span K (Set.range x) ≤ riemannRochSpace (D - Finsupp.single w 1) :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
  exact hle (hspan ▸ hf)

theorem mem_of_span_eq {ι : Type*} (x : ι → F) {D : Divisor K F}
    (hspan : Submodule.span K (Set.range x) = riemannRochSpace D) (i : ι) : x i ∈ riemannRochSpace D :=
  hspan ▸ Submodule.subset_span ⟨i, rfl⟩

theorem mul_mem_rr_add {A B : Divisor K F} {f g : F} (hf : f ∈ riemannRochSpace A)
    (hg : g ∈ riemannRochSpace B) : f * g ∈ riemannRochSpace (A + B) := by
  rw [mem_riemannRochSpace_iff] at hf hg ⊢
  intro w
  rcases eq_or_ne f 0 with rfl | hf0
  · left; rw [zero_mul]
  rcases eq_or_ne g 0 with rfl | hg0
  · left; rw [mul_zero]
  right
  rw [Place.ord_mul _ hf0 hg0, Finsupp.add_apply, neg_add]
  exact add_le_add ((hf w).resolve_left hf0) ((hg w).resolve_left hg0)

theorem exists_mem_notMem_of_finrank_ne (D : Divisor K F) (w : Place K F)
    (h : Module.finrank K (riemannRochSpace D) ≠
      Module.finrank K (riemannRochSpace (D - Finsupp.single w 1))) :
    ∃ f ∈ riemannRochSpace D, f ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  classical
  have hle : riemannRochSpace (D - Finsupp.single w 1) ≤ riemannRochSpace D := by
    refine lSpace_mono (Finsupp.le_def.mpr fun v => ?_)
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hne : riemannRochSpace (D - Finsupp.single w 1) ≠ riemannRochSpace D := by
    intro heq; exact h (by rw [heq])
  obtain ⟨f, hf, hnf⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  exact ⟨f, hf, hnf⟩

theorem exists_family_span_eq (D : Divisor K F) [FiniteDimensional K (riemannRochSpace D)] :
    ∃ (c : ℕ) (t : Fin c → F), (∀ i, t i ≠ 0) ∧ Submodule.span K (Set.range t) = riemannRochSpace D ∧
      c = Module.finrank K (riemannRochSpace D) := by
  let bs := Module.finBasis K (riemannRochSpace D)
  refine ⟨_, fun i => (bs i : F), fun i => ?_, ?_, rfl⟩
  · intro h0
    apply bs.ne_zero i
    exact Subtype.ext h0
  · have hr : Set.range (fun i => (bs i : F)) = (riemannRochSpace D).subtype '' Set.range bs := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, bs.span_eq, Submodule.map_top, Submodule.range_subtype]

end RRGeneric

section Families

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

def psz (a : ℕ) : ℕ → ℕ
  | 0 => a
  | k + 1 => psz a k * a

theorem psz_pos {a : ℕ} (ha : 0 < a) : ∀ k, 0 < psz a k
  | 0 => ha
  | k + 1 => Nat.mul_pos (psz_pos ha k) ha

def mulFam {a b : ℕ} (s : Fin a → F) (t : Fin b → F) : Fin (a * b) → F :=
  fun k => s (finProdFinEquiv.symm k).1 * t (finProdFinEquiv.symm k).2

def powFam {a : ℕ} (s : Fin a → F) : (k : ℕ) → Fin (psz a k) → F
  | 0 => s
  | k + 1 => mulFam (powFam s k) s

omit [Algebra (AlgebraicClosure ℚ) F] in
theorem mulFam_ne_zero {a b : ℕ} {s : Fin a → F} {t : Fin b → F} (hs : ∀ i, s i ≠ 0) (ht : ∀ j, t j ≠ 0) :
    ∀ k, mulFam s t k ≠ 0 := fun _ => mul_ne_zero (hs _) (ht _)

theorem powFam_ne_zero {a : ℕ} {s : Fin a → F} (hs : ∀ i, s i ≠ 0) : ∀ k idx, powFam s k idx ≠ 0
  | 0 => hs
  | k + 1 => mulFam_ne_zero (powFam_ne_zero hs k) hs

theorem mulFam_mem {a b : ℕ} {s : Fin a → F} {t : Fin b → F}
    {A B : Divisor (AlgebraicClosure ℚ) F} (hs : ∀ i, s i ∈ riemannRochSpace A) (ht : ∀ j, t j ∈ riemannRochSpace B) :
    ∀ k, mulFam s t k ∈ riemannRochSpace (A + B) := fun _ => mul_mem_rr_add (hs _) (ht _)

theorem powFam_mem {a : ℕ} {s : Fin a → F} {D : Divisor (AlgebraicClosure ℚ) F}
    (hs : ∀ i, s i ∈ riemannRochSpace D) : ∀ k idx, powFam s k idx ∈ riemannRochSpace ((k + 1) • D)
  | 0 => by simpa [powFam, psz] using hs
  | k + 1 => by
    intro idx
    have := mulFam_mem (powFam_mem hs k) hs idx
    rw [succ_nsmul]
    exact this

theorem mulFam_bpf {a b : ℕ} {s : Fin a → F} {t : Fin b → F} (hs0 : ∀ i, s i ≠ 0) (ht0 : ∀ j, t j ≠ 0)
    {A B : Divisor (AlgebraicClosure ℚ) F}
    (hs : ∀ w : Place (AlgebraicClosure ℚ) F, ∃ i, w.ord (s i) + A w = 0)
    (ht : ∀ w : Place (AlgebraicClosure ℚ) F, ∃ j, w.ord (t j) + B w = 0) :
    ∀ w : Place (AlgebraicClosure ℚ) F, ∃ k, w.ord (mulFam s t k) + (A + B) w = 0 := by
  intro w
  obtain ⟨i, hi⟩ := hs w
  obtain ⟨j, hj⟩ := ht w
  refine ⟨finProdFinEquiv (i, j), ?_⟩
  simp only [mulFam, Equiv.symm_apply_apply]
  rw [Place.ord_mul _ (hs0 i) (ht0 j), Finsupp.add_apply]
  linarith

theorem powFam_bpf {a : ℕ} {s : Fin a → F} (hs0 : ∀ i, s i ≠ 0) {D : Divisor (AlgebraicClosure ℚ) F}
    (hs : ∀ w : Place (AlgebraicClosure ℚ) F, ∃ i, w.ord (s i) + D w = 0) :
    ∀ (k) (w : Place (AlgebraicClosure ℚ) F), ∃ idx, w.ord (powFam s k idx) + ((k + 1) • D) w = 0
  | 0 => by simpa [powFam, psz] using hs
  | k + 1 => by
    intro w
    have := mulFam_bpf (powFam_ne_zero hs0 k) hs0 (powFam_bpf hs0 hs k) hs w
    rw [succ_nsmul]
    exact this

theorem pointHt_powFam {a : ℕ} (ha : 0 < a) (s : Fin a → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) :
    ∀ k, pointHt (powFam s k) v = (k + 1) * pointHt s v
  | 0 => by
    have h0 : pointHt (powFam s 0) v = pointHt s v := rfl
    rw [h0]
    push_cast
    ring
  | k + 1 => by
    have h := pointHt_mul_eq_add (psz_pos ha k) ha (powFam s k) s (powFam_ne_zero hs k) hs v hv
    have h' : pointHt (powFam s (k + 1)) v = pointHt (powFam s k) v + pointHt s v := h
    rw [h', pointHt_powFam ha s hs v hv k]
    push_cast
    ring

theorem absLogHeight_nonneg' {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  haveI := finiteDimensional_adjoin_range x
  unfold absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

theorem pointHt_nonneg {r : ℕ} (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) : 0 ≤ pointHt s v :=
  absLogHeight_nonneg' _

end Families

section Bar

variable (N : ℕ) [NeZero N]

theorem ell_eq_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 1 ≤ Divisor.degree D) :
    (ell D : ℤ) = Divisor.degree D + 1 - (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI hCD : HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) :=
    hasCanonicalDivisor_modularFunctionFieldBar N
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := essFiniteType_modularFunctionFieldBar N
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  haveI hDCG : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hRR : FunctionFieldRiemannRoch (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    functionFieldRiemannRoch_modularFunctionFieldBar N
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)])
  have hdegK := degree_canonicalDivisorOf_modularFunctionFieldBar N hω
  have hgen := genus_eq_genusFF_modularFunctionFieldBar N
  have h1 := hRR hω D
  have hneg : Divisor.degree (canonicalDivisorOf hω - D) < 0 := by
    rw [map_sub, hdegK, hgen]; linarith
  have hell : ell (canonicalDivisorOf hω - D) = 0 := by
    show Module.finrank _ (LSpace _) = 0
    rw [AlgebraicCurve.lSpace_eq_bot_of_degree_neg hneg, finrank_bot]
  rw [hell, hgen] at h1
  push_cast at h1
  linarith

scoped instance finiteDimensional_lSpace_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace D) := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : FiniteDimensional (AlgebraicClosure ℚ) (LSpace (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase _ _
      (constantsAreBase_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N)
  exact finiteDimensional_lSpace D

theorem isRational_bar (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.IsRational :=
  (Place.isRational_iff_deg_eq_one v).mpr (deg_eq_one_modularFunctionFieldBar N v)

theorem exists_mem_notMem_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ f ∈ riemannRochSpace D, f ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  apply exists_mem_notMem_of_finrank_ne
  have e1 := ell_eq_bar N D (by omega)
  have hdeg' : Divisor.degree (D - Finsupp.single w 1) = Divisor.degree D - 1 := by
    rw [map_sub, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N w]; push_cast; ring
  have e2 := ell_eq_bar N (D - Finsupp.single w 1) (by rw [hdeg']; omega)
  rw [hdeg'] at e2
  intro heq
  have : (ell D : ℤ) = (ell (D - Finsupp.single w 1) : ℤ) := by
    unfold ell LSpace; exact_mod_cast heq
  omega

theorem bpf_of_span_eq {ι : Type*} (x : ι → modularFunctionFieldBar N)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hspan : Submodule.span (AlgebraicClosure ℚ) (Set.range x) = riemannRochSpace D)
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ i, w.ord (x i) + D w = 0 := by
  intro w
  obtain ⟨i, hi⟩ := exists_index_notMem_of_span_eq x hspan w (exists_mem_notMem_bar N D hD w)
  exact ⟨i, ord_eq_of_mem_notMem w (mem_of_span_eq x hspan i) hi⟩

theorem pos_of_span_eq {a : ℕ} (x : Fin a → modularFunctionFieldBar N)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hspan : Submodule.span (AlgebraicClosure ℚ) (Set.range x) = riemannRochSpace D)
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D) : 0 < a := by
  by_contra ha
  have ha0 : a = 0 := by omega
  subst ha0
  obtain ⟨f, hf, hf'⟩ := exists_mem_notMem_bar N D hD (cuspInftyBar N)
  have : f ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range x) := hspan ▸ hf
  rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
  exact ne_zero_of_notMem hf' this

end Bar

end P2MHm
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_pointHt_le_mul_baseHt.P2MHm"

namespace P2MHm

section Chord

variable {N : ℕ} [NeZero N]

theorem degree_embDivisor : (embDivisor N).degree = (embDegree N : ℤ) := by
  rw [ModularCurve.embDivisor, map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N]
  simp

theorem embDivisor_apply_of_ne {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hw : w ≠ cuspInftyBar N) :
    embDivisor N w = 0 := by
  classical
  rw [ModularCurve.embDivisor, Finsupp.smul_apply, Finsupp.single_apply, if_neg (fun h => hw h.symm), smul_zero]

theorem embDivisor_apply_self : embDivisor N (cuspInftyBar N) = (embDegree N : ℤ) := by
  rw [ModularCurve.embDivisor, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem two_g_le_degree_embDivisor :
    2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ (embDivisor N).degree := by
  rw [degree_embDivisor, ModularCurve.embDegree]; push_cast; omega

theorem ord_nonneg_of_mem {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] (v : Place (AlgebraicClosure ℚ) F)
    {f : F} (hf : f ≠ 0) (h : f ∈ v.toValuationSubring) : 0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem h)).resolve_left hf

theorem ord_pos_of_evalAt_eq_zero {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] (v : Place (AlgebraicClosure ℚ) F)
    (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : f ∈ v.toValuationSubring) (h0 : v.evalAt f = 0) : 0 < v.ord f := by
  rcases (ord_nonneg_of_mem v hf h).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd h0 (v.evalAt_ne_zero_of_ord_eq_zero hv hf heq.symm)

theorem sum_ite_smul {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V] {n : ℕ} (j : Fin n) (c : K)
    (v : Fin n → V) : ∑ i, (if i = j then c else 0) • v i = c • v j := by
  rw [Finset.sum_eq_single j (fun i _ hi => by rw [if_neg hi, zero_smul]) (fun h => absurd (Finset.mem_univ j) h),
    if_pos rfl]

variable {r : ℕ}

theorem emb_ne_zero {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (i : Fin r) : s i ≠ 0 := hs.1.ne_zero i

theorem emb_mem {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (i : Fin r) : s i ∈ riemannRochSpace (embDivisor N) :=
  mem_of_span_eq s hs.2 i

theorem emb_bpf {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ i, w.ord (s i) + embDivisor N w = 0 :=
  bpf_of_span_eq N s hs.2 two_g_le_degree_embDivisor

theorem emb_regular {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
    {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hw : w ≠ cuspInftyBar N) (i : Fin r) :
    s i ∈ w.toValuationSubring := by
  have h := (mem_riemannRochSpace_iff.mp (emb_mem hs i) w).resolve_left (emb_ne_zero hs i)
  rw [embDivisor_apply_of_ne hw, neg_zero] at h
  exact w.mem_toValuationSubring_of_ord_nonneg_alt (emb_ne_zero hs i) h

theorem ord_emb_pivot (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    w.ord (s (pivotIndex s w hr)) = -embDivisor N w :=
  ord_pivot_eq hr s (emb_ne_zero hs) (embDivisor N) (emb_mem hs) w (emb_bpf hs w)

variable (N)

def projFam (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) : Fin r → modularFunctionFieldBar N :=
  fun j => if j = pivotIndex s (cuspInftyBar N) hr then 1
    else s j - evalVec s (cuspInftyBar N) j • s (pivotIndex s (cuspInftyBar N) hr)

def projOrd (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) : ℕ :=
  (-(cuspInftyBar N).ord (projFam N hr s (pivotIndex (projFam N hr s) (cuspInftyBar N) hr))).toNat

def projDiv (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  (projOrd N hr s : ℤ) • Finsupp.single (cuspInftyBar N) 1

variable {N}

theorem projFam_pivot (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) :
    projFam N hr s (pivotIndex s (cuspInftyBar N) hr) = 1 := by
  simp [projFam]

theorem projFam_of_ne (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) {j : Fin r}
    (hj : j ≠ pivotIndex s (cuspInftyBar N) hr) :
    projFam N hr s j = s j - evalVec s (cuspInftyBar N) j • s (pivotIndex s (cuspInftyBar N) hr) := by
  simp [projFam, hj]

theorem projFam_ne_zero (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (j : Fin r) :
    projFam N hr s j ≠ 0 := by
  set i₀ := pivotIndex s (cuspInftyBar N) hr with hi₀
  by_cases hj : j = i₀
  · rw [hj, hi₀, projFam_pivot hr s]; exact one_ne_zero
  rw [projFam_of_ne hr s (by rwa [← hi₀]), ← hi₀]
  intro h0
  have heq : s j = evalVec s (cuspInftyBar N) j • s i₀ := sub_eq_zero.mp h0
  have hmem : s j ∈ Submodule.span (AlgebraicClosure ℚ) (s '' {i₀}) := by
    rw [Set.image_singleton, heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  exact hs.1.notMem_span_image (s := {i₀}) (by simpa using hj) hmem

theorem projFam_regular (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
    {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hw : w ≠ cuspInftyBar N) (j : Fin r) :
    projFam N hr s j ∈ w.toValuationSubring := by
  by_cases hj : j = pivotIndex s (cuspInftyBar N) hr
  · rw [hj, projFam_pivot hr s]; exact one_mem _
  · rw [projFam_of_ne hr s hj]
    exact sub_mem (emb_regular hs hw j) (smul_mem_of_mem w _ (emb_regular hs hw _))

theorem ord_projFam_ge (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (j : Fin r) :
    -(2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ)) ≤ (cuspInftyBar N).ord (projFam N hr s j) := by
  set v := cuspInftyBar N with hv
  set i₀ := pivotIndex s v hr with hi₀
  have hrat := isRational_bar N v
  by_cases hj : j = i₀
  · rw [hj, hi₀, projFam_pivot hr s, Place.ord_one]; omega
  rw [projFam_of_ne hr s hj]
  set a := evalVec s v j with ha
  set q : modularFunctionFieldBar N := s j * (s i₀)⁻¹ with hq
  have hqmem : q ∈ v.toValuationSubring := ratio_pivot_mem hr s (emb_ne_zero hs) v j
  have haq : a = v.evalAt q := by rw [ha, evalVec_apply hr s v j]
  set d : modularFunctionFieldBar N := q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a with hd
  have hcmem : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ v.toValuationSubring := v.algebraMap_mem' a
  have hdmem : d ∈ v.toValuationSubring := sub_mem hqmem hcmem
  have hd0 : v.evalAt d = 0 := by
    have hsum : d + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a = q := by rw [hd]; ring
    have := evalAt_add_of_mem v hrat hdmem hcmem
    rw [hsum, v.evalAt_algebraMap_eq, ← haq] at this
    linear_combination -this
  have hprod : d * s i₀ = s j - a • s i₀ := by
    rw [hd, hq, sub_mul, mul_assoc, inv_mul_cancel₀ (emb_ne_zero hs i₀), mul_one, Algebra.smul_def]
  have hne : s j - a • s i₀ ≠ 0 := by
    have := projFam_ne_zero hr hs j
    rwa [projFam_of_ne hr s hj] at this
  have hdne : d ≠ 0 := by
    intro h0; apply hne; rw [← hprod, h0, zero_mul]
  have hdpos : 0 < v.ord d := ord_pos_of_evalAt_eq_zero v hrat hdne hdmem hd0
  have hpiv : v.ord (s i₀) = -embDivisor N v := ord_emb_pivot hr hs v
  have hEv : embDivisor N v = (embDegree N : ℤ) := by rw [hv]; exact embDivisor_apply_self
  rw [hEv, ModularCurve.embDegree] at hpiv
  rw [← hprod, v.ord_mul hdne (emb_ne_zero hs i₀)]
  push_cast at hpiv
  omega

theorem projOrd_eq (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) :
    (projOrd N hr s : ℤ) = -(cuspInftyBar N).ord (projFam N hr s (pivotIndex (projFam N hr s) (cuspInftyBar N) hr)) := by
  rw [projOrd]
  apply Int.toNat_of_nonneg
  have := ord_pivot_le hr (projFam N hr s) (cuspInftyBar N) (pivotIndex s (cuspInftyBar N) hr)
  rw [projFam_pivot hr s, Place.ord_one] at this
  omega

theorem projOrd_le (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) :
    (projOrd N hr s : ℤ) ≤ 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by
  rw [projOrd_eq hr hs]
  have := ord_projFam_ge hr hs (pivotIndex (projFam N hr s) (cuspInftyBar N) hr)
  omega

theorem projDiv_apply_self (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) :
    projDiv N hr s (cuspInftyBar N) = (projOrd N hr s : ℤ) := by
  rw [projDiv, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem projDiv_apply_of_ne (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hw : w ≠ cuspInftyBar N) :
    projDiv N hr s w = 0 := by
  classical
  rw [projDiv, Finsupp.smul_apply, Finsupp.single_apply, if_neg (fun h => hw h.symm), smul_zero]

theorem projFam_mem (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (j : Fin r) :
    projFam N hr s j ∈ riemannRochSpace (projDiv N hr s) := by
  rw [mem_riemannRochSpace_iff]
  intro w
  right
  by_cases hw : w = cuspInftyBar N
  · rw [hw, projDiv_apply_self, projOrd_eq hr hs, neg_neg]
    exact ord_pivot_le hr _ _ j
  · rw [projDiv_apply_of_ne hr s hw, neg_zero]
    exact ord_nonneg_of_mem w (projFam_ne_zero hr hs j) (projFam_regular hr hs hw j)

theorem projFam_bpf (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ j, w.ord (projFam N hr s j) + projDiv N hr s w = 0 := by
  intro w
  by_cases hw : w = cuspInftyBar N
  · refine ⟨pivotIndex (projFam N hr s) (cuspInftyBar N) hr, ?_⟩
    rw [hw, projDiv_apply_self, projOrd_eq hr hs]; ring
  · refine ⟨pivotIndex s (cuspInftyBar N) hr, ?_⟩
    rw [projFam_pivot hr s, projDiv_apply_of_ne hr s hw, Place.ord_one]; ring

theorem ord_projFam_pivot (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
    {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hw : w ≠ cuspInftyBar N) :
    w.ord (projFam N hr s (pivotIndex (projFam N hr s) w hr)) = 0 := by
  apply le_antisymm
  · have := ord_pivot_le hr (projFam N hr s) w (pivotIndex s (cuspInftyBar N) hr)
    rwa [projFam_pivot hr s, Place.ord_one] at this
  · exact ord_nonneg_of_mem w (projFam_ne_zero hr hs _) (projFam_regular hr hs hw _)

theorem projFam_height_le (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) :
    ∃ C : ℝ, ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (embDegree N : ℝ) * pointHt (projFam N hr s) v
        ≤ 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) * pointHt s v + C := by
  classical
  set g : ℕ := genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) with hg
  set e : ℕ := projOrd N hr s with he
  set u := projFam N hr s with hu
  have hu0 : ∀ j, u j ≠ 0 := projFam_ne_zero hr hs
  have hs0 : ∀ i, s i ≠ 0 := emb_ne_zero hs
  have hembR : (embDegree N : ℝ) = 2 * (g : ℝ) + 1 := by rw [ModularCurve.embDegree, ← hg]; push_cast; ring
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  ·
    have hCB : ConstantsAreBase (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      constantsAreBase_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N
    have hD0 : projDiv N hr s = 0 := by rw [projDiv, ← he, he0]; simp
    have hconst : ∀ j, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ u j = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c := by
      intro j
      have hmem : u j ∈ LSpace (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := by
        have := projFam_mem hr hs j
        rwa [hD0] at this
      rw [hCB] at hmem
      obtain ⟨c, hc⟩ := hmem
      refine ⟨c, ?_, ?_⟩
      · rintro rfl; apply hu0 j; rw [← hc]; simp
      · rw [← hc]; rfl
    choose c hc0 hc using hconst
    refine ⟨(embDegree N : ℝ) * absLogHeight c, fun v => ?_⟩
    have hev : evalVec u v = (c (pivotIndex u v hr))⁻¹ • c := by
      funext j
      rw [evalVec_apply hr u v j, Pi.smul_apply, smul_eq_mul, hc j, hc (pivotIndex u v hr), ← map_inv₀, ← map_mul,
        Place.evalAt_algebraMap_eq]
      ring
    have hpt : pointHt u v = absLogHeight c := by
      rw [pointHt, hev, absLogHeight_smul _ (inv_ne_zero (hc0 _))]
    rw [hpt]
    nlinarith [pointHt_nonneg s v, (Nat.cast_nonneg g : (0 : ℝ) ≤ g)]
  ·
    set Big : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := e • embDivisor N with hBig
    have hBigdeg : Big.degree = (e : ℤ) * (embDegree N : ℤ) := by
      rw [hBig, map_nsmul, degree_embDivisor, nsmul_eq_mul]
    have hBigdeg' : 2 * (g : ℤ) + 1 ≤ Big.degree := by
      rw [hBigdeg, ModularCurve.embDegree, ← hg]; push_cast
      have : (1 : ℤ) ≤ e := by exact_mod_cast hepos
      nlinarith
    have hBigA : (2 * g + 1) • projDiv N hr s = Big := by
      rw [hBig, projDiv, ← he, ModularCurve.embDivisor, ModularCurve.embDegree, ← hg]
      ext w
      simp only [Finsupp.smul_apply, smul_eq_mul, nsmul_eq_mul, Finsupp.single_apply]
      split_ifs <;> push_cast <;> ring
    obtain ⟨cB, wB, hwB0, hwBspan, -⟩ := exists_family_span_eq (K := AlgebraicClosure ℚ) Big

    set U := powFam u (2 * g) with hU
    have hU0 : ∀ idx, U idx ≠ 0 := powFam_ne_zero hu0 (2 * g)
    have hUmem : ∀ idx, U idx ∈ riemannRochSpace Big := by
      intro idx; rw [← hBigA]; exact powFam_mem (projFam_mem hr hs) (2 * g) idx
    have hUbpf : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ idx, w.ord (U idx) + Big w = 0 := by
      intro w; rw [← hBigA]; exact powFam_bpf hu0 (projFam_bpf hr hs) (2 * g) w

    set S := powFam s (e - 1) with hS
    have he1 : e - 1 + 1 = e := Nat.sub_add_cancel hepos
    have hS0 : ∀ idx, S idx ≠ 0 := powFam_ne_zero hs0 (e - 1)
    have hSmem : ∀ idx, S idx ∈ riemannRochSpace Big := by
      intro idx
      have := powFam_mem (emb_mem hs) (e - 1) idx
      rwa [he1] at this
    have hSbpf : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ idx, w.ord (S idx) + Big w = 0 := by
      intro w
      have := powFam_bpf hs0 (emb_bpf hs) (e - 1) w
      rwa [he1] at this
    obtain ⟨C₁, hC₁⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero N
      wB U hwB0 hU0 Big hBigdeg' hwBspan hUmem hUbpf
    obtain ⟨C₂, hC₂⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero N
      wB S hwB0 hS0 Big hBigdeg' hwBspan hSmem hSbpf
    refine ⟨C₁ + C₂, fun v => ?_⟩
    have hv := isRational_bar N v
    have h1 := hC₁ v
    have h2 := hC₂ v
    have hUeq : pointHt U v = (2 * g + 1 : ℝ) * pointHt u v := by
      rw [hU]; have := pointHt_powFam hr u hu0 v hv (2 * g); push_cast at this ⊢; linarith
    have hSeq : pointHt S v = (e : ℝ) * pointHt s v := by
      rw [hS]; have := pointHt_powFam hr s hs0 v hv (e - 1)
      rw [this]; congr 1; exact_mod_cast he1
    rw [abs_le] at h1 h2
    rw [hUeq] at h1
    rw [hSeq] at h2
    have hele : (e : ℝ) ≤ 2 * g := by
      have := projOrd_le hr hs; rw [← he, ← hg] at this; exact_mod_cast this
    have hpt := pointHt_nonneg s v
    rw [hembR]
    nlinarith [h1.1, h1.2, h2.1, h2.2, mul_le_mul_of_nonneg_right hele hpt]

theorem absLogHeight_chordVec_le (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) :
    ∃ C : ℝ, ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v ≠ cuspInftyBar N →
      absLogHeight (chordVec s v (cuspInftyBar N)) ≤ pointHt (projFam N hr s) v + C := by
  classical
  set i₀ := pivotIndex s (cuspInftyBar N) hr with hi₀
  set a := evalVec s (cuspInftyBar N) with ha
  set u := projFam N hr s with hu
  have hs0 : ∀ i, s i ≠ 0 := emb_ne_zero hs
  have hu0 : ∀ j, u j ≠ 0 := projFam_ne_zero hr hs
  have ha0 : a i₀ = 1 := by rw [ha, hi₀]; exact evalVec_pivot hr s hs0 _
  have hupiv : u i₀ = 1 := by rw [hu, hi₀]; exact projFam_pivot hr s
  have huj : ∀ j, j ≠ i₀ → u j = s j - a j • s i₀ := fun j hj => by
    rw [hu, ha, hi₀]; exact projFam_of_ne hr s (by rwa [← hi₀])

  have h1mem : (1 : modularFunctionFieldBar N) ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by
    rw [hs.2, mem_riemannRochSpace_iff]; intro w; right; rw [Place.ord_one]
    by_cases hw : w = cuspInftyBar N
    · rw [hw, embDivisor_apply_self]; simp
    · rw [embDivisor_apply_of_ne hw]; simp
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp h1mem
  let M : Fin r → Fin r → AlgebraicClosure ℚ := fun j i =>
    if j = i₀ then β i else ((if i = j then 1 else 0) - (if i = i₀ then a j else 0))
  have hM : ∀ j, ∑ i, M j i • s i = u j := by
    intro j
    by_cases hj : j = i₀
    · rw [hj, hupiv, ← hβ]
      exact Finset.sum_congr rfl fun i _ => by simp [M]
    · rw [huj j hj]
      have : ∀ i, M j i • s i = (if i = j then (1 : AlgebraicClosure ℚ) else 0) • s i - (if i = i₀ then a j else 0) • s i := by
        intro i; simp only [M, if_neg hj, sub_smul]
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib, sum_ite_smul, sum_ite_smul, one_smul]

  let T : (Fin r × Fin r) → Fin r → AlgebraicClosure ℚ := fun p k =>
    if k = i₀ then 0 else ((if k = p.1 then a p.2 else 0) - (if k = p.2 then a p.1 else 0))
  have hT : ∀ (p : Fin r × Fin r) (y : Fin r → AlgebraicClosure ℚ),
      ∑ k, T p k * y k = (if p.1 = i₀ then 0 else a p.2 * y p.1) - (if p.2 = i₀ then 0 else a p.1 * y p.2) := by
    intro p y
    have : ∀ k, T p k * y k = (if k = p.1 then (if k = i₀ then 0 else a p.2 * y k) else 0)
        - (if k = p.2 then (if k = i₀ then 0 else a p.1 * y k) else 0) := by
      intro k; simp only [T]; split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  refine ⟨Real.log (Fintype.card (Fin r)) + absLogHeight (fun q : (Fin r × Fin r) × Fin r => T q.1 q.2), ?_⟩
  intro v hv
  have hrat := isRational_bar N v
  have hord : v.ord (s (pivotIndex s v hr)) = v.ord (u (pivotIndex u v hr)) := by
    rw [ord_emb_pivot hr hs v, embDivisor_apply_of_ne hv, neg_zero, hu, ord_projFam_pivot hr hs hv]
  obtain ⟨c, hc0, hev⟩ := evalVec_eq_smul_linear hr hr s u hs0 hu0 M hM v hrat hord
  set e := evalVec s v with he
  have hf : ∀ k, k ≠ i₀ → evalVec u v k = c * (e k - a k * e i₀) := by
    intro k hk
    have := congrFun hev k
    rw [this, Pi.smul_apply, smul_eq_mul]
    congr 1
    have : ∀ i, M k i * e i = (if i = k then e i else 0) - (if i = i₀ then a k * e i else 0) := by
      intro i; simp only [M, if_neg hk]; split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hchord : chordVec s v (cuspInftyBar N) = c⁻¹ • fun p => ∑ k, T p k * evalVec u v k := by
    funext p
    obtain ⟨i, j⟩ := p
    rw [Pi.smul_apply, smul_eq_mul, hT]
    simp only [chordVec, ← he, ← ha]
    by_cases hi : i = i₀ <;> by_cases hj : j = i₀
    · rw [if_pos hi, if_pos hj, hi, hj]; ring
    · rw [if_pos hi, if_neg hj, hf j hj, hi, ha0]; field_simp; ring
    · rw [if_neg hi, if_pos hj, hf i hi, hj, ha0]; field_simp; ring
    · rw [if_neg hi, if_neg hj, hf i hi, hf j hj]; field_simp; ring
  rw [hchord, absLogHeight_smul _ (inv_ne_zero hc0)]
  have := absLogHeight_linear_le T (evalVec u v)
  rw [pointHt]
  linarith

end Chord
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_pointHt_le_mul_baseHt.P2MHm"

end P2MHm
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_pointHt_le_mul_baseHt.P2MHm"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_pointHt_le_mul_baseHt.P2MHm"

set_option synthInstance.maxHeartbeats 1600000 in
open AlgebraicCurve ModularCurve P2MHm in
theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ C : ℝ, ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v ≠ cuspInftyBar N →
      pointHt s v ≤ (embDegree N : ℝ) * baseHt s (cuspInftyBar N) v + C := by
  have hr : 0 < r := pos_of_span_eq N s hs.2 two_g_le_degree_embDivisor
  obtain ⟨C₁, hC₁⟩ := projFam_height_le hr hs
  obtain ⟨C₂, hC₂⟩ := absLogHeight_chordVec_le hr hs
  have hembR : (embDegree N : ℝ) = 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) + 1 := by
    rw [ModularCurve.embDegree]; push_cast; ring
  refine ⟨C₁ + (embDegree N : ℝ) * C₂, fun v hv => ?_⟩
  have h1 := hC₁ v
  have h2 := hC₂ v hv
  have hb : baseHt s (cuspInftyBar N) v = pointHt s v + pointHt s (cuspInftyBar N) - absLogHeight (chordVec s v (cuspInftyBar N)) := by
    rw [baseHt, if_neg hv, pairHt]
  rw [hb, hembR]
  rw [hembR] at h1
  have hp0 := pointHt_nonneg s (cuspInftyBar N)
  have hg0 : (0 : ℝ) ≤ (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) := Nat.cast_nonneg _
  nlinarith [h1, h2, hp0, hg0, mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) + 1)]

end S_ModularCurve_JZero_exists_pointHt_le_mul_baseHt
end P2MW
export P2MW.S_ModularCurve_JZero_exists_pointHt_le_mul_baseHt (solution)
