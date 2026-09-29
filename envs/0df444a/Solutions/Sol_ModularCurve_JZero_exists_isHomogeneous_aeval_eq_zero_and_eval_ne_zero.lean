-- Prove2me | solution 1 for ModularCurve.JZero.exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d337c933-28d7-58d9-b752-a6e75c1550c7

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
import Theorems.Thm_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_mul_add_of_degree_eq
import Theorems.Thm_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_self
import Theorems.Thm_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_eq
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero
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

namespace P2MS4

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
  | 0 => by simp at hs ⊢; exact hs
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
  | 0 => by simp at hs ⊢; exact hs
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

end P2MS4
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero.P2MS4"

namespace P2MS4

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

end Chord
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero.P2MS4"

end P2MS4
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero.P2MS4"

namespace P2MS4

section ProjAt

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

def altIdx (hr : 0 < r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F) : Fin r :=
  ⟨((pivotIndex s Q hr : ℕ) + 1) % r, Nat.mod_lt _ hr⟩

def jdx (hr : 0 < r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F) (j : Fin r) : Fin r :=
  if j = pivotIndex s Q hr then altIdx hr s Q else j

def projAt (hr : 0 < r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F) : Fin r → F :=
  fun j => s (jdx hr s Q j) - evalVec s Q (jdx hr s Q j) • s (pivotIndex s Q hr)

def projMat (hr : 0 < r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F) :
    Fin r → Fin r → AlgebraicClosure ℚ :=
  fun j i => (if i = jdx hr s Q j then 1 else 0)
    - (if i = pivotIndex s Q hr then evalVec s Q (jdx hr s Q j) else 0)

theorem altIdx_ne (hr : 0 < r) (h2 : 2 ≤ r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F) :
    altIdx hr s Q ≠ pivotIndex s Q hr := by
  intro h
  have hv := congrArg Fin.val h
  simp only [altIdx] at hv
  set p : ℕ := (pivotIndex s Q hr : ℕ) with hp
  have hpr : p < r := (pivotIndex s Q hr).isLt
  rcases Nat.lt_or_ge (p + 1) r with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have : p + 1 = r := by omega
    rw [this, Nat.mod_self] at hv; omega

theorem jdx_ne (hr : 0 < r) (h2 : 2 ≤ r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    jdx hr s Q j ≠ pivotIndex s Q hr := by
  unfold jdx
  split_ifs with h
  · exact altIdx_ne hr h2 s Q
  · exact h

theorem jdx_of_ne (hr : 0 < r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F) {j : Fin r}
    (hj : j ≠ pivotIndex s Q hr) : jdx hr s Q j = j := by
  unfold jdx; rw [if_neg hj]

theorem projAt_apply (hr : 0 < r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    projAt hr s Q j = s (jdx hr s Q j) - evalVec s Q (jdx hr s Q j) • s (pivotIndex s Q hr) := rfl

theorem sum_ite_smul' {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V] {n : ℕ} (j : Fin n) (c : K)
    (v : Fin n → V) : ∑ i, (if i = j then c else 0) • v i = c • v j := by
  rw [Finset.sum_eq_single j (fun i _ hi => by rw [if_neg hi, zero_smul]) (fun h => absurd (Finset.mem_univ j) h),
    if_pos rfl]

theorem projMat_spec (hr : 0 < r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    ∑ i, projMat hr s Q j i • s i = projAt hr s Q j := by
  have : ∀ i, projMat hr s Q j i • s i
      = (if i = jdx hr s Q j then (1 : AlgebraicClosure ℚ) else 0) • s i
        - (if i = pivotIndex s Q hr then evalVec s Q (jdx hr s Q j) else 0) • s i := by
    intro i; simp only [projMat, sub_smul]
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib, sum_ite_smul', sum_ite_smul', one_smul,
    projAt_apply]

theorem projMat_mulVec (hr : 0 < r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F)
    (x : Fin r → AlgebraicClosure ℚ) (j : Fin r) :
    ∑ i, projMat hr s Q j i * x i
      = x (jdx hr s Q j) - evalVec s Q (jdx hr s Q j) * x (pivotIndex s Q hr) := by
  have : ∀ i, projMat hr s Q j i * x i
      = (if i = jdx hr s Q j then x i else 0)
        - (if i = pivotIndex s Q hr then evalVec s Q (jdx hr s Q j) * x i else 0) := by
    intro i; simp only [projMat]; split_ifs <;> ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable (hr : 0 < r) {s : Fin r → F} (hs0 : ∀ i, s i ≠ 0) (hli : LinearIndependent (AlgebraicClosure ℚ) s)

include hs0 in
theorem evalVec_pivot_eq_one (Q : Place (AlgebraicClosure ℚ) F) : evalVec s Q (pivotIndex s Q hr) = 1 :=
  evalVec_pivot hr s hs0 Q

include hli in

theorem projAt_ne_zero (h2 : 2 ≤ r) (Q : Place (AlgebraicClosure ℚ) F) (j : Fin r) : projAt hr s Q j ≠ 0 := by
  set i₀ := pivotIndex s Q hr with hi₀
  set k := jdx hr s Q j with hk
  have hk0 : k ≠ i₀ := jdx_ne hr h2 s Q j
  rw [projAt_apply, ← hk, ← hi₀]
  intro h0
  have heq : s k = evalVec s Q k • s i₀ := sub_eq_zero.mp h0
  have hmem : s k ∈ Submodule.span (AlgebraicClosure ℚ) (s '' {i₀}) := by
    rw [Set.image_singleton, heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  exact hli.notMem_span_image (s := {i₀}) (by simpa using hk0) hmem

theorem projAt_mem_span (Q : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    projAt hr s Q j ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by
  rw [projAt_apply]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

variable {D : Divisor (AlgebraicClosure ℚ) F}
  (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace D)
  (hbpf : ∀ w : Place (AlgebraicClosure ℚ) F, ∃ i, w.ord (s i) + D w = 0)
  (hrat : ∀ v : Place (AlgebraicClosure ℚ) F, v.IsRational)

include hsD in
theorem projAt_mem (Q : Place (AlgebraicClosure ℚ) F) (j : Fin r) : projAt hr s Q j ∈ riemannRochSpace D :=
  hsD ▸ projAt_mem_span hr Q j

include hs0 hsD hbpf in

theorem ord_s_pivot (w : Place (AlgebraicClosure ℚ) F) : w.ord (s (pivotIndex s w hr)) = -D w :=
  ord_pivot_eq hr s hs0 D (mem_of_span_eq s hsD) w (hbpf w)

theorem evalAt_eq_zero_iff_ord_pos (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    v.evalAt f = 0 ↔ 0 < v.ord f := by
  constructor
  · intro h0
    by_contra hle
    have h0' : v.ord f = 0 :=
      le_antisymm (not_lt.mp hle)
        (((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem hf)).resolve_left hf0)
    exact v.evalAt_ne_zero_of_ord_eq_zero hv hf0 h0' h0
  · intro hpos
    have hnu : ¬IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
      rintro ⟨u, hu⟩
      have h := v.ord_coe_unit u
      rw [hu] at h
      change v.ord f = 0 at h
      omega
    have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
      by_contra h
      exact hnu ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)
    rw [v.evalAt_of_mem hf, hres, ← map_zero (algebraMap (AlgebraicClosure ℚ) v.ResidueField),
      v.residueInv_algebraMap]

include hr hs0 hsD hbpf hrat in

theorem sum_mul_evalVec_eq_zero (Q : Place (AlgebraicClosure ℚ) F) (c : Fin r → AlgebraicClosure ℚ)
    (hc : (∑ i, c i • s i) ∈ riemannRochSpace (D - Finsupp.single Q 1)) :
    ∑ i, c i * evalVec s Q i = 0 := by
  set i₀ := pivotIndex s Q hr with hi₀
  set f : F := ∑ i, c i • s i with hf
  have hrat' := hrat Q
  have hrs : ∀ i, s i * (s i₀)⁻¹ ∈ Q.toValuationSubring := fun i => ratio_pivot_mem hr s hs0 Q i
  have hq : f * (s i₀)⁻¹ = ∑ i, c i • (s i * (s i₀)⁻¹) := by
    rw [hf, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_assoc]
  have hqmem : f * (s i₀)⁻¹ ∈ Q.toValuationSubring := by rw [hq]; exact sum_smul_mem _ Q _ hrs
  have hqval : Q.evalAt (f * (s i₀)⁻¹) = ∑ i, c i * evalVec s Q i := by
    rw [hq, evalAt_sum_smul_of_mem _ Q hrat' _ hrs]
    exact Finset.sum_congr rfl fun i _ => by rw [hi₀, evalVec_apply hr s Q i]
  rw [← hqval]
  rcases eq_or_ne f 0 with h0 | h0
  · rw [h0, zero_mul, ← map_zero (algebraMap (AlgebraicClosure ℚ) F), Q.evalAt_algebraMap_eq]
  · have hq0 : f * (s i₀)⁻¹ ≠ 0 := mul_ne_zero h0 (inv_ne_zero (hs0 i₀))
    refine (evalAt_eq_zero_iff_ord_pos Q hrat' hqmem hq0).mpr ?_
    have hge := ((mem_riemannRochSpace_iff.mp hc) Q).resolve_left h0
    rw [Finsupp.sub_apply, Finsupp.single_eq_same] at hge
    have hpiv : Q.ord (s i₀) = -D Q := ord_s_pivot hr hs0 hsD hbpf Q
    rw [Q.ord_mul h0 (inv_ne_zero (hs0 i₀)), Q.ord_inv, hpiv]
    omega

include hs0 hli hsD hbpf hrat in

theorem ord_projAt_ge (h2 : 2 ≤ r) (Q : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    -D Q + 1 ≤ Q.ord (projAt hr s Q j) := by
  set i₀ := pivotIndex s Q hr with hi₀
  set k := jdx hr s Q j with hk
  have hrat' := hrat Q
  set a := evalVec s Q k with ha
  set q : F := s k * (s i₀)⁻¹ with hq
  have hqmem : q ∈ Q.toValuationSubring := ratio_pivot_mem hr s hs0 Q k
  have haq : a = Q.evalAt q := by rw [ha, evalVec_apply hr s Q k]
  set d : F := q - algebraMap (AlgebraicClosure ℚ) F a with hd
  have hcmem : algebraMap (AlgebraicClosure ℚ) F a ∈ Q.toValuationSubring := Q.algebraMap_mem' a
  have hdmem : d ∈ Q.toValuationSubring := sub_mem hqmem hcmem
  have hd0 : Q.evalAt d = 0 := by
    have hsum : d + algebraMap (AlgebraicClosure ℚ) F a = q := by rw [hd]; ring
    have := evalAt_add_of_mem Q hrat' hdmem hcmem
    rw [hsum, Q.evalAt_algebraMap_eq, ← haq] at this
    linear_combination -this
  have hprod : d * s i₀ = projAt hr s Q j := by
    rw [projAt_apply, ← hk, ← hi₀, ← ha, hd, hq, sub_mul, mul_assoc, inv_mul_cancel₀ (hs0 i₀), mul_one,
      Algebra.smul_def]
  have hne : projAt hr s Q j ≠ 0 := projAt_ne_zero hr hli h2 Q j
  have hdne : d ≠ 0 := by
    intro h0; apply hne; rw [← hprod, h0, zero_mul]
  have hdpos : 0 < Q.ord d := ord_pos_of_evalAt_eq_zero Q hrat' hdne hdmem hd0
  have hpiv : Q.ord (s i₀) = -D Q := ord_s_pivot hr hs0 hsD hbpf Q
  rw [← hprod, Q.ord_mul hdne (hs0 i₀), hpiv]
  omega

include hs0 hli hsD hbpf hrat in

theorem projAt_mem_sub (h2 : 2 ≤ r) (Q : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    projAt hr s Q j ∈ riemannRochSpace (D - Finsupp.single Q 1) := by
  classical
  rw [mem_riemannRochSpace_iff]
  intro w
  right
  rw [Finsupp.sub_apply, Finsupp.single_apply]
  by_cases hw : Q = w
  · subst hw
    rw [if_pos rfl]
    have := ord_projAt_ge hr hs0 hli hsD hbpf hrat h2 Q j
    omega
  · rw [if_neg hw, sub_zero]
    exact ((mem_riemannRochSpace_iff.mp (projAt_mem hr hsD Q j)) w).resolve_left
      (projAt_ne_zero hr hli h2 Q j)

include hs0 hli hsD hbpf hrat in

theorem span_projAt (h2 : 2 ≤ r) (Q : Place (AlgebraicClosure ℚ) F) :
    Submodule.span (AlgebraicClosure ℚ) (Set.range (projAt hr s Q)) = riemannRochSpace (D - Finsupp.single Q 1) := by
  classical
  set i₀ := pivotIndex s Q hr with hi₀
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact projAt_mem_sub hr hs0 hli hsD hbpf hrat h2 Q j
  · intro f hf
    have hfD : f ∈ riemannRochSpace D := by
      refine lSpace_mono (Finsupp.le_def.mpr fun v => ?_) hf
      rw [Finsupp.sub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    rw [← hsD] at hfD
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hfD
    have hkill : ∑ i, c i * evalVec s Q i = 0 :=
      sum_mul_evalVec_eq_zero hr hs0 hsD hbpf hrat Q c (hc ▸ hf)

    have hbar : ∀ j, s j - evalVec s Q j • s i₀ ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range (projAt hr s Q)) := by
      intro j
      by_cases hj : j = i₀
      · rw [hj, hi₀, evalVec_pivot hr s hs0 Q, one_smul, sub_self]
        exact Submodule.zero_mem _
      · have : projAt hr s Q j = s j - evalVec s Q j • s i₀ := by
          rw [projAt_apply, jdx_of_ne hr s Q (by rwa [← hi₀]), ← hi₀]
        rw [← this]
        exact Submodule.subset_span ⟨j, rfl⟩
    have hrepr : f = ∑ j, c j • (s j - evalVec s Q j • s i₀) := by
      have h1 : ∑ j, c j • (s j - evalVec s Q j • s i₀)
          = ∑ j, c j • s j - (∑ j, c j * evalVec s Q j) • s i₀ := by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_sub, mul_smul]
      rw [h1, hkill, zero_smul, sub_zero, hc]
    rw [hrepr]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbar j)

def selMat (hr : 0 < r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F) :
    Fin r → (Fin r × Fin r) → AlgebraicClosure ℚ :=
  fun j p => if p = (pivotIndex s Q hr, jdx hr s Q j) then -1 else 0

def recMat (hr : 0 < r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F) :
    (Fin r × Fin r) → Fin r → AlgebraicClosure ℚ :=
  fun p j => (if j = p.1 then (if p.1 = pivotIndex s Q hr then 0 else evalVec s Q p.2) else 0)
    - (if j = p.2 then (if p.2 = pivotIndex s Q hr then 0 else evalVec s Q p.1) else 0)

include hs0 in
theorem selMat_spec (Q P : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    ∑ p, selMat hr s Q j p * chordVec s P Q p = ∑ i, projMat hr s Q j i * evalVec s P i := by
  classical
  rw [projMat_mulVec]
  simp only [selMat, ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [chordVec, evalVec_pivot hr s hs0 Q]
  ring

include hs0 in
theorem recMat_spec (Q P : Place (AlgebraicClosure ℚ) F) (p : Fin r × Fin r) :
    ∑ j, recMat hr s Q p j * (∑ i, projMat hr s Q j i * evalVec s P i) = chordVec s P Q p := by
  classical
  obtain ⟨a, b⟩ := p
  simp only [projMat_mulVec]
  have key : ∀ j, recMat hr s Q (a, b) j * (evalVec s P (jdx hr s Q j)
        - evalVec s Q (jdx hr s Q j) * evalVec s P (pivotIndex s Q hr))
      = (if j = a then (if a = pivotIndex s Q hr then 0 else evalVec s Q b) *
            (evalVec s P (jdx hr s Q j) - evalVec s Q (jdx hr s Q j) * evalVec s P (pivotIndex s Q hr)) else 0)
        - (if j = b then (if b = pivotIndex s Q hr then 0 else evalVec s Q a) *
            (evalVec s P (jdx hr s Q j) - evalVec s Q (jdx hr s Q j) * evalVec s P (pivotIndex s Q hr)) else 0) := by
    intro j; simp only [recMat]; split_ifs <;> ring
  simp only [key, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [chordVec]
  have h1 := evalVec_pivot hr s hs0 Q
  by_cases ha : a = pivotIndex s Q hr <;> by_cases hb : b = pivotIndex s Q hr
  · simp only [if_pos ha, if_pos hb]; rw [ha, hb]; ring
  · simp only [if_pos ha, if_neg hb]; rw [jdx_of_ne hr s Q hb, ha, h1]; ring
  · simp only [if_neg ha, if_pos hb]; rw [jdx_of_ne hr s Q ha, hb, h1]; ring
  · simp only [if_neg ha, if_neg hb]; rw [jdx_of_ne hr s Q ha, jdx_of_ne hr s Q hb]; ring

def chordConst (hr : 0 < r) (s : Fin r → F) (Q : Place (AlgebraicClosure ℚ) F) : ℝ :=
  max (Real.log (Fintype.card (Fin r × Fin r)) + absLogHeight (fun q : Fin r × (Fin r × Fin r) => selMat hr s Q q.1 q.2))
    (Real.log (Fintype.card (Fin r)) + absLogHeight (fun q : (Fin r × Fin r) × Fin r => recMat hr s Q q.1 q.2))

include hs0 hli hsD hbpf hrat in

theorem abs_chord_sub_pointHt_projAt_le (h2 : 2 ≤ r) (Q : Place (AlgebraicClosure ℚ) F)
    (hubpf : ∀ w : Place (AlgebraicClosure ℚ) F,
      ∃ j, w.ord (projAt hr s Q j) + (D - Finsupp.single Q 1 : Divisor (AlgebraicClosure ℚ) F) w = 0)
    (P : Place (AlgebraicClosure ℚ) F) (hPQ : P ≠ Q) (hPD : D P = 0) :
    |absLogHeight (chordVec s P Q) - pointHt (projAt hr s Q) P| ≤ chordConst hr s Q := by
  classical
  set u := projAt hr s Q with hu
  have hu0 : ∀ j, u j ≠ 0 := projAt_ne_zero hr hli h2 Q
  have hDQ : (D - Finsupp.single Q 1 : Divisor (AlgebraicClosure ℚ) F) P = 0 := by
    rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hPQ), sub_zero, hPD]
  have hord : P.ord (s (pivotIndex s P hr)) = P.ord (u (pivotIndex u P hr)) := by
    rw [ord_s_pivot hr hs0 hsD hbpf P, hPD, neg_zero, hu,
      ord_pivot_eq hr (projAt hr s Q) hu0 (D - Finsupp.single Q 1)
        (projAt_mem_sub hr hs0 hli hsD hbpf hrat h2 Q) P (hubpf P), hDQ, neg_zero]
  obtain ⟨c, hc0, hev⟩ :=
    evalVec_eq_smul_linear hr hr s u hs0 hu0 (projMat hr s Q) (projMat_spec hr s Q) P (hrat P) hord
  set y : Fin r → AlgebraicClosure ℚ := fun j => ∑ i, projMat hr s Q j i * evalVec s P i with hy
  have hpt : pointHt u P = absLogHeight y := by
    rw [pointHt, hev, absLogHeight_smul _ hc0]

  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have h1 : absLogHeight y ≤ Real.log (Fintype.card (Fin r × Fin r))
      + absLogHeight (fun q : Fin r × (Fin r × Fin r) => selMat hr s Q q.1 q.2)
      + absLogHeight (chordVec s P Q) := by
    have hfun : y = fun j => ∑ p, selMat hr s Q j p * chordVec s P Q p := by
      funext j; rw [hy]; exact (selMat_spec hr hs0 Q P j).symm
    rw [hfun]
    exact absLogHeight_linear_le _ _
  have h2' : absLogHeight (chordVec s P Q) ≤ Real.log (Fintype.card (Fin r))
      + absLogHeight (fun q : (Fin r × Fin r) × Fin r => recMat hr s Q q.1 q.2) + absLogHeight y := by
    have hfun : chordVec s P Q = fun p => ∑ j, recMat hr s Q p j * y j := by
      funext p; rw [hy]; exact (recMat_spec hr hs0 Q P p).symm
    conv_lhs => rw [hfun]
    exact absLogHeight_linear_le _ _
  rw [hpt, abs_le, chordConst]
  constructor
  · linarith [le_max_left (Real.log (Fintype.card (Fin r × Fin r))
        + absLogHeight (fun q : Fin r × (Fin r × Fin r) => selMat hr s Q q.1 q.2))
      (Real.log (Fintype.card (Fin r)) + absLogHeight (fun q : (Fin r × Fin r) × Fin r => recMat hr s Q q.1 q.2)),
      le_max_right (Real.log (Fintype.card (Fin r × Fin r))
        + absLogHeight (fun q : Fin r × (Fin r × Fin r) => selMat hr s Q q.1 q.2))
      (Real.log (Fintype.card (Fin r)) + absLogHeight (fun q : (Fin r × Fin r) × Fin r => recMat hr s Q q.1 q.2))]
  · linarith [le_max_left (Real.log (Fintype.card (Fin r × Fin r))
        + absLogHeight (fun q : Fin r × (Fin r × Fin r) => selMat hr s Q q.1 q.2))
      (Real.log (Fintype.card (Fin r)) + absLogHeight (fun q : (Fin r × Fin r) × Fin r => recMat hr s Q q.1 q.2)),
      le_max_right (Real.log (Fintype.card (Fin r × Fin r))
        + absLogHeight (fun q : Fin r × (Fin r × Fin r) => selMat hr s Q q.1 q.2))
      (Real.log (Fintype.card (Fin r)) + absLogHeight (fun q : (Fin r × Fin r) × Fin r => recMat hr s Q q.1 q.2))]

end ProjAt
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero.P2MS4"

end P2MS4
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero.P2MS4"

namespace P2MS4

section Core

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem card_emb_eq {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) :
    (r : ℤ) = (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 2 := by
  have h1 : Module.finrank (AlgebraicClosure ℚ) (riemannRochSpace (embDivisor N)) = r := by
    rw [← hs.2, finrank_span_eq_card hs.1, Fintype.card_fin]
  have h2 := ell_eq_bar N (embDivisor N)
    (by rw [degree_embDivisor, ModularCurve.embDegree]; push_cast; omega)
  have h3 : (ell (embDivisor N) : ℤ) = r := by unfold ell LSpace; exact_mod_cast h1
  rw [degree_embDivisor, ModularCurve.embDegree] at h2
  push_cast at h2
  omega

theorem two_le_card_emb {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) : 2 ≤ r := by
  have := card_emb_eq hs; omega

theorem degree_embDivisor_sub_single (Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (embDivisor N - Finsupp.single Q 1).degree = (embDegree N : ℤ) - 1 := by
  rw [map_sub, degree_embDivisor, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N Q]; ring

theorem projAt_bpf_bar (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
    (Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∃ j, w.ord (projAt hr s Q j)
        + (embDivisor N - Finsupp.single Q 1 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) w = 0 :=
  bpf_of_span_eq N (projAt hr s Q)
    (span_projAt hr (emb_ne_zero hs) hs.1 hs.2 (emb_bpf hs) (isRational_bar N) (two_le_card_emb hs) Q)
    (by rw [degree_embDivisor_sub_single, ModularCurve.embDegree]; push_cast; omega)

theorem abs_chord_sub_pointHt_projAt_le_bar (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N}
    (hs : IsEmbBasis N s) (Q P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hPQ : P ≠ Q) (hP : P ≠ cuspInftyBar N) :
    |absLogHeight (chordVec s P Q) - pointHt (projAt hr s Q) P| ≤ chordConst hr s Q :=
  abs_chord_sub_pointHt_projAt_le hr (emb_ne_zero hs) hs.1 hs.2 (emb_bpf hs) (isRational_bar N)
    (two_le_card_emb hs) Q (projAt_bpf_bar hr hs Q) P hPQ (embDivisor_apply_of_ne hP)

theorem absLogHeight_one {ι : Type} [Fintype ι] : absLogHeight (fun _ : ι => (1 : AlgebraicClosure ℚ)) = 0 := by
  haveI := finiteDimensional_adjoin_range (fun _ : ι => (1 : AlgebraicClosure ℚ))
  unfold absLogHeight
  have : (fun i : ι => (⟨(fun _ : ι => (1 : AlgebraicClosure ℚ)) i,
      IntermediateField.subset_adjoin ℚ (Set.range fun _ : ι => (1 : AlgebraicClosure ℚ)) ⟨i, rfl⟩⟩ :
        IntermediateField.adjoin ℚ (Set.range fun _ : ι => (1 : AlgebraicClosure ℚ))))
      = fun _ => 1 := by
    funext i; apply Subtype.ext; rfl
  rw [this, Height.logHeight_eq_log_mulHeight, Height.fun_mulHeight_one, Real.log_one, mul_zero]

theorem pointHt_projAt_eq_zero_of_genus_zero (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N}
    (hs : IsEmbBasis N s) (hg : genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) = 0)
    (Q P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    pointHt (projAt hr s Q) P = 0 := by
  have hr2 : r = 2 := by have := card_emb_eq hs; rw [hg] at this; omega
  have h2 := two_le_card_emb hs

  have hjdx : ∀ j j' : Fin r, jdx hr s Q j = jdx hr s Q j' := by
    intro j j'
    have ha := jdx_ne hr h2 s Q j
    have hb := jdx_ne hr h2 s Q j'
    have h3 := (jdx hr s Q j).isLt
    have h4 := (jdx hr s Q j').isLt
    have h5 := (pivotIndex s Q hr).isLt
    rw [Ne, Fin.ext_iff] at ha hb
    rw [Fin.ext_iff]
    omega
  have hconst : ∀ j j' : Fin r, projAt hr s Q j = projAt hr s Q j' := by
    intro j j'; rw [projAt_apply, projAt_apply, hjdx j j']
  have hu0 : ∀ j, projAt hr s Q j ≠ 0 := projAt_ne_zero hr hs.1 h2 Q
  have hev : evalVec (projAt hr s Q) P = fun _ => 1 := by
    funext j
    rw [evalVec_apply hr, hconst j (pivotIndex (projAt hr s Q) P hr), mul_inv_cancel₀ (hu0 _), Place.evalAt_one]
  rw [pointHt, hev, absLogHeight_one]

theorem abs_projAt_height_sub_le (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
    (Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      |(embDegree N : ℝ) * pointHt (projAt hr s Q) P
          - 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) * pointHt s P|
        ≤ 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) * ε * pointHt s P + C := by
  classical
  set g : ℕ := genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) with hg
  set u := projAt hr s Q with hu
  have h2 := two_le_card_emb hs
  have hu0 : ∀ j, u j ≠ 0 := projAt_ne_zero hr hs.1 h2 Q
  have hs0 : ∀ i, s i ≠ 0 := emb_ne_zero hs
  have hembR : (embDegree N : ℝ) = 2 * (g : ℝ) + 1 := by rw [ModularCurve.embDegree, ← hg]; push_cast; ring
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  ·
    refine ⟨0, fun P => ?_⟩
    have h0 : pointHt u P = 0 := by rw [hu]; exact pointHt_projAt_eq_zero_of_genus_zero hr hs (by rw [← hg, hg0]) Q P
    rw [h0, hg0]; simp
  ·
    set EQ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := embDivisor N - Finsupp.single Q 1 with hEQ
    set Big₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := (2 * g) • embDivisor N with hBig₁
    set Big₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := (2 * g + 1) • EQ with hBig₂
    have hdeg₁ : Big₁.degree = 2 * (g : ℤ) * (2 * g + 1) := by
      rw [hBig₁, map_nsmul, degree_embDivisor, nsmul_eq_mul, ModularCurve.embDegree, ← hg]; push_cast; ring
    have hdeg₂ : Big₂.degree = 2 * (g : ℤ) * (2 * g + 1) := by
      rw [hBig₂, map_nsmul, hEQ, degree_embDivisor_sub_single, nsmul_eq_mul, ModularCurve.embDegree, ← hg]
      push_cast; ring
    have hg1 : (1 : ℤ) ≤ g := by exact_mod_cast hgpos
    have hd₁ : 2 * (g : ℤ) + 1 ≤ Big₁.degree := by rw [hdeg₁]; nlinarith
    have hd₂ : 2 * (g : ℤ) + 1 ≤ Big₂.degree := by rw [hdeg₂]; nlinarith
    have hdeg : Big₁.degree = Big₂.degree := by rw [hdeg₁, hdeg₂]
    obtain ⟨c₁, w₁, hw₁0, hw₁span, -⟩ := exists_family_span_eq (K := AlgebraicClosure ℚ) Big₁
    obtain ⟨c₂, w₂, hw₂0, hw₂span, -⟩ := exists_family_span_eq (K := AlgebraicClosure ℚ) Big₂

    set U := powFam u (2 * g) with hU
    have hU0 : ∀ idx, U idx ≠ 0 := powFam_ne_zero hu0 (2 * g)
    have hUmem : ∀ idx, U idx ∈ riemannRochSpace Big₂ := fun idx =>
      powFam_mem (projAt_mem_sub hr hs0 hs.1 hs.2 (emb_bpf hs) (isRational_bar N) h2 Q) (2 * g) idx
    have hUbpf : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ idx, w.ord (U idx) + Big₂ w = 0 :=
      powFam_bpf hu0 (projAt_bpf_bar hr hs Q) (2 * g)
    set S := powFam s (2 * g - 1) with hS
    have h21 : 2 * g - 1 + 1 = 2 * g := by omega
    have hS0 : ∀ idx, S idx ≠ 0 := powFam_ne_zero hs0 (2 * g - 1)
    have hSmem : ∀ idx, S idx ∈ riemannRochSpace Big₁ := by
      intro idx
      have := powFam_mem (emb_mem hs) (2 * g - 1) idx
      rwa [h21] at this
    have hSbpf : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ idx, w.ord (S idx) + Big₁ w = 0 := by
      intro w
      have := powFam_bpf hs0 (emb_bpf hs) (2 * g - 1) w
      rwa [h21] at this
    obtain ⟨C₁, hC₁⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero N
      w₂ U hw₂0 hU0 Big₂ hd₂ hw₂span hUmem hUbpf
    obtain ⟨C₂, hC₂⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero N
      w₁ S hw₁0 hS0 Big₁ hd₁ hw₁span hSmem hSbpf
    obtain ⟨C₃, hC₃⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_mul_add_of_degree_eq N
      w₁ w₂ hw₁0 hw₂0 Big₁ Big₂ hd₁ hdeg hw₁span hw₂span ε hε
    refine ⟨C₁ + C₂ + C₃ + ε * C₂, fun P => ?_⟩
    have hv := isRational_bar N P
    have h1 := hC₁ P
    have h2' := hC₂ P
    have h3 := hC₃ P
    have hUeq : pointHt U P = (2 * g + 1 : ℝ) * pointHt u P := by
      rw [hU]; have := pointHt_powFam hr u hu0 P hv (2 * g); push_cast at this ⊢; linarith
    have hSeq : pointHt S P = (2 * g : ℝ) * pointHt s P := by
      rw [hS]; have := pointHt_powFam hr s hs0 P hv (2 * g - 1)
      rw [this]; congr 1; exact_mod_cast h21
    rw [abs_le] at h1 h2' h3 ⊢
    rw [hUeq] at h1
    rw [hSeq] at h2'
    have hpt := pointHt_nonneg s P
    have hptw := pointHt_nonneg w₁ P
    rw [hembR]
    constructor <;> nlinarith [h1.1, h1.2, h2'.1, h2'.2, h3.1, h3.2, mul_le_mul_of_nonneg_left h2'.1 hε.le,
      mul_le_mul_of_nonneg_left h2'.2 hε.le]

end Core
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero.P2MS4"

end P2MS4
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero.P2MS4"

namespace P2MC25

open P2MS4

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem rr_pow : ∀ m : ℕ, 1 ≤ m →
    riemannRochSpace (embDivisor N) ^ m = riemannRochSpace ((m : ℤ) • embDivisor N)
  | 0 => fun h => absurd h (by norm_num)
  | 1 => fun _ => by rw [pow_one, Nat.cast_one, one_zsmul]
  | 2 => fun _ => by
    rw [pow_two, ModularCurve.JZero.riemannRochSpace_embDivisor_mul_self N]; norm_num
  | (m + 3) => fun _ => by
    have ih := rr_pow (m + 2) (by omega)
    rw [pow_succ, ih, mul_comm, ModularCurve.JZero.riemannRochSpace_embDivisor_mul_eq N (m + 2) (by omega)]
    push_cast
    ring_nf

theorem span_monomials {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (m : ℕ) (hm : 1 ≤ m) :
    Submodule.span (AlgebraicClosure ℚ) (Set.range fun φ : Fin m → Fin r => ∏ l, s (φ l))
      = riemannRochSpace ((m : ℤ) • embDivisor N) := by
  classical
  rw [← rr_pow (N := N) m hm, ← hs.2, Submodule.span_pow]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨φ, rfl⟩
    apply Submodule.subset_span
    rw [Set.mem_pow]
    exact ⟨fun l => ⟨s (φ l), ⟨φ l, rfl⟩⟩, by rw [List.prod_ofFn]⟩
  · rw [Submodule.span_le]
    intro f hf
    rw [Set.mem_pow] at hf
    obtain ⟨g, hg⟩ := hf
    apply Submodule.subset_span
    choose φ hφ using fun l => (g l).2
    refine ⟨φ, ?_⟩
    rw [← hg, List.prod_ofFn]
    exact Finset.prod_congr rfl fun l _ => hφ l

noncomputable def formOf (m : ℕ) (c : (Fin m → Fin r) → AlgebraicClosure ℚ) : MvPolynomial (Fin r) (AlgebraicClosure ℚ) :=
  ∑ φ : Fin m → Fin r, MvPolynomial.C (c φ) * ∏ l, MvPolynomial.X (φ l)

theorem formOf_isHomogeneous (m : ℕ) (c : (Fin m → Fin r) → AlgebraicClosure ℚ) : (formOf m c).IsHomogeneous m := by
  classical
  unfold formOf
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun φ _ => ?_
  apply MvPolynomial.IsHomogeneous.C_mul
  have := MvPolynomial.IsHomogeneous.prod Finset.univ (fun l => (MvPolynomial.X (φ l) : MvPolynomial (Fin r) (AlgebraicClosure ℚ)))
    (fun _ => 1) (fun l _ => MvPolynomial.isHomogeneous_X _ _)
  simpa using this

theorem aeval_formOf (s : Fin r → modularFunctionFieldBar N) (m : ℕ) (c : (Fin m → Fin r) → AlgebraicClosure ℚ) :
    MvPolynomial.aeval s (formOf m c) = ∑ φ : Fin m → Fin r, c φ • ∏ l, s (φ l) := by
  classical
  unfold formOf
  rw [map_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [map_mul, MvPolynomial.aeval_C, map_prod, Algebra.smul_def]
  congr 1
  exact Finset.prod_congr rfl fun l _ => MvPolynomial.aeval_X s (φ l)

theorem exists_form_of_mem {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (m : ℕ) {f : modularFunctionFieldBar N}
    (hf : f ∈ riemannRochSpace ((m : ℤ) • embDivisor N)) :
    ∃ P : MvPolynomial (Fin r) (AlgebraicClosure ℚ), P.IsHomogeneous m ∧ MvPolynomial.aeval s P = f := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  ·
    have hCB : ConstantsAreBase (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      constantsAreBase_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N
    have hmem : f ∈ LSpace (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := by rwa [Nat.cast_zero, zero_smul] at hf
    rw [hCB] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C _ _, ?_⟩
    rw [MvPolynomial.aeval_C, ← hc]; rfl
  · rw [← span_monomials hs m hm] at hf
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hf
    exact ⟨formOf m c, formOf_isHomogeneous m c, by rw [aeval_formOf, hc]⟩

noncomputable def linForm (a : Fin r → AlgebraicClosure ℚ) : MvPolynomial (Fin r) (AlgebraicClosure ℚ) :=
  ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i

theorem linForm_isHomogeneous (a : Fin r → AlgebraicClosure ℚ) : (linForm a).IsHomogeneous 1 := by
  unfold linForm
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X _ i).C_mul _

theorem eval_linForm (a x : Fin r → AlgebraicClosure ℚ) : MvPolynomial.eval x (linForm a) = ∑ i, a i * x i := by
  unfold linForm; simp [map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem aeval_linForm (s : Fin r → modularFunctionFieldBar N) (a : Fin r → AlgebraicClosure ℚ) :
    MvPolynomial.aeval s (linForm a) = ∑ i, a i • s i := by
  unfold linForm
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.smul_def]

variable {s : Fin r → modularFunctionFieldBar N}

theorem aeval_linForm_ne_zero (hs : IsEmbBasis N s) {a : Fin r → AlgebraicClosure ℚ} (ha : a ≠ 0) :
    MvPolynomial.aeval s (linForm a) ≠ 0 := by
  rw [aeval_linForm]
  intro h0
  exact ha (funext fun i => Fintype.linearIndependent_iff.mp hs.1 a h0 i)

theorem aeval_linForm_mem (hs : IsEmbBasis N s) (a : Fin r → AlgebraicClosure ℚ) :
    MvPolynomial.aeval s (linForm a) ∈ riemannRochSpace (embDivisor N) := by
  rw [aeval_linForm]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (emb_mem hs i)

theorem one_le_ord_add_of_dot_eq_zero (hs : IsEmbBasis N s) (hr : 0 < r) {c : Fin r → AlgebraicClosure ℚ} (hc : c ≠ 0)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hcw : ∑ i, c i * evalVec s w i = 0) :
    1 ≤ w.ord (MvPolynomial.aeval s (linForm c)) + embDivisor N w := by
  have hrat := isRational_bar N w
  have hs0 := emb_ne_zero hs
  set piv := s (pivotIndex s w hr) with hpiv
  have hpiv0 : piv ≠ 0 := hs0 _
  have hordpiv : w.ord piv = -embDivisor N w := ord_emb_pivot hr hs w

  have hreg : ∀ i, s i * piv⁻¹ ∈ w.toValuationSubring := fun i => by
    refine w.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 i) (inv_ne_zero hpiv0)) ?_
    rw [Place.ord_mul _ (hs0 i) (inv_ne_zero hpiv0), Place.ord_inv, hordpiv]
    have := ((mem_riemannRochSpace_iff.mp (emb_mem hs i)) w).resolve_left (hs0 i)
    linarith
  have hsum := evalAt_sum_smul_of_mem Finset.univ w hrat c (f := fun i => s i * piv⁻¹) hreg
  have hval : w.evalAt (∑ i, c i • (s i * piv⁻¹)) = 0 := by
    rw [hsum, ← hcw]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [evalVec_apply hr]
  have hℓ0 : MvPolynomial.aeval s (linForm c) ≠ 0 := aeval_linForm_ne_zero hs hc
  have hfac : ∑ i, c i • (s i * piv⁻¹) = MvPolynomial.aeval s (linForm c) * piv⁻¹ := by
    rw [aeval_linForm, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_assoc]
  have hne : MvPolynomial.aeval s (linForm c) * piv⁻¹ ≠ 0 := mul_ne_zero hℓ0 (inv_ne_zero hpiv0)
  have hmem : MvPolynomial.aeval s (linForm c) * piv⁻¹ ∈ w.toValuationSubring := by
    rw [← hfac]; exact Subring.sum_mem _ fun i _ => by
      rw [Algebra.smul_def]; exact Subring.mul_mem _ (w.algebraMap_mem' _) (hreg i)
  rw [hfac] at hval
  have hpos : 0 < w.ord (MvPolynomial.aeval s (linForm c) * piv⁻¹) :=
    ord_pos_of_evalAt_eq_zero w hrat hne hmem hval
  rw [Place.ord_mul _ hℓ0 (inv_ne_zero hpiv0), Place.ord_inv, hordpiv] at hpos
  linarith

theorem exists_covector {K : Type*} [Field K] {n : ℕ} (x v : Fin n → K) (i₀ : Fin n) (hx : x i₀ ≠ 0)
    (hv : ∀ t : K, v ≠ t • x) : ∃ c : Fin n → K, c ≠ 0 ∧ ∑ i, c i * x i = 0 ∧ ∑ i, c i * v i ≠ 0 := by
  classical
  by_contra hall
  push_neg at hall

  have key : ∀ j, x i₀ * v j - x j * v i₀ = 0 := by
    intro j
    by_cases hj : j = i₀
    · subst hj; ring
    set c : Fin n → K := fun i => if i = j then x i₀ else if i = i₀ then -x j else 0 with hc
    have hc0 : c ≠ 0 := fun h => by
      have := congrFun h j; simp [hc] at this; exact hx this
    have hcx : ∑ i, c i * x i = 0 := by
      rw [Finset.sum_eq_add_of_mem (a := j) (b := i₀) (Finset.mem_univ _) (Finset.mem_univ _) hj]
      · simp [hc, hj, Ne.symm hj]; ring
      · intro i _ hij; simp [hc, hij.1, hij.2]
    have := hall c hc0 hcx
    rw [Finset.sum_eq_add_of_mem (a := j) (b := i₀) (Finset.mem_univ _) (Finset.mem_univ _) hj] at this
    · simp [hc, hj, Ne.symm hj] at this; linear_combination this
    · intro i _ hij; simp [hc, hij.1, hij.2]
  apply hv (v i₀ / x i₀)
  funext j
  have hk := key j
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination hk

theorem ord_pow' (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) {f : modularFunctionFieldBar N} (hf : f ≠ 0) : ∀ n : ℕ, w.ord (f ^ n) = n * w.ord f
  | 0 => by rw [pow_zero, Place.ord_one]; simp
  | n + 1 => by rw [pow_succ, Place.ord_mul _ (pow_ne_zero _ hf) hf, ord_pow' w hf n]; push_cast; ring

theorem ord_prod_pow {ι : Type*} (S : Finset ι) (f : ι → modularFunctionFieldBar N) (n : ι → ℕ) (hf : ∀ i ∈ S, f i ≠ 0)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (∏ i ∈ S, f i ^ n i) ≠ 0 ∧ w.ord (∏ i ∈ S, f i ^ n i) = ∑ i ∈ S, (n i : ℤ) * w.ord (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    obtain ⟨h0, hord⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ha0 : f a ^ n a ≠ 0 := pow_ne_zero _ (hf a (Finset.mem_insert_self a S))
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    refine ⟨mul_ne_zero ha0 h0, ?_⟩
    rw [Place.ord_mul _ ha0 h0, ord_pow' _ (hf a (Finset.mem_insert_self a S)), hord]

theorem main (hs : IsEmbBasis N s) (v : Fin r → AlgebraicClosure ℚ)
    (hv : ∀ (Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (c : AlgebraicClosure ℚ), v ≠ c • evalVec s Q) :
    ∃ (k : ℕ) (Φ : MvPolynomial (Fin r) (AlgebraicClosure ℚ)),
      Φ.IsHomogeneous k ∧ MvPolynomial.aeval s Φ = 0 ∧ MvPolynomial.eval v Φ ≠ 0 := by
  classical

  have h2 : 2 ≤ r := two_le_card_emb hs
  have hr : 0 < r := by omega
  have hs0 := emb_ne_zero hs
  obtain ⟨Q₀⟩ : Nonempty (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := ⟨cuspInftyBar N⟩
  have hv0 : v ≠ 0 := fun h => hv Q₀ 0 (by rw [h, zero_smul])
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by by_contra h; push_neg at h; exact hv0 (funext h)
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin r, j ≠ i₀ := by
    by_contra h; push_neg at h
    have : Fintype.card (Fin r) ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => by rw [h a, h b]
    rw [Fintype.card_fin] at this; omega

  set a : Fin r → AlgebraicClosure ℚ := fun i => if i = i₀ then v j₀ else if i = j₀ then -v i₀ else 0 with hadef
  have ha0 : a ≠ 0 := fun h => by
    have := congrFun h j₀; simp [hadef, hj₀] at this; exact hi₀ this
  have hav : ∑ i, a i * v i = 0 := by
    rw [Finset.sum_eq_add_of_mem (a := i₀) (b := j₀) (Finset.mem_univ _) (Finset.mem_univ _) (Ne.symm hj₀)]
    · simp [hadef, hj₀]; ring
    · intro i _ hii; simp [hadef, hii.1, hii.2]
  set u := MvPolynomial.aeval s (linForm a) with hu
  have hu0 : u ≠ 0 := aeval_linForm_ne_zero hs ha0
  have huE : u ∈ riemannRochSpace (embDivisor N) := aeval_linForm_mem hs a

  obtain ⟨Du, hDu, hDudeg⟩ := (hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor u hu0
  set Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := Du + embDivisor N with hZa
  have hZa_apply : ∀ w, Za w = w.ord u + embDivisor N w := fun w => by rw [hZa, Finsupp.add_apply, hDu]
  have hZa0 : ∀ w, 0 ≤ Za w := fun w => by
    rw [hZa_apply]; have := ((mem_riemannRochSpace_iff.mp huE) w).resolve_left hu0; linarith
  set S := Za.support with hS
  set n : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℕ := fun w => (Za w).toNat with hn
  have hnZ : ∀ w, (n w : ℤ) = Za w := fun w => Int.toNat_of_nonneg (hZa0 w)

  have hcov : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ c : Fin r → AlgebraicClosure ℚ, c ≠ 0 ∧ ∑ i, c i * evalVec s w i = 0 ∧ ∑ i, c i * v i ≠ 0 := by
    intro w
    refine exists_covector (evalVec s w) v (pivotIndex s w hr) ?_ fun t => hv w t
    rw [evalVec_apply hr, mul_inv_cancel₀ (hs0 _), Place.evalAt_one]; exact one_ne_zero
  choose c hc0 hcx hcv using hcov

  set G : MvPolynomial (Fin r) (AlgebraicClosure ℚ) := ∏ w ∈ S, linForm (c w) ^ n w with hG
  set k : ℕ := ∑ w ∈ S, n w with hk
  have hGhom : G.IsHomogeneous k := by
    rw [hG, hk]
    refine MvPolynomial.IsHomogeneous.prod S _ _ fun w _ => ?_
    have := (linForm_isHomogeneous (c w)).pow (n w)
    rwa [one_mul] at this
  have hGv : MvPolynomial.eval v G ≠ 0 := by
    rw [hG, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun w _ => by rw [map_pow, eval_linForm]; exact pow_ne_zero _ (hcv w)

  set ℓ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → modularFunctionFieldBar N := fun w => MvPolynomial.aeval s (linForm (c w)) with hℓ
  have hℓ0 : ∀ w, ℓ w ≠ 0 := fun w => aeval_linForm_ne_zero hs (hc0 w)
  have hGs : MvPolynomial.aeval s G = ∏ w ∈ S, ℓ w ^ n w := by rw [hG, map_prod]; simp only [map_pow]; rfl
  have hGs0 : (∏ w ∈ S, ℓ w ^ n w) ≠ 0 := (ord_prod_pow S ℓ n (fun w _ => hℓ0 w) Q₀).1
  have hordG : ∀ w' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w'.ord (∏ w ∈ S, ℓ w ^ n w) = ∑ w ∈ S, (n w : ℤ) * w'.ord (ℓ w) :=
    fun w' => (ord_prod_pow S ℓ n (fun w _ => hℓ0 w) w').2
  have hGs0' : MvPolynomial.aeval s G ≠ 0 := by rw [hGs]; exact hGs0
  have hkZ : (k : ℤ) = ∑ w ∈ S, (n w : ℤ) := by rw [hk]; push_cast; rfl
  have hdivG : ∀ w' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), Za w' - (k : ℤ) * embDivisor N w' ≤ w'.ord (MvPolynomial.aeval s G) := by
    intro w'
    rw [hGs, hordG w', hkZ, Finset.sum_mul]
    have hterm : ∀ w ∈ S, (n w : ℤ) * (-embDivisor N w') + (if w = w' then (n w : ℤ) else 0) ≤ (n w : ℤ) * w'.ord (ℓ w) := by
      intro w _
      have hlow : -embDivisor N w' ≤ w'.ord (ℓ w) :=
        ((mem_riemannRochSpace_iff.mp (aeval_linForm_mem hs (c w))) w').resolve_left (hℓ0 w)
      have hn0 : (0 : ℤ) ≤ n w := Int.natCast_nonneg _
      split_ifs with hww
      · subst hww
        have h1 := one_le_ord_add_of_dot_eq_zero hs hr (hc0 w) w (hcx w)
        nlinarith
      · nlinarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' S w'] at hsum
    have hZw : (if w' ∈ S then (n w' : ℤ) else 0) = Za w' := by
      split_ifs with hw'
      · exact hnZ w'
      · rw [hS, Finsupp.notMem_support_iff] at hw'; rw [hw']
    rw [hZw] at hsum
    have e : ∑ w ∈ S, (n w : ℤ) * (-embDivisor N w') = -(∑ w ∈ S, (n w : ℤ) * embDivisor N w') := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun w _ => by ring
    rw [e] at hsum
    linarith

  have hk1 : 1 ≤ k := by

    have hdeg : Za.degree = embDegree N := by rw [hZa, map_add, hDudeg, zero_add, degree_embDivisor]
    by_contra hk0
    push_neg at hk0
    have hk00 : k = 0 := by omega
    have hS0 : ∀ w ∈ S, n w = 0 := fun w hw => by
      have := Finset.single_le_sum (fun w _ => Nat.zero_le (n w)) hw; rw [← hk, hk00] at this; omega
    have hZa00 : Za = 0 := by
      ext w
      by_cases hw : w ∈ S
      · have := hnZ w; rw [hS0 w hw] at this; simpa using this.symm
      · rw [hS, Finsupp.notMem_support_iff] at hw; exact hw
    rw [hZa00, map_zero] at hdeg
    have : (1 : ℤ) ≤ embDegree N := by rw [ModularCurve.embDegree]; push_cast; linarith [Int.natCast_nonneg (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))]
    linarith
  set q := MvPolynomial.aeval s G * u⁻¹ with hq
  have hqmem : q ∈ riemannRochSpace (((k - 1 : ℕ) : ℤ) • embDivisor N) := by
    rw [mem_riemannRochSpace_iff]
    intro w; right
    rw [hq, Place.ord_mul _ hGs0' (inv_ne_zero hu0), Place.ord_inv, Finsupp.smul_apply, smul_eq_mul]
    have h1 := hdivG w
    have h2 := hZa_apply w
    push_cast [Nat.cast_sub hk1]
    nlinarith
  obtain ⟨G', hG'hom, hG'⟩ := exists_form_of_mem hs (k - 1) hqmem

  refine ⟨k, G - linForm a * G', ?_, ?_, ?_⟩
  · refine hGhom.sub ?_
    have := (linForm_isHomogeneous a).mul hG'hom
    rwa [show 1 + (k - 1) = k by omega] at this
  · rw [map_sub, map_mul, hG', ← hu, hq]
    field_simp
    ring
  · rw [map_sub, map_mul, eval_linForm, hav, zero_mul, sub_zero]
    exact hGv

end P2MC25
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero.P2MS4"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero.P2MS4"

open AlgebraicCurve ModularCurve in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v : Fin r → AlgebraicClosure ℚ)
    (hv : ∀ (Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (c : AlgebraicClosure ℚ),
      v ≠ c • evalVec s Q) :
    ∃ (k : ℕ) (Φ : MvPolynomial (Fin r) (AlgebraicClosure ℚ)),
      Φ.IsHomogeneous k ∧ MvPolynomial.aeval s Φ = 0 ∧ MvPolynomial.eval v Φ ≠ 0 :=
  P2MC25.main hs v hv

end S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero
end P2MW
export P2MW.S_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero (solution)
