-- Prove2me | solution 1 for ModularCurve.exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/51a10d13-2f5e-5629-9aab-ba07752ac040

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials
import Theorems.Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_differential_eq_zero_of_lift_correspondence_eq_zero
import Theorems.Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero
import Theorems.Thm_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm
import Theorems.Thm_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd
import Theorems.Thm_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_dvd
import Theorems.Thm_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne
import Theorems.Thm_CuspForm_qCoeff_heckeTLinOne
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped TensorProduct

namespace A1UG1COT

section KernelTransfer

variable {ι A C : Type*} [Ring A] [Algebra ℤ A] [Ring C] [Algebra ℤ C] (a : ι → A) (c : ι → C)

noncomputable def evalAdjoin : FreeAlgebra ℤ ι →+* ↥(Algebra.adjoin ℤ (Set.range a)) :=
  ((FreeAlgebra.lift ℤ a).codRestrict (Algebra.adjoin ℤ (Set.range a)) (fun p => by
    rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift]; exact ⟨p, rfl⟩)).toRingHom

@[scoped simp] theorem coe_evalAdjoin (p : FreeAlgebra ℤ ι) :
    (evalAdjoin a p : A) = FreeAlgebra.lift ℤ a p := rfl

theorem evalAdjoin_surjective : Function.Surjective (evalAdjoin a) := by
  rintro ⟨t, ht⟩
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift] at ht
  obtain ⟨p, rfl⟩ := ht
  exact ⟨p, rfl⟩

theorem evalAdjoin_ι (i : ι) :
    evalAdjoin a (FreeAlgebra.ι ℤ i) = ⟨a i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ :=
  Subtype.ext (by simp)

theorem exists_ringHom_adjoin_of_ker_iff
    (hker : ∀ p : FreeAlgebra ℤ ι, FreeAlgebra.lift ℤ a p = 0 ↔ FreeAlgebra.lift ℤ c p = 0) :
    ∃ ρ : ↥(Algebra.adjoin ℤ (Set.range a)) →+* C,
      Function.Injective ρ ∧
      ∀ i, ρ ⟨a i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ = c i := by
  classical
  set f := evalAdjoin a with hf
  have hsurj := evalAdjoin_surjective a
  let g : {g : FreeAlgebra ℤ ι →+* C // RingHom.ker f ≤ RingHom.ker g} :=
    ⟨(FreeAlgebra.lift ℤ c).toRingHom, fun p hp => by
      rw [RingHom.mem_ker] at hp ⊢
      have hp' : FreeAlgebra.lift ℤ a p = 0 := by
        have := congrArg Subtype.val hp
        rw [hf, coe_evalAdjoin] at this
        exact this
      exact (hker p).1 hp'⟩
  refine ⟨f.liftOfSurjective hsurj g, ?_, ?_⟩
  · intro s t hst
    obtain ⟨p, rfl⟩ := hsurj s
    obtain ⟨q, rfl⟩ := hsurj t
    have h1 : FreeAlgebra.lift ℤ c p = FreeAlgebra.lift ℤ c q := by
      have hp := f.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hsurj) g p
      have hq := f.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hsurj) g q
      simp only [RingHom.liftOfSurjective] at hst
      rw [hp, hq] at hst
      exact hst
    have h2 : FreeAlgebra.lift ℤ a (p - q) = 0 := by
      rw [hker, map_sub, h1, sub_self]
    apply Subtype.ext
    rw [coe_evalAdjoin, coe_evalAdjoin, ← sub_eq_zero, ← map_sub, h2]
  · intro i
    rw [← evalAdjoin_ι, ← hf]
    simp only [RingHom.liftOfSurjective]
    rw [f.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hsurj) g]
    show FreeAlgebra.lift ℤ c (FreeAlgebra.ι ℤ i) = c i
    exact FreeAlgebra.lift_ι_apply c i

end KernelTransfer

section Unop

variable {T B : Type*} [Ring T] [Ring B]

def unopHom (ρ : T →+* Bᵐᵒᵖ) (hT : ∀ s t : T, s * t = t * s) : T →+* B where
  toFun t := MulOpposite.unop (ρ t)
  map_one' := by rw [map_one, MulOpposite.unop_one]
  map_mul' s t := by rw [hT s t, map_mul, MulOpposite.unop_mul]
  map_zero' := by rw [map_zero, MulOpposite.unop_zero]
  map_add' s t := by rw [map_add, MulOpposite.unop_add]

@[scoped simp] theorem unopHom_apply (ρ : T →+* Bᵐᵒᵖ) (hT : ∀ s t : T, s * t = t * s) (t : T) :
    unopHom ρ hT t = MulOpposite.unop (ρ t) := rfl

theorem unopHom_injective (ρ : T →+* Bᵐᵒᵖ) (hT : ∀ s t : T, s * t = t * s)
    (hρ : Function.Injective ρ) : Function.Injective (unopHom ρ hT) :=
  fun _ _ h => hρ (MulOpposite.unop_injective h)

end Unop

section Conj

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {E : Type*} [Field E] [Algebra K E]
variable {W : Type*} [AddCommGroup W] [Module E W]

noncomputable def conjBaseChange (e : E ⊗[K] V ≃ₗ[E] W) : Module.End K V →+* Module.End E W where
  toFun f := e.toLinearMap ∘ₗ f.baseChange E ∘ₗ e.symm.toLinearMap
  map_one' := by
    rw [LinearMap.baseChange_one]
    ext w
    simp
  map_mul' f g := by
    rw [LinearMap.baseChange_mul]
    ext w
    simp
  map_zero' := by
    rw [LinearMap.baseChange_zero]
    ext w
    simp
  map_add' f g := by
    rw [LinearMap.baseChange_add]
    ext w
    simp

theorem conjBaseChange_apply (e : E ⊗[K] V ≃ₗ[E] W) (f : Module.End K V) (w : W) :
    conjBaseChange e f w = e (f.baseChange E (e.symm w)) := rfl

theorem tmul_one_injective : Function.Injective (fun v : V => (1 : E) ⊗ₜ[K] v) := by
  have hinj : LinearMap.ker (Algebra.linearMap K E) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (algebraMap K E).injective
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K E) hinj
  have hlam1 : lam 1 = 1 := by
    have := LinearMap.congr_fun hlam 1
    simpa using this
  let r : E ⊗[K] V →ₗ[K] V := (TensorProduct.lid K V).toLinearMap ∘ₗ lam.rTensor V
  have hr : ∀ v : V, r ((1 : E) ⊗ₜ[K] v) = v := fun v => by
    simp [r, LinearMap.rTensor_tmul, hlam1]
  intro v w h
  have := congrArg r h
  simpa [hr] using this

variable (E) in
theorem baseChange_injective : Function.Injective (fun f : Module.End K V => f.baseChange E) := by
  intro f g h
  ext v
  have := LinearMap.congr_fun h ((1 : E) ⊗ₜ[K] v)
  simp only [LinearMap.baseChange_tmul] at this
  exact tmul_one_injective this

theorem conjBaseChange_injective (e : E ⊗[K] V ≃ₗ[E] W) :
    Function.Injective (conjBaseChange e) := by
  intro f g h
  apply baseChange_injective E
  refine LinearMap.ext fun x => ?_
  have := LinearMap.congr_fun h (e x)
  simp only [conjBaseChange_apply, LinearEquiv.symm_apply_apply] at this
  exact e.injective this

theorem conjBaseChange_eq_of_tmul (e : E ⊗[K] V ≃ₗ[E] W) (f : Module.End K V) (T : Module.End E W)
    (h : ∀ v : V, e ((1 : E) ⊗ₜ[K] f v) = T (e ((1 : E) ⊗ₜ[K] v))) :
    conjBaseChange e f = T := by
  have key : e.toLinearMap ∘ₗ f.baseChange E = T ∘ₗ e.toLinearMap := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
        have hc : c ⊗ₜ[K] v = c • ((1 : E) ⊗ₜ[K] v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [hc, map_smul, map_smul, map_smul, LinearMap.baseChange_tmul, h v, map_smul]
    | add x y hx hy =>
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_add] at hx hy ⊢
        rw [hx, hy]
  ext w
  have := LinearMap.congr_fun key (e.symm w)
  simpa [conjBaseChange_apply] using this

end Conj

end A1UG1COT
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff.A1UG1COT"

namespace A1UG1COT

namespace Bridge

open AlgebraicCurve
open scoped Pointwise

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isIntegral_algEquiv (σ : F ≃ₐ[K] F) : (σ : F →ₐ[K] F).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ σ.surjective

theorem isIntegral_id : (AlgHom.id K F).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ Function.surjective_id

theorem finiteAlong_algEquiv (σ : F ≃ₐ[K] F) : FiniteAlong K (σ : F →ₐ[K] F) := by
  unfold FiniteAlong
  exact RingHom.Finite.of_surjective _ σ.surjective

theorem finiteAlong_id : FiniteAlong K (AlgHom.id K F) := by
  unfold FiniteAlong
  exact RingHom.Finite.of_surjective _ Function.surjective_id

theorem separableAlong_of_surjective [CharZero F] (φ : F →ₐ[K] F)
    (hφ : Function.Surjective φ) : SeparableAlong K φ := by
  unfold SeparableAlong
  letI := algebraAlong φ
  haveI : Algebra.IsIntegral F F := isIntegral_along φ (RingHom.isIntegral_of_surjective _ hφ)
  exact Algebra.IsSeparable.of_integral F F

theorem separableAlong_algEquiv [CharZero F] (σ : F ≃ₐ[K] F) : SeparableAlong K (σ : F →ₐ[K] F) :=
  separableAlong_of_surjective _ σ.surjective

theorem separableAlong_id [CharZero F] : SeparableAlong K (AlgHom.id K F) :=
  separableAlong_of_surjective _ Function.surjective_id

theorem restrictAlong_algEquiv (σ : F ≃ₐ[K] F) (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral)
    (w : Place K F) :
    w.restrictAlong (σ : F →ₐ[K] F) hσ = (SemilinearAut.ofAlgAut σ)⁻¹ • w := by
  apply Place.ext
  ext x
  show x ∈ w.toValuationSubring.comap (σ : F →ₐ[K] F).toRingHom ↔
    x ∈ (SemilinearAut.ofAlgAut σ)⁻¹ • w.toValuationSubring
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_inv_pointwise_smul_iff,
    SemilinearAut.ofAlgAut_smul]
  rfl

theorem restrictAlong_id (hid : (AlgHom.id K F).toRingHom.IsIntegral) (w : Place K F) :
    w.restrictAlong (AlgHom.id K F) hid = w := by
  apply Place.ext
  ext x
  show x ∈ w.toValuationSubring.comap (AlgHom.id K F).toRingHom ↔ x ∈ w.toValuationSubring
  rw [ValuationSubring.mem_comap]
  rfl

theorem ramificationIndexAlong_algEquiv (σ : F ≃ₐ[K] F) (w : Place K F) :
    w.ramificationIndexAlong (σ : F →ₐ[K] F) = 1 := by
  letI := algebraAlong (σ : F →ₐ[K] F)
  show sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F f) = n} = 1
  set S : Set ℕ := {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F f) = n} with hS
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ1 : w.ord (π : F) = 1 := w.ord_coe_irreducible hπ
  have hπ0 : (π : F) ≠ 0 := by
    intro h
    rw [h, Place.ord_zero] at hπ1
    exact zero_ne_one hπ1
  have h1 : (1 : ℕ) ∈ S := by
    refine ⟨Nat.one_pos, σ.symm (π : F), by simpa using hπ0, ?_⟩
    show w.ord (σ (σ.symm (π : F))) = 1
    rw [AlgEquiv.apply_symm_apply, hπ1]
  have hle : sInf S ≤ 1 := Nat.sInf_le h1
  have hmem : sInf S ∈ S := Nat.sInf_mem ⟨1, h1⟩
  have hpos : 0 < sInf S := hmem.1
  omega

theorem inertiaDegAlong_id (hid : (AlgHom.id K F).toRingHom.IsIntegral) (w : Place K F) :
    w.inertiaDegAlong (AlgHom.id K F) hid = 1 := by
  letI := algebraAlong (AlgHom.id K F)
  haveI := isScalarTower_along (AlgHom.id K F)
  haveI := isIntegral_along (AlgHom.id K F) hid
  show Module.finrank (w.restrict F).ResidueField w.ResidueField = 1

  have hsurj : Function.Surjective (Place.restrictResidueMap F w) := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    have hb : (b : F) ∈ (w.restrict F).toValuationSubring := by
      rw [Place.mem_restrict_iff]
      exact b.2
    refine ⟨IsLocalRing.residue _ ⟨(b : F), hb⟩, ?_⟩
    rw [Place.restrictResidueMap_residue]
    exact congrArg _ (Subtype.ext rfl)
  have hmap : Function.Bijective (algebraMap (w.restrict F).ResidueField w.ResidueField) := by

    have key : algebraMap (w.restrict F).ResidueField w.ResidueField =
        Place.restrictResidueMap F w := by
      first
        | exact Place.algebraMap_residueField_eq
        | rfl
    rw [key]
    exact ⟨(Place.restrictResidueMap F w).injective, hsurj⟩
  let e : (w.restrict F).ResidueField ≃ₗ[(w.restrict F).ResidueField] w.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) hmap
  rw [← e.finrank_eq, Module.finrank_self]

theorem pullbackAlong_algEquiv [HasPrincipalDivisors K F] (σ : F ≃ₐ[K] F)
    (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong (σ : F →ₐ[K] F) hσ D = SemilinearAut.ofAlgAut σ • D := by
  ext w
  rw [Divisor.pullbackAlong_apply, ramificationIndexAlong_algEquiv, restrictAlong_algEquiv,
    SemilinearAut.divisor_smul_apply, Nat.cast_one, one_mul]

theorem pushforwardAlong_id (hid : (AlgHom.id K F).toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pushforwardAlong (AlgHom.id K F) hid D = D := by
  induction D using Finsupp.induction with
  | zero => exact map_zero _
  | single_add v n D _ _ ih =>
      rw [map_add, ih, Divisor.pushforwardAlong_single, restrictAlong_id, inertiaDegAlong_id,
        Nat.cast_one, mul_one]

theorem pic0_correspondence_algEquiv_id [HasPrincipalDivisors K F] (σ : F ≃ₐ[K] F)
    (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral) (hid : (AlgHom.id K F).toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K (σ : F →ₐ[K] F) hσ)
    (hfin : FiniteAlong K (AlgHom.id K F)) (hN : NormFormulaAlong K (AlgHom.id K F) hfin)
    (c : Pic0 K F) :
    Pic0.correspondence (σ : F →ₐ[K] F) (AlgHom.id K F) hσ hid hFI hfin hN c =
      SemilinearAut.ofAlgAut σ • c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [Pic0.correspondence_mk, SemilinearAut.pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [Pic0.coe_degZeroCorrespondence, SemilinearAut.coe_degZeroSMulHom,
    Divisor.correspondence_apply, pullbackAlong_algEquiv, pushforwardAlong_id]

end Bridge
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff.A1UG1COT"

end A1UG1COT
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff.A1UG1COT"

namespace A1UG1COT

p2m_open "ModularCurve~IsCusp AlgebraicCurve CongruenceSubgroup"
open scoped TensorProduct MatrixGroups

section Family

variable (M : ℕ)

local notation "ℚ̄" => AlgebraicClosure ℚ

abbrev FX : Type := ↥(x1FunctionFieldBar M)

abbrev Fup (ℓ : Nat.Primes) : Type := ↥(laurentBaseChange ℚ̄ (x1x0FunctionFieldC ℚ M (M * ℓ)))

abbrev Fam (i : Nat.Primes ⊕ ℕ) : Type :=
  @Sum.rec Nat.Primes ℕ (fun _ => Type) (fun ℓ => Fup M ℓ) (fun _ => FX M) i

scoped instance instFieldFam : (i : Nat.Primes ⊕ ℕ) → Field (Fam M i) :=
  @Sum.rec Nat.Primes ℕ (fun i => Field (Fam M i)) (fun _ => inferInstance) (fun _ => inferInstance)

scoped instance instAlgebraFam : (i : Nat.Primes ⊕ ℕ) → Algebra ℚ̄ (Fam M i) :=
  @Sum.rec Nat.Primes ℕ (fun i => Algebra ℚ̄ (Fam M i)) (fun _ => inferInstance) (fun _ => inferInstance)

theorem neZero_prime (ℓ : Nat.Primes) : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩

abbrev legβ (ℓ : Nat.Primes) : FX M →ₐ[ℚ̄] Fup M ℓ :=
  haveI := neZero_prime ℓ; heckeBetaOneBar ℚ̄ M ℓ

abbrev legα (ℓ : Nat.Primes) : FX M →ₐ[ℚ̄] Fup M ℓ :=
  haveI := neZero_prime ℓ; heckeAlphaOneBar ℚ̄ M ℓ

abbrev legσ (d : ℕ) : FX M →ₐ[ℚ̄] FX M := (diamondAutBar M d : FX M →ₐ[ℚ̄] FX M)

abbrev legφ : (i : Nat.Primes ⊕ ℕ) → (FX M →ₐ[ℚ̄] Fam M i) :=
  @Sum.rec Nat.Primes ℕ (fun i => FX M →ₐ[ℚ̄] Fam M i) (fun ℓ => legβ M ℓ) (fun d => legσ M d)

abbrev legψ : (i : Nat.Primes ⊕ ℕ) → (FX M →ₐ[ℚ̄] Fam M i) :=
  @Sum.rec Nat.Primes ℕ (fun i => FX M →ₐ[ℚ̄] Fam M i) (fun ℓ => legα M ℓ)
    (fun _ => AlgHom.id ℚ̄ (FX M))

end Family
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff.A1UG1COT"

section Curve

variable (M : ℕ) [NeZero M]

local notation "ℚ̄" => AlgebraicClosure ℚ

omit [NeZero M] in

theorem T_mem_inf (t : ℕ) : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 t := by
  refine ⟨?_, ?_⟩
  · simp [Gamma1_mem, ModularGroup.T]
  · simp [Gamma0_mem, ModularGroup.T]

omit [NeZero M] in
theorem T_mem : ModularGroup.T ∈ Gamma1 M := (T_mem_inf M 1).1

theorem hfg : ∃ x : FX M, Transcendental ℚ̄ x ∧
    FiniteDimensional (IntermediateField.adjoin ℚ̄ ({x} : Set (FX M))) (FX M) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℚ̄ (Gamma1 M) (T_mem M)

theorem isCurveOver_FX : IsCurveOver ℚ̄ (FX M) := by
  obtain ⟨x, hx, hfin⟩ := hfg M
  haveI := hfin
  exact AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx

theorem isCurveOver_Fup (ℓ : Nat.Primes) : IsCurveOver ℚ̄ (Fup M ℓ) := by
  haveI : NeZero (M * (ℓ : ℕ)) := ⟨mul_ne_zero (NeZero.ne M) ℓ.2.ne_zero⟩
  haveI : (Gamma1 M ⊓ Gamma0 (M * (ℓ : ℕ))).FiniteIndex := inferInstance
  obtain ⟨x, hx, hfin⟩ :
      ∃ x : Fup M ℓ, Transcendental ℚ̄ x ∧
        FiniteDimensional (IntermediateField.adjoin ℚ̄ ({x} : Set (Fup M ℓ))) (Fup M ℓ) :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℚ̄
      (Gamma1 M ⊓ Gamma0 (M * (ℓ : ℕ))) (T_mem_inf M _)
  haveI := hfin
  exact AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx

theorem isCurveOver_Fam : ∀ i : Nat.Primes ⊕ ℕ, IsCurveOver ℚ̄ (Fam M i)
  | Sum.inl ℓ => isCurveOver_Fup M ℓ
  | Sum.inr _ => isCurveOver_FX M

omit [NeZero M] in

theorem charZero_FX : CharZero (FX M) :=
  charZero_of_injective_algebraMap (algebraMap ℚ̄ (FX M)).injective

end Curve
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff.A1UG1COT"

section Witnesses

variable {M : ℕ} [NeZero M]

local notation "ℚ̄" => AlgebraicClosure ℚ

omit [NeZero M] in
theorem hin_hecke (hin : HeckeDiamondInputsAll M) (ℓ : Nat.Primes) :
    haveI := neZero_prime ℓ; HeckeInputsOneAlong ℚ̄ M ℓ := hin.1 ℓ

omit [NeZero M] in
theorem h0 (hin : HeckeDiamondInputsAll M) (ℓ : Nat.Primes) :
    haveI := neZero_prime ℓ; HeckeBetaOneDefined M ℓ := (hin_hecke hin ℓ).fst
omit [NeZero M] in
theorem hα (hin : HeckeDiamondInputsAll M) (ℓ : Nat.Primes) :
    haveI := neZero_prime ℓ; HeckeAlphaOneBarIntegral ℚ̄ M ℓ := (hin_hecke hin ℓ).snd.fst
omit [NeZero M] in
theorem hβ (hin : HeckeDiamondInputsAll M) (ℓ : Nat.Primes) :
    haveI := neZero_prime ℓ; HeckeBetaOneBarIntegral ℚ̄ M ℓ := (hin_hecke hin ℓ).snd.snd.fst
omit [NeZero M] in
theorem hPup (hin : HeckeDiamondInputsAll M) (ℓ : Nat.Primes) :
    HasPrincipalDivisors ℚ̄ (Fup M ℓ) := (hin_hecke hin ℓ).snd.snd.snd.fst
omit [NeZero M] in
theorem hfinα (hin : HeckeDiamondInputsAll M) (ℓ : Nat.Primes) :
    FiniteAlong ℚ̄ (legα M ℓ) := (hin_hecke hin ℓ).snd.snd.snd.snd.fst
omit [NeZero M] in
theorem hFIβ (hin : HeckeDiamondInputsAll M) (ℓ : Nat.Primes) :
    haveI := hPup hin ℓ
    FundamentalIdentityAlong ℚ̄ (legβ M ℓ) (hβ hin ℓ) := (hin_hecke hin ℓ).snd.snd.snd.snd.snd.1
omit [NeZero M] in
theorem hNFα (hin : HeckeDiamondInputsAll M) (ℓ : Nat.Primes) :
    NormFormulaAlong ℚ̄ (legα M ℓ) (hfinα hin ℓ) := (hin_hecke hin ℓ).snd.snd.snd.snd.snd.2

theorem hP (hin : HeckeDiamondInputsAll M) : ∀ i : Nat.Primes ⊕ ℕ, HasPrincipalDivisors ℚ̄ (Fam M i)
  | Sum.inl ℓ => hPup hin ℓ
  | Sum.inr _ => (isCurveOver_FX M).toHasPrincipalDivisors

omit [NeZero M] in
theorem hφ (hin : HeckeDiamondInputsAll M) :
    ∀ i : Nat.Primes ⊕ ℕ, (legφ M i).toRingHom.IsIntegral
  | Sum.inl ℓ => hβ hin ℓ
  | Sum.inr d => Bridge.isIntegral_algEquiv (diamondAutBar M d)

omit [NeZero M] in
theorem hψ (hin : HeckeDiamondInputsAll M) :
    ∀ i : Nat.Primes ⊕ ℕ, (legψ M i).toRingHom.IsIntegral
  | Sum.inl ℓ => hα hin ℓ
  | Sum.inr _ => Bridge.isIntegral_id

omit [NeZero M] in
theorem hfin (hin : HeckeDiamondInputsAll M) : ∀ i : Nat.Primes ⊕ ℕ, FiniteAlong ℚ̄ (legψ M i)
  | Sum.inl ℓ => hfinα hin ℓ
  | Sum.inr _ => Bridge.finiteAlong_id

theorem hFI (hin : HeckeDiamondInputsAll M) :
    ∀ i : Nat.Primes ⊕ ℕ, haveI := hP hin i; FundamentalIdentityAlong ℚ̄ (legφ M i) (hφ hin i)
  | Sum.inl ℓ => hFIβ hin ℓ
  | Sum.inr d => by
      haveI := hP hin (Sum.inr d)
      haveI := charZero_FX M
      exact AlgebraicCurve.fundamentalIdentityAlong _ _ (Bridge.finiteAlong_algEquiv _)
        (Bridge.separableAlong_algEquiv _)

theorem hNF (hin : HeckeDiamondInputsAll M) :
    ∀ i : Nat.Primes ⊕ ℕ, haveI := hP hin i; NormFormulaAlong ℚ̄ (legψ M i) (hfin hin i)
  | Sum.inl ℓ => hNFα hin ℓ
  | Sum.inr d => by
      haveI := hP hin (Sum.inr d)
      haveI := charZero_FX M
      exact AlgebraicCurve.normFormulaAlong _ _ Bridge.separableAlong_id

theorem heckeDiamondGenBar_eq_correspondence (hin : HeckeDiamondInputsAll M) :
    heckeDiamondGenBar M = fun i =>
      (haveI := hP hin i
       (Pic0.correspondence (legφ M i) (legψ M i) (hφ hin i) (hψ hin i) (hFI hin i) (hfin hin i)
          (hNF hin i)).toIntLinearMap) := by
  funext i
  cases i with
  | inl ℓ =>
      haveI := neZero_prime ℓ
      haveI := hPup hin ℓ
      show (heckeOperatorOneAlong ℚ̄ M ℓ).toIntLinearMap = _
      rw [heckeOperatorOneAlong_eq (h0 hin ℓ) (hα hin ℓ) (hβ hin ℓ) (hFIβ hin ℓ) (hfinα hin ℓ)
        (hNFα hin ℓ)]
      rfl
  | inr d =>
      haveI := hP hin (Sum.inr d)
      refine LinearMap.ext fun c => ?_
      show diamondOneBar M d c = Pic0.correspondence (legσ M d) (AlgHom.id ℚ̄ (FX M))
        (hφ hin (Sum.inr d)) (hψ hin (Sum.inr d)) (hFI hin (Sum.inr d)) (hfin hin (Sum.inr d))
        (hNF hin (Sum.inr d)) c
      rw [diamondOneBar_apply, Bridge.pic0_correspondence_algEquiv_id]

end Witnesses
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff.A1UG1COT"

section Cotangent

variable {M : ℕ} [NeZero M]

local notation "ℚ̄" => AlgebraicClosure ℚ

abbrev RegX (M : ℕ) : Submodule ℚ̄ Ω[FX M⁄ℚ̄] := regularDifferentials ℚ̄ (FX M)

abbrev Θ (M : ℕ) : Ω[FX M⁄ℚ̄] →ₗ[FX M] LaurentSeries ℚ̄ := diffQExp (x1FunctionFieldBar M)

abbrev cDiff (M : ℕ) (i : Nat.Primes ⊕ ℕ) : Ω[FX M⁄ℚ̄] →ₗ[ℚ̄] Ω[FX M⁄ℚ̄] :=
  Differential.correspondence (legφ M i) (legψ M i)

theorem cDiff_mem (hin : HeckeDiamondInputsAll M) (i : Nat.Primes ⊕ ℕ) :
    ∀ ω ∈ RegX M, cDiff M i ω ∈ RegX M := by
  intro ω hω
  haveI : IsCurveOver ℚ̄ (FX M) := isCurveOver_FX M
  haveI : IsCurveOver ℚ̄ (Fam M i) := isCurveOver_Fam M i
  exact AlgebraicCurve.Differential.correspondence_mem_regularDifferentials ℚ̄ (FX M) (Fam M i)
    (hfg M) (legφ M i) (legψ M i) (hφ hin i) (hψ hin i) (hfin hin i) hω

def cRes (hin : HeckeDiamondInputsAll M) (i : Nat.Primes ⊕ ℕ) : (Module.End ℚ̄ ↥(RegX M))ᵐᵒᵖ :=
  MulOpposite.op ((cDiff M i).restrict (cDiff_mem hin i))

theorem restrict_lift (hin : HeckeDiamondInputsAll M) (p : FreeAlgebra ℤ (Nat.Primes ⊕ ℕ))
    (v : ↥(RegX M)) :
    ((MulOpposite.unop (FreeAlgebra.lift ℤ (cRes hin) p) v : ↥(RegX M)) : Ω[FX M⁄ℚ̄]) =
      MulOpposite.unop (FreeAlgebra.lift ℤ (fun i => MulOpposite.op (cDiff M i)) p)
        (v : Ω[FX M⁄ℚ̄]) := by
  induction p using FreeAlgebra.induction generalizing v with
  | grade0 r =>
      rw [AlgHom.commutes, AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op,
        MulOpposite.algebraMap_apply, MulOpposite.unop_op, eq_intCast, eq_intCast,
        Module.End.intCast_apply, Module.End.intCast_apply, Submodule.coe_smul_of_tower]
  | grade1 i =>
      simp only [FreeAlgebra.lift_ι_apply, cRes, MulOpposite.unop_op, LinearMap.coe_restrict_apply]
  | mul a b ha hb =>
      simp only [map_mul, MulOpposite.unop_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
      simp only [map_add, MulOpposite.unop_add, LinearMap.add_apply, Submodule.coe_add, ha, hb]

theorem ker_iff (hin : HeckeDiamondInputsAll M) (p : FreeAlgebra ℤ (Nat.Primes ⊕ ℕ)) :
    FreeAlgebra.lift ℤ (heckeDiamondGenBar M) p = 0 ↔ FreeAlgebra.lift ℤ (cRes hin) p = 0 := by
  haveI : IsCurveOver ℚ̄ (FX M) := isCurveOver_FX M
  haveI : ∀ i : Nat.Primes ⊕ ℕ, HasPrincipalDivisors ℚ̄ (Fam M i) := hP hin
  rw [heckeDiamondGenBar_eq_correspondence hin]
  constructor
  · intro hp
    have hW := AlgebraicCurve.Pic0.freeAlgebra_lift_differential_eq_zero_of_lift_correspondence_eq_zero
      ℚ̄ (FX M) (hfg M) (Fam M) (legφ M) (legψ M) (hφ hin) (hψ hin) (hFI hin)
      (hfin hin) (hNF hin) p hp
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [restrict_lift hin p v, MulOpposite.unop_zero, LinearMap.zero_apply, Submodule.coe_zero]
    exact hW v v.2
  · intro hp
    refine AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero
      ℚ̄ (FX M) (hfg M) (Fam M) (legφ M) (legψ M) (hφ hin) (hψ hin) (hFI hin)
      (hfin hin) (hNF hin) p ?_
    intro ω hω
    have := restrict_lift hin p ⟨ω, hω⟩
    rw [hp, MulOpposite.unop_zero, LinearMap.zero_apply, Submodule.coe_zero] at this
    exact this.symm

end Cotangent
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff.A1UG1COT"

section QExp

open ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped ModularForm

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem cusp_periodic (F : CuspForm (Γ₁ℝ M) k) : Periodic (⇑F ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex F (one_mem_strictPeriods M)

theorem cusp_holo (F : CuspForm (Γ₁ℝ M) k) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'

theorem cusp_bdd (F : CuspForm (Γ₁ℝ M) k) : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ M)) :=
    ⟨(Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  exact ModularFormClass.bdd_at_infty F

theorem cusp_ext_of_qCoeff {F G : CuspForm (Γ₁ℝ M) k} (h : ∀ n : ℕ, qCoeff (⇑F) n = qCoeff (⇑G) n) :
    F = G :=
  DFunLike.coe_injective (UpperHalfPlane.eq_of_forall_qCoeff_eq (cusp_periodic F) (cusp_holo F)
    (cusp_bdd F) (cusp_periodic G) (cusp_holo G) (cusp_bdd G) h)

theorem cusp_ext_of_ofPowerSeries {F G : CuspForm (Γ₁ℝ M) k}
    (h : HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑F) =
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑G)) : F = G := by
  have h' : qExpansion 1 ⇑F = qExpansion 1 ⇑G := HahnSeries.ofPowerSeries_injective h
  exact cusp_ext_of_qCoeff fun n => by rw [qCoeff, qCoeff, h']

theorem analyticAt_cuspFunction' (F : CuspForm (Γ₁ℝ M) k) : AnalyticAt ℂ (cuspFunction 1 (⇑F)) 0 :=
  analyticAt_cuspFunction_zero one_pos (cusp_periodic F) (cusp_holo F) (cusp_bdd F)

theorem qCoeff_smul' (c : ℂ) (F : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(c • F)) n = c * qCoeff (⇑F) n := by
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul (analyticAt_cuspFunction' F) c, map_smul,
    smul_eq_mul]

theorem qCoeff_add' (F G : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(F + G)) n = qCoeff (⇑F) n + qCoeff (⇑G) n := by
  rw [qCoeff, qCoeff, qCoeff, CuspForm.coe_add,
    qExpansion_add (analyticAt_cuspFunction' F) (analyticAt_cuspFunction' G), map_add]

theorem qCoeff_zero'' (n : ℕ) : qCoeff (⇑(0 : CuspForm (Γ₁ℝ M) k)) n = 0 := by
  rw [qCoeff, CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]

end QExp
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff.A1UG1COT"

section Values

variable {M : ℕ} [NeZero M]

local notation "ℚ̄" => AlgebraicClosure ℚ

open ModularFormClass

def emb : ℚ̄ →+* ℂ :=
  haveI : Algebra.IsAlgebraic ℚ ℚ̄ := by convert AlgebraicClosure.isAlgebraic ℚ <;> first | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
  (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := ℚ̄)).toRingHom

structure Dict (M : ℕ) [NeZero M] where

  e : letI := (emb).toAlgebra
    ℂ ⊗[ℚ̄] ↥(RegX M) ≃ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma1 M) 2

  he : letI := (emb).toAlgebra
    ∀ ω : ↥(RegX M), coeffMap emb (Θ M (ω : Ω[FX M⁄ℚ̄])) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(e (1 ⊗ₜ ω)))

def dict (M : ℕ) [NeZero M] : Dict M :=
  ⟨(ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm M emb).choose,
    (ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm M
      emb).choose_spec⟩

theorem qCoeff_dict (D : Dict M) (ω : ↥(RegX M)) (n : ℕ) :
    letI := (emb).toAlgebra
    qCoeff (⇑(D.e ((1 : ℂ) ⊗ₜ[ℚ̄] ω))) n = emb ((Θ M (ω : Ω[FX M⁄ℚ̄])).coeff n) := by
  letI := (emb).toAlgebra
  have h := congrArg (fun x : LaurentSeries ℂ => x.coeff (n : ℤ)) (D.he ω)
  simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] at h
  rw [qCoeff]
  exact h.symm

omit [NeZero M] in

theorem hdia (hin : HeckeDiamondInputsAll M) {d : ℕ} (hd : d.Coprime M) :
    (∃ σ : ↥(x1FunctionField M) ≃ₐ[ℚ] ↥(x1FunctionField M), IsDiamondAut M d σ) ∧
      ∃ σ' : ↥(x1FunctionFieldBar M) ≃ₐ[ℚ̄] ↥(x1FunctionFieldBar M),
        IsBaseChangeAutOf ℚ̄ (diamondAut M d) σ' :=
  hin.2 d hd

theorem tmul_value_diamond (hin : HeckeDiamondInputsAll M) (D : Dict M) {d : ℕ} (hd : d.Coprime M)
    (v : ↥(RegX M)) :
    letI := (emb).toAlgebra
    D.e ((1 : ℂ) ⊗ₜ[ℚ̄] ((cDiff M (Sum.inr d)).restrict (cDiff_mem hin (Sum.inr d)) v)) =
      CuspForm.diamondLinOne M 2 d (D.e ((1 : ℂ) ⊗ₜ[ℚ̄] v)) := by
  letI := (emb).toAlgebra
  apply cusp_ext_of_ofPowerSeries
  rw [← D.he]
  exact ModularCurve.coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne M
    (hdia hin hd).1 (hdia hin hd).2 emb (v : Ω[FX M⁄ℚ̄]) _ (D.he v)

theorem tmul_value_hecke (hin : HeckeDiamondInputsAll M) (D : Dict M) (ℓ : Nat.Primes)
    (hℓM : ¬ (ℓ : ℕ) ∣ M) (v : ↥(RegX M)) :
    letI := (emb).toAlgebra
    D.e ((1 : ℂ) ⊗ₜ[ℚ̄] ((cDiff M (Sum.inl ℓ)).restrict (cDiff_mem hin (Sum.inl ℓ)) v)) =
      CuspForm.heckeTLinOne 2 ℓ.prop hℓM (D.e ((1 : ℂ) ⊗ₜ[ℚ̄] v)) := by
  letI := (emb).toAlgebra
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hcop : Nat.Coprime (ℓ : ℕ) M := (Nat.Prime.coprime_iff_not_dvd ℓ.2).mpr hℓM

  have hdiam := tmul_value_diamond hin D hcop v
  apply cusp_ext_of_qCoeff
  intro n
  rw [qCoeff_dict, LinearMap.coe_restrict_apply, CuspForm.qCoeff_heckeTLinOne, qCoeff_dict]

  have hT : (Θ M (cDiff M (Sum.inl ℓ) (v : Ω[FX M⁄ℚ̄]))).coeff (n : ℤ) =
      (Θ M (v : Ω[FX M⁄ℚ̄])).coeff (n * ℓ) + ((ℓ : ℕ) : ℚ̄) *
        (if ((ℓ : ℕ) : ℤ) ∣ (n : ℤ) then
          (Θ M (cDiff M (Sum.inr (ℓ : ℕ)) (v : Ω[FX M⁄ℚ̄]))).coeff ((n : ℤ) / (ℓ : ℕ)) else 0) :=
    ModularCurve.coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd M ℓ hℓM
      (h0 hin ℓ) (hdia hin hcop).1 (hdia hin hcop).2 (v : Ω[FX M⁄ℚ̄]) n
  rw [hT, map_add, map_mul, map_natCast]
  have h21 : ((2 : ℤ) - 1) = 1 := by norm_num
  rw [h21, zpow_one, Nat.cast_mul, mul_comm ((ℓ : ℕ) : ℤ) (n : ℤ)]
  congr 1
  by_cases hdvd : (ℓ : ℕ) ∣ n
  · have hdvd' : ((ℓ : ℕ) : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hdvd
    rw [if_pos hdvd', if_pos hdvd, ← hdiam, qCoeff_dict, LinearMap.coe_restrict_apply,
      Int.natCast_div]
  · have hdvd' : ¬ ((ℓ : ℕ) : ℤ) ∣ (n : ℤ) := fun h => hdvd (Int.natCast_dvd_natCast.mp h)
    rw [if_neg hdvd', if_neg hdvd, map_zero, mul_zero]

theorem tmul_value_heckeU (hin : HeckeDiamondInputsAll M) (D : Dict M) (ℓ : Nat.Primes)
    (hℓM : (ℓ : ℕ) ∣ M) (v : ↥(RegX M)) (n : ℕ) :
    letI := (emb).toAlgebra
    qCoeff (⇑(D.e ((1 : ℂ) ⊗ₜ[ℚ̄] ((cDiff M (Sum.inl ℓ)).restrict (cDiff_mem hin (Sum.inl ℓ)) v)))) n =
      qCoeff (⇑(D.e ((1 : ℂ) ⊗ₜ[ℚ̄] v))) (ℓ * n) := by
  letI := (emb).toAlgebra
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  rw [qCoeff_dict, LinearMap.coe_restrict_apply, qCoeff_dict]
  have hU : (Θ M (cDiff M (Sum.inl ℓ) (v : Ω[FX M⁄ℚ̄]))).coeff (n : ℤ) =
      (Θ M (v : Ω[FX M⁄ℚ̄])).coeff (n * ℓ) :=
    ModularCurve.coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_dvd M ℓ hℓM
      (h0 hin ℓ) (v : Ω[FX M⁄ℚ̄]) n
  rw [hU, Nat.cast_mul, mul_comm ((ℓ : ℕ) : ℤ) (n : ℤ)]

theorem heckeU_clause (hin : HeckeDiamondInputsAll M) (D : Dict M) (ℓ : Nat.Primes)
    (hℓM : (ℓ : ℕ) ∣ M) (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2) (n : ℕ) :
    letI := (emb).toAlgebra
    qCoeff (⇑(conjBaseChange D.e ((cDiff M (Sum.inl ℓ)).restrict (cDiff_mem hin (Sum.inl ℓ))) f)) n =
      qCoeff (⇑f) (ℓ * n) := by
  letI := (emb).toAlgebra
  set U := (cDiff M (Sum.inl ℓ)).restrict (cDiff_mem hin (Sum.inl ℓ)) with hUdef
  rw [conjBaseChange_apply]

  have key : ∀ x : ℂ ⊗[ℚ̄] ↥(RegX M),
      qCoeff (⇑(D.e (U.baseChange ℂ x))) n = qCoeff (⇑(D.e x)) (ℓ * n) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, qCoeff_zero'', qCoeff_zero'']
    | tmul c v =>
        have hc : c ⊗ₜ[ℚ̄] v = c • ((1 : ℂ) ⊗ₜ[ℚ̄] v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have hc' : c ⊗ₜ[ℚ̄] (U v) = c • ((1 : ℂ) ⊗ₜ[ℚ̄] (U v)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [LinearMap.baseChange_tmul, hc', hc, map_smul, map_smul, qCoeff_smul', qCoeff_smul',
          hUdef, tmul_value_heckeU hin D ℓ hℓM v n]
    | add x y hx hy =>
        rw [map_add, map_add, map_add, qCoeff_add', qCoeff_add', hx, hy]
  have h := key (D.e.symm f)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

end Values
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff.A1UG1COT"

end A1UG1COT
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff.A1UG1COT"

p2m_open "ModularCurve~IsCusp"

set_option maxHeartbeats 3200000 in
theorem solution (M : ℕ) [NeZero M]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M) :
    ∃ Φ : ↥(Algebra.adjoin ℤ (Set.range (ModularCurve.heckeDiamondGenBar M))) →+*
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2),
      Function.Injective Φ ∧
      (∀ (ℓ : Nat.Primes) (hℓM : ¬ (ℓ : ℕ) ∣ M),
        Φ ⟨ModularCurve.heckeOperatorOneBar M ℓ,
            Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩
          = CuspForm.heckeTLinOne 2 ℓ.prop hℓM) ∧
      (∀ (d : ℕ), Nat.Coprime d M →
        Φ ⟨ModularCurve.diamondOneBar M d,
            Algebra.subset_adjoin (Set.mem_range_self (Sum.inr d))⟩
          = CuspForm.diamondLinOne M 2 d) ∧
      ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ∣ M →
        ∀ (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2) (n : ℕ),
          ModularFormClass.qCoeff
              (Φ ⟨ModularCurve.heckeOperatorOneBar M ℓ,
                  Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩ f) n
            = ModularFormClass.qCoeff f (ℓ * n) := by
  classical
  letI : Algebra (AlgebraicClosure ℚ) ℂ := (A1UG1COT.emb).toAlgebra

  obtain ⟨ρ₀, hρ₀inj, hρ₀⟩ :=
    A1UG1COT.exists_ringHom_adjoin_of_ker_iff (heckeDiamondGenBar M) (A1UG1COT.cRes hin)
      (A1UG1COT.ker_iff hin)

  have hT : ∀ s t : ↥(Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))), s * t = t * s :=
    fun s t => (isMulCommutative_adjoin_heckeDiamondGenBar hcomm).is_comm.comm s t
  let ρ₁ := A1UG1COT.unopHom ρ₀ hT

  let D := A1UG1COT.dict M
  refine ⟨(A1UG1COT.conjBaseChange D.e).comp ρ₁, ?_, ?_, ?_, ?_⟩
  · exact (A1UG1COT.conjBaseChange_injective D.e).comp (A1UG1COT.unopHom_injective ρ₀ hT hρ₀inj)
  · intro ℓ hℓM
    show ((A1UG1COT.conjBaseChange D.e).comp ρ₁)
        ⟨heckeDiamondGenBar M (Sum.inl ℓ), Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩
      = _
    rw [RingHom.comp_apply, A1UG1COT.unopHom_apply, hρ₀ (Sum.inl ℓ), A1UG1COT.cRes,
      MulOpposite.unop_op]
    exact A1UG1COT.conjBaseChange_eq_of_tmul D.e _ _ (A1UG1COT.tmul_value_hecke hin D ℓ hℓM)
  · intro d hd
    show ((A1UG1COT.conjBaseChange D.e).comp ρ₁)
        ⟨heckeDiamondGenBar M (Sum.inr d), Algebra.subset_adjoin (Set.mem_range_self (Sum.inr d))⟩
      = _
    rw [RingHom.comp_apply, A1UG1COT.unopHom_apply, hρ₀ (Sum.inr d), A1UG1COT.cRes,
      MulOpposite.unop_op]
    exact A1UG1COT.conjBaseChange_eq_of_tmul D.e _ _ (A1UG1COT.tmul_value_diamond hin D hd)
  ·
    intro ℓ hℓM f n
    show ModularFormClass.qCoeff (⇑(((A1UG1COT.conjBaseChange D.e).comp ρ₁)
        ⟨heckeDiamondGenBar M (Sum.inl ℓ), Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩ f)) n
      = _
    rw [RingHom.comp_apply, A1UG1COT.unopHom_apply, hρ₀ (Sum.inl ℓ), A1UG1COT.cRes,
      MulOpposite.unop_op]
    exact A1UG1COT.heckeU_clause hin D ℓ hℓM f n

end
end S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff
end P2MW
export P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff (solution)
