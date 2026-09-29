-- Prove2me | solution 1 for ModularCurve.genusFF_xHFunctionFieldBar_le_finrank_cuspForm_gammaH_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/fb32222a-9748-5c84-8e58-11f2ae4d2355

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Theorems.Thm_ModularCurve_exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_finrank_cuspForm_gammaH_two
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

open ModularCurve AlgebraicCurve HahnSeries KaehlerDifferential
open scoped MatrixGroups

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace XHGenusLE

local notation "ℚb" => AlgebraicClosure ℚ

variable (Γ : Subgroup SL(2, ℤ))

abbrev Fb : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)

theorem jq_mem : jq ∈ qExpFunctionFieldC ℚ Γ :=
  intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ)

abbrev jB : Fb Γ :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem Γ)⟩

theorem coeffMap_qEuler {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s : LaurentSeries R) :
    coeffMap f (qEuler R s) = qEuler S (coeffMap f s) := by
  ext n
  simp [qEuler_coeff, coeffMap_coeff]

theorem qEuler_eq_thetaL (s : LaurentSeries ℂ) : qEuler ℂ s = thetaL ℂ s := by
  ext n
  rw [qEuler_coeff, thetaL_apply, ModularCurve.theta_coeff, zsmul_eq_mul]

theorem coeffMap_coeffEmb' (ι₀ : AlgebraicClosure ℚ →+* ℂ) (z : LaurentSeries ℚ) :
    coeffMap ι₀ (coeffEmb (AlgebraicClosure ℚ) z) = coeffEmb ℂ z := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) z

theorem coeffMap_coeffEmb_jq (ι₀ : AlgebraicClosure ℚ →+* ℂ) :
    coeffMap ι₀ (coeffEmb (AlgebraicClosure ℚ) jq) = jqModC ℂ := by
  rw [coeffEmb, coeffMap_coeffMap, ← jqModC_rat]
  exact map_jqModC _

theorem coeffMap_algebraMap' (ι₀ : AlgebraicClosure ℚ →+* ℂ) (c : AlgebraicClosure ℚ) :
    coeffMap ι₀ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c) =
      algebraMap ℂ (LaurentSeries ℂ) (ι₀ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_mem_laurentBaseChange_complex (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀) :
    coeffMap ι₀ x ∈ laurentBaseChange ℂ F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap']
        exact (laurentBaseChange ℂ F₀).algebraMap_mem _
      · rw [coeffMap_coeffEmb']
        exact coeffEmb_mem_laurentBaseChange ℂ hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

noncomputable def phi (ι₀ : AlgebraicClosure ℚ →+* ℂ) : Fb Γ →+* LaurentSeries ℂ :=
  (coeffMap ι₀).comp (Fb Γ).toSubfield.subtype

theorem phi_apply (ι₀ : AlgebraicClosure ℚ →+* ℂ) (x : Fb Γ) :
    phi Γ ι₀ x = coeffMap ι₀ (x : LaurentSeries (AlgebraicClosure ℚ)) := rfl

theorem phi_algebraMap (ι₀ : AlgebraicClosure ℚ →+* ℂ) (c : AlgebraicClosure ℚ) :
    phi Γ ι₀ (algebraMap (AlgebraicClosure ℚ) (Fb Γ) c) = algebraMap ℂ (LaurentSeries ℂ) (ι₀ c) := by
  rw [phi_apply]
  exact coeffMap_algebraMap' ι₀ c

theorem phi_jB (ι₀ : AlgebraicClosure ℚ →+* ℂ) : phi Γ ι₀ (jB Γ) = jqModC ℂ := by
  rw [phi_apply]
  exact coeffMap_coeffEmb_jq ι₀

theorem isIntegral_phi (ι₀ : AlgebraicClosure ℚ →+* ℂ) (a : Fb Γ) {y : Fb Γ}
    (hy : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (Fb Γ))) y) :
    IsIntegral (Algebra.adjoin ℂ ({phi Γ ι₀ a} : Set (LaurentSeries ℂ))) (phi Γ ι₀ y) := by
  have hmem : ∀ r : Fb Γ,
      r ∈ Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (Fb Γ)) →
      phi Γ ι₀ r ∈ Algebra.adjoin ℂ ({phi Γ ι₀ a} : Set (LaurentSeries ℂ)) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem r hr =>
        rw [Set.mem_singleton_iff] at hr
        subst hr
        exact Algebra.subset_adjoin (Set.mem_singleton _)
    | algebraMap c =>
        rw [phi_algebraMap]
        exact Subalgebra.algebraMap_mem _ _
    | add r s _ _ hr hs => rw [map_add]; exact add_mem hr hs
    | mul r s _ _ hr hs => rw [map_mul]; exact mul_mem hr hs
  let ψ : Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (Fb Γ)) →+*
      Algebra.adjoin ℂ ({phi Γ ι₀ a} : Set (LaurentSeries ℂ)) :=
    ((phi Γ ι₀).comp (Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (Fb Γ))).val.toRingHom).codRestrict
      (Algebra.adjoin ℂ ({phi Γ ι₀ a} : Set (LaurentSeries ℂ))) (fun r => hmem r r.2)
  refine IsIntegral.map_of_comp_eq ψ (phi Γ ι₀) ?_ hy
  ext r
  rfl

theorem D_jB_ne_zero : D (AlgebraicClosure ℚ) (Fb Γ) (jB Γ) ≠ 0 := by
  intro h
  have h1 : diffQExp (Fb Γ) (D (AlgebraicClosure ℚ) (Fb Γ) (jB Γ)) =
      qEuler (AlgebraicClosure ℚ) ((jB Γ : Fb Γ) : LaurentSeries (AlgebraicClosure ℚ)) :=
    diffQExp_D _ _
  rw [h, map_zero] at h1
  have h2 := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff (-1)) h1
  simp only at h2
  rw [qEuler_coeff] at h2
  have h3 : ((jB Γ : Fb Γ) : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1) = 1 := by
    show (coeffEmb (AlgebraicClosure ℚ) jq).coeff (-1) = 1
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]
  rw [h3, HahnSeries.coeff_zero] at h2
  norm_num at h2

theorem alg_transport (M : ℕ) [NeZero M]
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (F : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hF : F = qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)
    (jbar : ↥F) (hjbar : (jbar : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (x : ↥F) (hx : x • D (AlgebraicClosure ℚ) ↥F jbar ∈ regularDifferentials (AlgebraicClosure ℚ) ↥F) :
    IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥F))
        (x ^ 6 * jbar ^ 4 * (jbar - algebraMap (AlgebraicClosure ℚ) ↥F 1728) ^ 3) ∧
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({jbar⁻¹} : Set ↥F))
        (x ^ (2 * Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥F)) ↥F) *
          jbar ^ (Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥F)) ↥F + 1) *
          (jbar - algebraMap (AlgebraicClosure ℚ) ↥F 1728) ^
            Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥F)) ↥F) := by
  subst hF
  exact ModularCurve.isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC M Γ hΓ₁
    hΓ₀ jbar hjbar x hx

theorem Fb_eq : (Fb Γ : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) =
    qExpFunctionFieldC (AlgebraicClosure ℚ) Γ :=
  ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq (AlgebraicClosure ℚ) Γ

theorem coe_jB : ((jB Γ : Fb Γ) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
  show coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ)
  rw [coeffEmb, ← jqModC_rat]
  exact map_jqModC _

abbrev S2 : Type := CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2

theorem conv (M : ℕ) [NeZero M] [Γ.FiniteIndex]
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (hT : ModularGroup.T ∈ Γ) [IsCurveOver (AlgebraicClosure ℚ) (Fb Γ)]
    (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (ω : Ω[↥(Fb Γ)⁄AlgebraicClosure ℚ])
    (hω : ω ∈ regularDifferentials (AlgebraicClosure ℚ) ↥(Fb Γ)) :
    ∃ f : S2 Γ,
      coeffMap ι₀ (diffQExp (Fb Γ) ω) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) := by
  classical

  have hrank : Module.finrank (Fb Γ) Ω[Fb Γ⁄AlgebraicClosure ℚ] = 1 := IsCurveOver.finrank_kaehler
  obtain ⟨x, hx⟩ := (finrank_eq_one_iff_of_nonzero'
    (D (AlgebraicClosure ℚ) (Fb Γ) (jB Γ)) (D_jB_ne_zero Γ)).mp hrank ω

  have hxreg : x • D (AlgebraicClosure ℚ) (Fb Γ) (jB Γ) ∈
      regularDifferentials (AlgebraicClosure ℚ) (Fb Γ) := by
    rw [hx]; exact hω
  obtain ⟨h₁, h₂⟩ := alg_transport Γ M hΓ₁ hΓ₀ (Fb Γ) (Fb_eq Γ) (jB Γ) (coe_jB Γ) x hxreg

  have hXmem : phi Γ ι₀ x ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) :=
    coeffMap_mem_laurentBaseChange_complex ι₀ _ x.2
  have hJ : phi Γ ι₀ (jB Γ) = jqModC ℂ := phi_jB Γ ι₀
  have h1728 : phi Γ ι₀ (algebraMap (AlgebraicClosure ℚ) (Fb Γ) 1728) = algebraMap ℂ (LaurentSeries ℂ) 1728 := by
    rw [phi_algebraMap, map_ofNat]
  have h₁' := isIntegral_phi Γ ι₀ (jB Γ) h₁
  have h₂' := isIntegral_phi Γ ι₀ ((jB Γ)⁻¹) h₂
  rw [map_inv₀, hJ] at h₂'
  rw [hJ] at h₁'
  simp only [map_mul, map_pow, map_sub, hJ, h1728] at h₁' h₂'
  set n : ℕ := Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jB Γ} : Set (Fb Γ))) (Fb Γ) with hn

  have h₁'' : IsIntegral (Algebra.adjoin ℂ ({jqModC ℂ} : Set (LaurentSeries ℂ)))
      ((phi Γ ι₀ x) ^ 6 * jqModC ℂ ^ (4 * 1) * (jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * 1)) := by
    simpa only [mul_one] using h₁'
  have h₂'' : IsIntegral (Algebra.adjoin ℂ ({(jqModC ℂ)⁻¹} : Set (LaurentSeries ℂ)))
      ((phi Γ ι₀ x) ^ (2 * n) * jqModC ℂ ^ (1 * n + 1) * (jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (1 * n)) := by
    simpa only [one_mul] using h₂'
  obtain ⟨f, hf⟩ :=
    ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC
      Γ hT 1 le_rfl (phi Γ ι₀ x) hXmem n h₁'' h₂''
  refine ⟨f, ?_⟩

  have hΘ : diffQExp (Fb Γ) ω =
      ((x : Fb Γ) : LaurentSeries (AlgebraicClosure ℚ)) *
        qEuler (AlgebraicClosure ℚ) ((jB Γ : Fb Γ) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [← hx]
    exact diffQExp_smul_D _ _ _
  show coeffMap ι₀ (diffQExp (Fb Γ) ω) = _
  rw [hΘ, map_mul, coeffMap_qEuler, qEuler_eq_thetaL, ← phi_apply, ← phi_apply, hJ]
  rw [pow_one] at hf
  exact hf.symm

theorem exists_transcendental [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    ∃ x : Fb Γ, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (Fb Γ))) (Fb Γ) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) Γ hT

theorem isCurveOver_Fb [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) : IsCurveOver (AlgebraicClosure ℚ) (Fb Γ) := by
  obtain ⟨x, htr, hfd⟩ := exists_transcendental Γ hT
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd

theorem essFiniteType_Fb [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    Algebra.EssFiniteType (AlgebraicClosure ℚ) (Fb Γ) := by
  obtain ⟨x, htr, hfd⟩ := exists_transcendental Γ hT
  exact AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htr hfd

theorem finite_and_finrank_regularDifferentials_eq_genusFF [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    Module.Finite (AlgebraicClosure ℚ) ↥(regularDifferentials (AlgebraicClosure ℚ) (Fb Γ)) ∧
      Module.finrank (AlgebraicClosure ℚ) ↥(regularDifferentials (AlgebraicClosure ℚ) (Fb Γ)) =
        genusFF (AlgebraicClosure ℚ) (Fb Γ) := by
  obtain ⟨x, htr, hfd⟩ := exists_transcendental Γ hT
  haveI : IsCurveOver (AlgebraicClosure ℚ) (Fb Γ) := isCurveOver_Fb Γ hT
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (Fb Γ) := essFiniteType_Fb Γ hT
  haveI : HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := Fb Γ) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ v : Place (AlgebraicClosure ℚ) (Fb Γ), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  haveI := hfd
  have hC : ConstantsAreBase (AlgebraicClosure ℚ) (Fb Γ) :=
    AlgebraicCurve.constantsAreBase_of_isAlgClosed_of_transcendental x htr
  have hRR : FunctionFieldRiemannRoch (AlgebraicClosure ℚ) (Fb Γ) :=
    AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental htr hfd
  have hSG : StichtenothGenusExists (AlgebraicClosure ℚ) (Fb Γ) :=
    AlgebraicCurve.stichtenothGenusExists_of_isCurveOver hC
  have hWDA : WeilDualityAdelic (AlgebraicClosure ℚ) (Fb Γ) :=
    AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR hSG
  have hgg : genus (AlgebraicClosure ℚ) (Fb Γ) = genusFF (AlgebraicClosure ℚ) (Fb Γ) :=
    AlgebraicCurve.genus_eq_genusFF hRR hWDA hC
  obtain ⟨hfin, hrk⟩ :=
    AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := AlgebraicClosure ℚ) (F := Fb Γ)
  exact ⟨hfin, hrk.trans hgg⟩

theorem diffQExp_injective [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    Function.Injective ⇑(ModularCurve.diffQExp (Fb Γ)) := by
  obtain ⟨x, hxT, hxfd⟩ := exists_transcendental Γ hT
  haveI : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (Fb Γ))) (Fb Γ) := hxfd
  haveI : Algebra.IsAlgebraic
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (Fb Γ))) (Fb Γ) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (Fb Γ))) (Fb Γ) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [injective_iff_map_eq_zero]
  intro ω hω
  obtain ⟨c, hc, -⟩ := KaehlerDifferential.exists_unique_smul_D_of_transcendental (AlgebraicClosure ℚ) x hxT ω
  rw [hc, ModularCurve.diffQExp_smul_D] at hω
  rcases mul_eq_zero.mp hω with hc0 | hq0
  · have hc00 : c = 0 := by exact_mod_cast hc0
    rw [hc, hc00, zero_smul]
  · exfalso
    apply hxT
    have hcoeff : ∀ n : ℤ, n ≠ 0 → (x : LaurentSeries (AlgebraicClosure ℚ)).coeff n = 0 := by
      intro n hn
      have h := congrArg (fun y : LaurentSeries (AlgebraicClosure ℚ) => y.coeff n) hq0
      simp only [HahnSeries.coeff_zero] at h
      change ((n : AlgebraicClosure ℚ)) * (x : LaurentSeries (AlgebraicClosure ℚ)).coeff n = 0 at h
      exact (mul_eq_zero.mp h).resolve_left (Int.cast_ne_zero.mpr hn)
    set a : AlgebraicClosure ℚ := (x : LaurentSeries (AlgebraicClosure ℚ)).coeff 0 with ha
    have hx : (x : LaurentSeries (AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a := by
      rw [ModularCurve.algebraMap_laurentSeries_eq_single]
      ext n
      by_cases hn : n = 0
      · subst hn; simp [ha]
      · rw [hcoeff n hn, HahnSeries.coeff_single_of_ne hn]
    have hx' : x = algebraMap (AlgebraicClosure ℚ) ↥(Fb Γ) a := by
      apply Subtype.ext
      rw [hx, IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) ↥(Fb Γ)
        (LaurentSeries (AlgebraicClosure ℚ)) a]
      rfl
    rw [hx']
    exact isAlgebraic_algebraMap _

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

def qExpL (hT : ModularGroup.T ∈ Γ) : S2 Γ →ₗ[ℂ] LaurentSeries ℂ where
  toFun f := HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f)
  map_add' f g := by
    simp only [CuspForm.coe_add]
    rw [ModularForm.qExpansion_add one_pos (one_mem_strictPeriods Γ hT) f g, map_add]
  map_smul' c f := by
    simp only [CuspForm.IsGLPos.coe_smul, RingHom.id_apply]
    rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods Γ hT) c f]
    rw [PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

@[scoped simp] theorem qExpL_apply (hT : ModularGroup.T ∈ Γ) (f : S2 Γ) :
    qExpL Γ hT f = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) := rfl

theorem main (M : ℕ) [NeZero M] [Γ.FiniteIndex]
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (hT : ModularGroup.T ∈ Γ) :
    genusFF (AlgebraicClosure ℚ) (Fb Γ) ≤ Module.finrank ℂ (S2 Γ) := by
  classical
  haveI : IsCurveOver (AlgebraicClosure ℚ) (Fb Γ) := isCurveOver_Fb Γ hT
  obtain ⟨hfin, hrk⟩ := finite_and_finrank_regularDifferentials_eq_genusFF Γ hT
  haveI := hfin
  haveI : FiniteDimensional ℂ (S2 Γ) := CuspForm.finiteDimensional_of_isArithmetic _ 2

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι₀ : AlgebraicClosure ℚ →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := AlgebraicClosure ℚ)).toRingHom
  letI : Algebra (AlgebraicClosure ℚ) ℂ := ι₀.toAlgebra

  set R := regularDifferentials (AlgebraicClosure ℚ) (Fb Γ) with hR
  let B := Module.finBasis (AlgebraicClosure ℚ) ↥R
  have hconv := fun i : Fin (Module.finrank (AlgebraicClosure ℚ) ↥R) =>
    conv Γ M hΓ₁ hΓ₀ hT ι₀ ((B i : ↥R) : Ω[↥(Fb Γ)⁄AlgebraicClosure ℚ]) (B i).2
  choose f hf using hconv

  have hLIq : LinearIndependent (AlgebraicClosure ℚ)
      (fun i => diffQExp (Fb Γ) ((B i : ↥R) : Ω[↥(Fb Γ)⁄AlgebraicClosure ℚ])) := by
    let Θq : Ω[↥(Fb Γ)⁄AlgebraicClosure ℚ] →ₗ[AlgebraicClosure ℚ] LaurentSeries (AlgebraicClosure ℚ) :=
      (diffQExp (Fb Γ)).restrictScalars (AlgebraicClosure ℚ)
    have h1 : LinearIndependent (AlgebraicClosure ℚ) (fun i => ((B i : ↥R) : Ω[↥(Fb Γ)⁄AlgebraicClosure ℚ])) :=
      B.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
    exact h1.map' Θq (LinearMap.ker_eq_bot.mpr (diffQExp_injective Γ hT))
  have hLI' : LinearIndependent ℂ
      (⇑(coeffMap (algebraMap (AlgebraicClosure ℚ) ℂ)) ∘
        fun i => diffQExp (Fb Γ) ((B i : ↥R) : Ω[↥(Fb Γ)⁄AlgebraicClosure ℚ])) :=
    ModularCurve.linearIndependent_coeffMap_comp_of_linearIndependent (AlgebraicClosure ℚ) ℂ _ hLIq
  have hcomp : (⇑(coeffMap (algebraMap (AlgebraicClosure ℚ) ℂ)) ∘
        fun i => diffQExp (Fb Γ) ((B i : ↥R) : Ω[↥(Fb Γ)⁄AlgebraicClosure ℚ])) = ⇑(qExpL Γ hT) ∘ f := by
    funext i
    simp only [Function.comp_apply, qExpL_apply]
    exact hf i
  rw [hcomp] at hLI'
  have hLI : LinearIndependent ℂ f := LinearIndependent.of_comp (qExpL Γ hT) hLI'
  calc genusFF (AlgebraicClosure ℚ) (Fb Γ)
      = Fintype.card (Fin (Module.finrank (AlgebraicClosure ℚ) ↥R)) := by rw [Fintype.card_fin, hrk]
    _ ≤ Module.finrank ℂ (S2 Γ) := hLI.fintype_card_le_finrank

end XHGenusLE
p2m_reactivate "P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_finrank_cuspForm_gammaH_two.XHGenusLE"

end
p2m_reactivate "P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_finrank_cuspForm_gammaH_two.XHGenusLE"

scoped instance XHGenusLE.finiteIndex_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

p2m_reactivate "P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_finrank_cuspForm_gammaH_two.XHGenusLE"
open scoped MatrixGroups in
theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) ≤
      Module.finrank ℂ (CuspForm (CohCarrier.GammaH M H) 2) :=
  XHGenusLE.main (CohCarrier.GammaH M H) M (ModularCurve.Gamma1_le_GammaH M H)
    (CohCarrier.GammaH_le_Gamma0 H) (ModularCurve.translation_mem_GammaH M H)

#print axioms solution

end S_ModularCurve_genusFF_xHFunctionFieldBar_le_finrank_cuspForm_gammaH_two
end P2MW
export P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_finrank_cuspForm_gammaH_two (solution)
