-- Prove2me | solution 1 for ModularCurve.exists_linearMap_injective_tensorProduct_kaehler_map_ssPolarDifferentials_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/80373221-f063-521d-ae71-7c7b5101d5a9

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Theorems.Thm_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul
import Theorems.Thm_AlgebraicCurve_map_mem_polarDifferentials_and_mem_span_image_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_ModularCurve_comap_ne_top_and_mem_ssPlacesQExp_of_mem_and_mem_ssPlacesQExp_of_comap_eq
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_of_ne_top
import Theorems.Thm_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_map_ssPolarDifferentials_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct MatrixGroups
p2m_open "ModularCurve P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_map_ssPolarDifferentials_eq.ModularCurve AlgebraicCurve KaehlerDifferential HahnSeries CongruenceSubgroup"

namespace ModularCurve
p2m_export "ModularCurve" "ssPlacesQExp ssPolarDifferentials infSubgroup neZero_div intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffMap_intSeriesC coeffMap_mem_qExpFunctionFieldC_of_mem exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul comap_ne_top_and_mem_ssPlacesQExp_of_mem_and_mem_ssPlacesQExp_of_comap_eq ssJSet_eq_image_algebraMap_of_isAlgClosed exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed"
namespace DiffAGlue
p2m_open "ModularCurve"

theorem Gamma_le_GammaH (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) : Gamma N ≤ CohCarrier.GammaH N H' := by
  intro A hA
  rw [Gamma_mem] at hA
  obtain ⟨h00, h01, h10, h11⟩ := hA
  have hA0 : A ∈ Gamma0 N := by rw [Gamma0_mem]; exact h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem _

scoped instance finiteIndex_GammaH (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) : (CohCarrier.GammaH N H').FiniteIndex :=
  IsCongruenceSubgroup.finiteIndex ⟨N, NeZero.ne N, Gamma_le_GammaH N H'⟩

theorem T_mem_GammaH (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH N H' := by
  have hT0 : ModularGroup.T ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp [ModularGroup.T]
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hT0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨ModularGroup.T, hT0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    change ((ModularGroup.T 1 1 : ℤ) : ZMod N) = 1
    simp [ModularGroup.T]
  rw [this]
  exact one_mem _

section Setup
variable (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K] (Γ : Subgroup SL(2, ℤ))

def iota : ↥(qExpFunctionFieldC k Γ) →+* ↥(qExpFunctionFieldC K Γ) where
  toFun x := ⟨coeffMap (algebraMap k K) (x : LaurentSeries k),
    coeffMap_mem_qExpFunctionFieldC_of_mem (algebraMap k K) Γ x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_iota (x : ↥(qExpFunctionFieldC k Γ)) :
    ((iota k K Γ x : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) = coeffMap (algebraMap k K) (x : LaurentSeries k) := rfl

scoped instance algebraFkFK : Algebra ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) := (iota k K Γ).toAlgebra

theorem algebraMap_Fk_FK : algebraMap ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) = iota k K Γ := rfl

scoped instance algebrakFK : Algebra k ↥(qExpFunctionFieldC K Γ) :=
  ((algebraMap K ↥(qExpFunctionFieldC K Γ)).comp (algebraMap k K)).toAlgebra

theorem algebraMap_k_FK_apply (a : k) :
    algebraMap k ↥(qExpFunctionFieldC K Γ) a = algebraMap K ↥(qExpFunctionFieldC K Γ) (algebraMap k K a) := rfl

scoped instance isScalarTower_k_K_FK : IsScalarTower k K ↥(qExpFunctionFieldC K Γ) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance isScalarTower_k_Fk_FK : IsScalarTower k ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) := by
  refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
  apply Subtype.ext
  rw [algebraMap_k_FK_apply, algebraMap_Fk_FK, coe_iota]
  change algebraMap K (LaurentSeries K) (algebraMap k K a) = coeffMap (algebraMap k K) (algebraMap k (LaurentSeries k) a)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

scoped instance smulCommClass_K_Fk_FK : SMulCommClass K ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) :=
  ⟨fun c f x => by simp only [Algebra.smul_def]; ring⟩

theorem adjoin_range_iota_eq_top :
    IntermediateField.adjoin K (Set.range (algebraMap ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ))) = ⊤ := by
  rw [algebraMap_Fk_FK]
  apply le_antisymm le_top

  intro x _
  set A := IntermediateField.adjoin K (Set.range (iota k K Γ)) with hA

  have hgen : intFormRatiosC K Γ ⊆ (A.map (qExpFunctionFieldC K Γ).val : Set (LaurentSeries K)) := by
    rintro _ ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩
    have hg0k : intSeriesC k pg ≠ 0 := by
      intro h
      apply hg0
      rw [← coeffMap_intSeriesC (algebraMap k K) pg, h, map_zero]
    refine ⟨⟨intSeriesC K pf / intSeriesC K pg, intFormRatiosC_subset K Γ ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩⟩, ?_, rfl⟩
    apply IntermediateField.subset_adjoin
    refine ⟨⟨intSeriesC k pf / intSeriesC k pg, intFormRatiosC_subset k Γ ⟨w, f, g, pf, pg, hf, hg, hg0k, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    rw [coe_iota, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  have hle : qExpFunctionFieldC K Γ ≤ A.map (qExpFunctionFieldC K Γ).val := by
    change IntermediateField.adjoin K (intFormRatiosC K Γ) ≤ _
    exact IntermediateField.adjoin_le_iff.mpr hgen
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

end Setup

end ModularCurve.DiffAGlue
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_map_ssPolarDifferentials_eq.ModularCurve P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_map_ssPolarDifferentials_eq.ModularCurve.DiffAGlue"
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_map_ssPolarDifferentials_eq.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_map_ssPolarDifferentials_eq.ModularCurve P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_map_ssPolarDifferentials_eq.ModularCurve.DiffAGlue"

open scoped TensorProduct MatrixGroups in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_map_ssPolarDifferentials_eq.ModularCurve ModularCurve.DiffAGlue AlgebraicCurve KaehlerDifferential in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra k K] :
    ∃ Φ : K ⊗[k] Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k] →ₗ[K]
        Ω[↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄K],
      Function.Injective Φ ∧
      (∀ (c : K) (f g : ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))
          (f' g' : ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
          (f' : LaurentSeries K) = coeffMap (algebraMap k K) (f : LaurentSeries k) →
          (g' : LaurentSeries K) = coeffMap (algebraMap k K) (g : LaurentSeries k) →
          Φ (c ⊗ₜ[k] (f • D k ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) g)) =
            c • (f' • D K ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) g')) ∧
      Submodule.map Φ
          ((ssPolarDifferentials k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p).baseChange K) =
        ssPolarDifferentials K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  set Γ' := CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)
  have hT : ModularGroup.T ∈ Γ' := T_mem_GammaH (M / p) _
  obtain ⟨Φ, hinj, hpin⟩ :=
    ModularCurve.exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul k K Γ' hT
  refine ⟨Φ, hinj, hpin, ?_⟩

  obtain ⟨xk, -, hxk, hxkfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed k Γ' hT
  obtain ⟨xK, -, hxK, hxKfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ' hT
  haveI : IsCurveOver k ↥(qExpFunctionFieldC k Γ') := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxk hxkfd
  haveI : IsCurveOver K ↥(qExpFunctionFieldC K Γ') := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxK hxKfd
  haveI : Algebra.EssFiniteType k ↥(qExpFunctionFieldC k Γ') :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hxk hxkfd
  haveI : Algebra.EssFiniteType K ↥(qExpFunctionFieldC K Γ') :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hxK hxKfd
  have hdK : ∀ v : Place k ↥(qExpFunctionFieldC k Γ'), v.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hdK' : ∀ w : Place K ↥(qExpFunctionFieldC K Γ'), w.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hgen := adjoin_range_iota_eq_top k K Γ'

  obtain ⟨hsub, hsup⟩ :=
    AlgebraicCurve.map_mem_polarDifferentials_and_mem_span_image_of_constantFieldExtension_of_isAlgClosed
      k ↥(qExpFunctionFieldC k Γ') K ↥(qExpFunctionFieldC K Γ') ⟨xk, hxk, hxkfd⟩ ⟨xK, hxK, hxKfd⟩ hgen hdK hdK'
      (ssPlacesQExp k Γ' p)

  have hι : ∀ x : ↥(qExpFunctionFieldC k Γ'),
      ((algebraMap ↥(qExpFunctionFieldC k Γ') ↥(qExpFunctionFieldC K Γ') x : ↥(qExpFunctionFieldC K Γ')) : LaurentSeries K) =
        coeffMap (algebraMap k K) (x : LaurentSeries k) := fun x => rfl
  have hss := ModularCurve.ssJSet_eq_image_algebraMap_of_isAlgClosed p k K
  have hS' : {w : Place K ↥(qExpFunctionFieldC K Γ') | ∃ v ∈ ssPlacesQExp k Γ' p,
      w.toValuationSubring.comap (algebraMap ↥(qExpFunctionFieldC k Γ') ↥(qExpFunctionFieldC K Γ')) = v.toValuationSubring} =
      ssPlacesQExp K Γ' p := by
    ext w
    have hA2S := ModularCurve.comap_ne_top_and_mem_ssPlacesQExp_of_mem_and_mem_ssPlacesQExp_of_comap_eq p k K Γ'
      (algebraMap ↥(qExpFunctionFieldC k Γ') ↥(qExpFunctionFieldC K Γ')) hι hss w
    constructor
    · rintro ⟨v, hv, hcomap⟩
      exact hA2S.2 v hv hcomap
    · intro hw
      obtain ⟨hne, hall⟩ := hA2S.1 hw
      obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_of_ne_top
        (algebraMap ↥(qExpFunctionFieldC k Γ') ↥(qExpFunctionFieldC K Γ')) w
        (fun a => by
          rw [← IsScalarTower.algebraMap_apply k ↥(qExpFunctionFieldC k Γ') ↥(qExpFunctionFieldC K Γ') a,
            algebraMap_k_FK_apply]
          exact w.algebraMap_mem' _) hne
      exact ⟨v, hall v hv.symm, hv.symm⟩
  rw [hS'] at hsub hsup

  haveI : IsScalarTower ↥(qExpFunctionFieldC k Γ') ↥(qExpFunctionFieldC K Γ') Ω[↥(qExpFunctionFieldC K Γ')⁄K] :=
    KaehlerDifferential.isScalarTower_of_tower K ↥(qExpFunctionFieldC K Γ')
  have hΦ1 : ∀ ω : Ω[↥(qExpFunctionFieldC k Γ')⁄k],
      Φ (1 ⊗ₜ[k] ω) = KaehlerDifferential.map k K ↥(qExpFunctionFieldC k Γ') ↥(qExpFunctionFieldC K Γ') ω := by
    intro ω
    have key : ∀ η ∈ Submodule.span ↥(qExpFunctionFieldC k Γ') (Set.range (D k ↥(qExpFunctionFieldC k Γ'))),
        ∀ f : ↥(qExpFunctionFieldC k Γ'),
          Φ (1 ⊗ₜ[k] (f • η)) = KaehlerDifferential.map k K ↥(qExpFunctionFieldC k Γ') ↥(qExpFunctionFieldC K Γ') (f • η) := by
      intro η hη
      induction hη using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨g, rfl⟩ := hy
          intro f
          rw [hpin 1 f g (algebraMap _ _ f) (algebraMap _ _ g) (hι f) (hι g), one_smul, LinearMap.map_smul,
            KaehlerDifferential.map_D, algebraMap_smul]
      | zero => intro f; rw [smul_zero, TensorProduct.tmul_zero, map_zero, map_zero]
      | add y z _ _ hy hz => intro f; rw [smul_add, TensorProduct.tmul_add, map_add, map_add, hy, hz]
      | smul g y _ hy => intro f; rw [smul_smul]; exact hy (f * g)
    have := key ω (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1
    rw [one_smul] at this
    exact this

  have hset : (Φ : K ⊗[k] Ω[↥(qExpFunctionFieldC k Γ')⁄k] → Ω[↥(qExpFunctionFieldC K Γ')⁄K]) ''
      ((ssPolarDifferentials k Γ' p).map (TensorProduct.mk k K Ω[↥(qExpFunctionFieldC k Γ')⁄k] 1) :
        Set (K ⊗[k] Ω[↥(qExpFunctionFieldC k Γ')⁄k])) =
      KaehlerDifferential.map k K ↥(qExpFunctionFieldC k Γ') ↥(qExpFunctionFieldC K Γ') ''
        (ssPolarDifferentials k Γ' p : Set (Ω[↥(qExpFunctionFieldC k Γ')⁄k])) := by
    ext η
    simp only [Set.mem_image, Submodule.map_coe, TensorProduct.mk_apply, SetLike.mem_coe]
    constructor
    · rintro ⟨_, ⟨ω, hω, rfl⟩, rfl⟩
      exact ⟨ω, hω, (hΦ1 ω).symm⟩
    · rintro ⟨ω, hω, rfl⟩
      exact ⟨_, ⟨ω, hω, rfl⟩, hΦ1 ω⟩
  rw [Submodule.baseChange_eq_span, Submodule.map_span, hset]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨ω, hω, rfl⟩
    exact hsub ω hω
  · intro η hη
    exact hsup η hη

#print axioms solution

end S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_map_ssPolarDifferentials_eq
end P2MW
export P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_map_ssPolarDifferentials_eq (solution)
