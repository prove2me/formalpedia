-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.exists_ringEquiv_adicCompletion_stalk_drinfeldChart_baseChange_of_cyclotomicWitness_of_isAlgClosed_of_isPrimitiveRoot_mul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/386fc227-1d4d-5229-ae86-85283268ef1d

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AdicCompletionLocalRing

import Theorems.Thm_IsLocalRing_exists_ringHom_adicCompletion_of_isDiscreteValuationRing_of_maximalIdeal_eq_map_of_residueField
import Theorems.Thm_Algebra_TensorProduct_exists_ringHom_residueField_eq_ker_lift_of_isPrime_of_isAlgClosed
import Theorems.Thm_MvPowerSeries_exists_ringEquiv_quotient_span_comp_map_eq_of_ringEquiv_of_linearPart_of_span_eq
import Theorems.Thm_DrinfeldCurve_LocalChart_exists_mem_sq_map_add_mem_of_linearPart_mem_of_isPrime
import Theorems.Thm_AdicCompletion_exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_dominates
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_ringHom_of_dvd
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
import Theorems.Thm_IsLocalRing_perfectField_residueField_of_isAlgebraic_rat
import Theorems.Thm_ModularCurve_laurentBaseChange_eq_adjoin_image_coeffMap_and_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_baseChange_of_cyclotomic_of_isPrimitiveRoot_mul_of_dvd
import Theorems.Thm_AdicCompletion_exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing

import Theorems.Thm_AdicCompletion_exists_ringHom_residueField_surjective_of_ringEquiv_mvPowerSeries_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_ringEquiv_adicCompletion_stalk_drinfeldChart_baseChange_of_cyclotomicWitness_of_isAlgClosed_of_isPrimitiveRoot_mul_of_dvd
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups TensorProduct

set_option synthInstance.maxHeartbeats 1600000

namespace WASM

open IsLocalRing

noncomputable def adicCongr {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) :
    AdicCompletion I R ≃+* AdicCompletion J R := by
  subst h; exact RingEquiv.refl _

theorem adicCongr_algebraMap {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) (x : R) :
    adicCongr h (algebraMap R (AdicCompletion I R) x) = algebraMap R (AdicCompletion J R) x := by
  subst h; rfl

theorem finite_and_isSeparable_residueField
    (A₀ B₀ W₀ : Type*) [CommRing A₀] [IsLocalRing A₀] [CommRing B₀] [Algebra A₀ B₀] [Algebra.FiniteType A₀ B₀]
    [CommRing W₀] [IsLocalRing W₀] [Algebra A₀ W₀] [IsLocalHom (algebraMap A₀ W₀)]
    [PerfectField (ResidueField A₀)]
    (ρ : B₀ →+* ResidueField W₀) (hρ : Function.Surjective ρ)
    (hρA : ∀ a : A₀, ρ (algebraMap A₀ B₀ a) = residue W₀ (algebraMap A₀ W₀ a)) :
    Module.Finite (ResidueField A₀) (ResidueField W₀) ∧
      Algebra.IsSeparable (ResidueField A₀) (ResidueField W₀) := by
  let ρₐ : B₀ →ₐ[A₀] ResidueField W₀ :=
    { toRingHom := ρ
      commutes' := fun a => by
        rw [IsScalarTower.algebraMap_apply A₀ W₀ (ResidueField W₀), ResidueField.algebraMap_eq]
        exact hρA a }
  haveI : Algebra.FiniteType A₀ (ResidueField W₀) := Algebra.FiniteType.of_surjective ρₐ hρ
  haveI : Algebra.FiniteType (ResidueField A₀) (ResidueField W₀) :=
    Algebra.FiniteType.of_restrictScalars_finiteType (R := A₀) (S := ResidueField A₀) (A := ResidueField W₀)
  haveI hfin : Module.Finite (ResidueField A₀) (ResidueField W₀) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  exact ⟨hfin, inferInstance⟩

theorem exists_comp_eq_of_surjective {B₀ F Ω : Type*} [CommRing B₀] [CommRing F] [CommRing Ω]
    (ρ : B₀ →+* F) (hρ : Function.Surjective ρ) (χ : B₀ →+* Ω)
    (hker : ∀ b : B₀, ρ b = 0 → χ b = 0) :
    ∃ χbar : F →+* Ω, ∀ b : B₀, χbar (ρ b) = χ b := by
  refine ⟨(Ideal.Quotient.lift (RingHom.ker ρ) χ fun b hb => hker b hb).comp
    (RingHom.quotientKerEquivOfSurjective hρ).symm.toRingHom, fun b => ?_⟩
  simp [RingHom.quotientKerEquivOfSurjective_symm_apply]

theorem constantCoeff_eq_zero_of_mem_pow {W : Type*} [CommRing W] (n : ℕ) (hn : n ≠ 0)
    (h : MvPowerSeries (Fin 2) W)
    (hh : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ n) :
    MvPowerSeries.constantCoeff h = 0 := by
  have hle : (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ n ≤
      RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin 2) (R := W)) := by
    refine (Ideal.pow_le_self hn).trans ?_
    rw [Ideal.span_le]
    rintro x hx
    rcases hx with rfl | rfl <;> simp [RingHom.mem_ker, MvPowerSeries.constantCoeff_X]
  exact hle hh

theorem eq_of_comap_eq_of_iso_localization {B : Type*} [CommRing B] (y : Ideal B) [y.IsPrime]
    (R : Type*) [CommRing R] (γ : B →+* R) (E : R ≃+* Localization.AtPrime y)
    (hE : ∀ b : B, E (γ b) = algebraMap B (Localization.AtPrime y) b)
    (p₁ p₂ : Ideal R) (h : p₁.comap γ = p₂.comap γ) : p₁ = p₂ := by
  have hc : ∀ p : Ideal R, (p.comap E.symm.toRingHom).under B = p.comap γ := by
    intro p
    rw [Ideal.under_def, Ideal.comap_comap]
    congr 1
    ext b
    simp [← hE]
  have hback : ∀ p : Ideal R, (p.comap E.symm.toRingHom).comap E.toRingHom = p := by
    intro p
    rw [Ideal.comap_comap]
    convert Ideal.comap_id p
    ext x
    simp
  rw [← hback p₁, ← hback p₂,
    ← IsLocalization.map_under (M := y.primeCompl) (S := Localization.AtPrime y) (p₁.comap E.symm.toRingHom),
    ← IsLocalization.map_under (M := y.primeCompl) (S := Localization.AtPrime y) (p₂.comap E.symm.toRingHom),
    hc, hc, h]

theorem isNoetherianRing_of_baseChange (A₀ A C₀ C : Type*) [CommRing A₀] [CommRing A] [Algebra A₀ A]
    [IsNoetherianRing A] [CommRing C₀] [Algebra A₀ C₀] [Algebra.FiniteType A₀ C₀] [CommRing C] [Algebra A C]
    (c : C₀ →+* C) (β : A ⊗[A₀] C₀ ≃+* C) (hβ : ∀ (a : A) (b : C₀), β (a ⊗ₜ[A₀] b) = algebraMap A C a * c b) :
    IsNoetherianRing C := by
  haveI hft : Algebra.FiniteType A (A ⊗[A₀] C₀) := inferInstance
  let βₐ : A ⊗[A₀] C₀ →ₐ[A] C :=
    { toRingHom := β.toRingHom
      commutes' := fun a => by
        show β (algebraMap A (A ⊗[A₀] C₀) a) = algebraMap A C a
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hβ, map_one,
          mul_one] }
  haveI : Algebra.FiniteType A C := Algebra.FiniteType.of_surjective βₐ (fun x => β.surjective x)
  exact Algebra.FiniteType.isNoetherianRing A C

end WASM

section
open IsLocalRing MvPowerSeries
theorem WASM_brdist_transport
    (q : ℕ) [Fact q.Prime]
    (W₀ W : Type) [CommRing W₀] [IsLocalRing W₀] [CommRing W] [IsLocalRing W] (ψ : W₀ →+* W)
    (π₀ : W₀) (hπ₀ : maximalIdeal W₀ = Ideal.span {π₀})
    (hqW₀ : (q : W₀) ∈ maximalIdeal W₀) (hqW : (q : W) ∈ maximalIdeal W)
    (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀) (hu₀ : IsUnit u₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1}) ^ (q + 2))
    (g : MvPowerSeries (Fin 2) W)
    (hrel : MvPowerSeries.map ψ (C π₀ * v₀ - f₀ * u₀) ∈ Ideal.span {g})
    (π : W) (hπ : ∃ r : W, ψ π₀ = π * r)
    (R₀ R B₀ B : Type) [CommRing R₀] [CommRing R] [CommRing B₀] [CommRing B]
    (φ₀ : R₀ →+* MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {C π₀ * v₀ - f₀ * u₀})
    (φ : R →+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {g})
    (γ₀ : B₀ →+* R₀) (γ : B →+* R) (c : B₀ →+* B)
    (hloc : ∀ p₁ p₂ : Ideal R₀, p₁.IsPrime → p₂.IsPrime → p₁.comap γ₀ = p₂.comap γ₀ → p₁ = p₂)
    (hcompat : ∀ (x : B₀) (s : MvPowerSeries (Fin 2) W₀),
      φ₀ (γ₀ x) = Ideal.Quotient.mk (Ideal.span {C π₀ * v₀ - f₀ * u₀}) s →
      φ (γ (c x)) = Ideal.Quotient.mk (Ideal.span {g}) (MvPowerSeries.map ψ s))
    (hdist₀ :
      let S₀ := (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C π₀ * v₀ - f₀ * u₀})
      let mkS₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π₀ * v₀ - f₀ * u₀})
      ∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S₀), P₁.IsPrime → P₂.IsPrime →
        (mkS₀ (MvPowerSeries.X 0) ∉ P₁ ∨ mkS₀ (MvPowerSeries.X 1) ∉ P₁) →
        (mkS₀ (MvPowerSeries.X 0) ∉ P₂ ∨ mkS₀ (MvPowerSeries.X 1) ∉ P₂) →
        mkS₀ (MvPowerSeries.C π₀) ∈ P₁ → mkS₀ (MvPowerSeries.C π₀) ∈ P₂ →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
            mkS₀ (MvPowerSeries.C ((a₁ : ℤ) : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₀) * MvPowerSeries.X 1 + h)
              ∈ P₁) →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
            mkS₀ (MvPowerSeries.C ((a₂ : ℤ) : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₀) * MvPowerSeries.X 1 + h)
              ∈ P₂) →
        ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
          Ideal.comap φ₀ P₁ ≠ Ideal.comap φ₀ P₂) :
    let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {g})
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {g})
    ∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →
      (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
      (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
      mkS (MvPowerSeries.C π) ∈ P₁ → mkS (MvPowerSeries.C π) ∈ P₂ →
      (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
          mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h)
            ∈ P₁) →
      (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
          mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h)
            ∈ P₂) →
      ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
        Ideal.comap φ P₁ ≠ Ideal.comap φ P₂ := by
  intro S_ mkS_
  subst mkS_ S_
  intro a₁ b₁ a₂ b₂ P₁ P₂ hP₁ hP₂ hX₁ hX₂ hπ₁ hπ₂ hab₁ hab₂ hdet hEq
  classical
  obtain ⟨r, hr⟩ := hπ

  have hker : ∀ s ∈ (Ideal.span {C π₀ * v₀ - f₀ * u₀} : Ideal (MvPowerSeries (Fin 2) W₀)), (Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W))).comp (MvPowerSeries.map ψ) s = 0 := by
    intro s hs
    rw [Ideal.mem_span_singleton'] at hs
    obtain ⟨t, rfl⟩ := hs
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact Ideal.mul_mem_left _ _ hrel
  obtain ⟨lam, hlam_mk⟩ : ∃ lam : MvPowerSeries (Fin 2) W₀ ⧸ (Ideal.span {C π₀ * v₀ - f₀ * u₀} : Ideal (MvPowerSeries (Fin 2) W₀)) →+* MvPowerSeries (Fin 2) W ⧸ (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W)),
      ∀ s : MvPowerSeries (Fin 2) W₀, lam (Ideal.Quotient.mk (Ideal.span {C π₀ * v₀ - f₀ * u₀} : Ideal (MvPowerSeries (Fin 2) W₀)) s) = Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W)) (MvPowerSeries.map ψ s) :=
    ⟨Ideal.Quotient.lift (Ideal.span {C π₀ * v₀ - f₀ * u₀} : Ideal (MvPowerSeries (Fin 2) W₀)) ((Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W))).comp (MvPowerSeries.map ψ)) hker, fun s => rfl⟩

  have hsq : ∀ x : B₀, lam (φ₀ (γ₀ x)) = φ (γ (c x)) := by
    intro x
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (φ₀ (γ₀ x))
    rw [← hs, hlam_mk, hcompat x s hs.symm]

  have hCπ : ∀ P : Ideal (MvPowerSeries (Fin 2) W ⧸ (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W))), Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W)) (C π) ∈ P →
      (C (ψ π₀) : MvPowerSeries (Fin 2) W) ∈ P.comap (Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W))) := by
    intro P hP
    rw [Ideal.mem_comap, hr, map_mul, map_mul]
    exact P.mul_mem_right _ hP

  have key : ∀ (a b : ℤ) (P : Ideal (MvPowerSeries (Fin 2) W ⧸ (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W)))), P.IsPrime →
      (Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W)) (X 0) ∉ P ∨ Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W)) (X 1) ∉ P) →
      Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W)) (C π) ∈ P →
      (∃ h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ 2,
        Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W)) (C ((a : ℤ) : W) * X 0 + C ((b : ℤ) : W) * X 1 + h) ∈ P) →
      (P.comap lam).IsPrime ∧
      (Ideal.Quotient.mk (Ideal.span {C π₀ * v₀ - f₀ * u₀} : Ideal (MvPowerSeries (Fin 2) W₀)) (X 0) ∉ P.comap lam ∨ Ideal.Quotient.mk (Ideal.span {C π₀ * v₀ - f₀ * u₀} : Ideal (MvPowerSeries (Fin 2) W₀)) (X 1) ∉ P.comap lam) ∧
      Ideal.Quotient.mk (Ideal.span {C π₀ * v₀ - f₀ * u₀} : Ideal (MvPowerSeries (Fin 2) W₀)) (C π₀) ∈ P.comap lam ∧
      (∃ h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1}) ^ 2,
        Ideal.Quotient.mk (Ideal.span {C π₀ * v₀ - f₀ * u₀} : Ideal (MvPowerSeries (Fin 2) W₀)) (C ((a : ℤ) : W₀) * X 0 + C ((b : ℤ) : W₀) * X 1 + h) ∈ P.comap lam) := by
    intro a b P hP hX hCπP hab
    haveI := hP
    refine ⟨Ideal.comap_isPrime lam P, ?_, ?_, ?_⟩
    · simp only [Ideal.mem_comap, hlam_mk, map_X]
      exact hX
    · rw [Ideal.mem_comap, hlam_mk, map_C]
      exact hCπ P hCπP
    · have hQ : (P.comap (Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W)))).IsPrime := Ideal.comap_isPrime _ P
      have hQg : MvPowerSeries.map ψ (C π₀ * v₀ - f₀ * u₀) ∈ P.comap (Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W))) := by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hrel]
        exact P.zero_mem
      have hQX : (X 0 : MvPowerSeries (Fin 2) W) ∉ P.comap (Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W))) ∨
          (X 1 : MvPowerSeries (Fin 2) W) ∉ P.comap (Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W))) := by
        simp only [Ideal.mem_comap]; exact hX
      have hab' : ∃ h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ 2,
          C ((a : ℤ) : W) * X 0 + C ((b : ℤ) : W) * X 1 + h ∈ P.comap (Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W))) := by
        obtain ⟨h, hh, hmem⟩ := hab
        exact ⟨h, hh, Ideal.mem_comap.mpr hmem⟩
      obtain ⟨h₀, hh₀, hmem₀⟩ :=
        DrinfeldCurve.LocalChart.exists_mem_sq_map_add_mem_of_linearPart_mem_of_isPrime q W₀ W ψ π₀ hπ₀ hqW₀ hqW
          f₀ u₀ v₀ hu₀ hf₀ (P.comap (Ideal.Quotient.mk (Ideal.span {g} : Ideal (MvPowerSeries (Fin 2) W)))) hQ hQg hQX (hCπ P hCπP) a b hab'
      refine ⟨h₀, hh₀, ?_⟩
      rw [Ideal.mem_comap, hlam_mk]
      exact Ideal.mem_comap.mp hmem₀
  obtain ⟨hP'₁, hX'₁, hπ'₁, hab'₁⟩ := key a₁ b₁ P₁ hP₁ hX₁ hπ₁ hab₁
  obtain ⟨hP'₂, hX'₂, hπ'₂, hab'₂⟩ := key a₂ b₂ P₂ hP₂ hX₂ hπ₂ hab₂
  have hne : Ideal.comap φ₀ (P₁.comap lam) ≠ Ideal.comap φ₀ (P₂.comap lam) :=
    hdist₀ a₁ b₁ a₂ b₂ (P₁.comap lam) (P₂.comap lam) hP'₁ hP'₂ hX'₁ hX'₂ hπ'₁ hπ'₂ hab'₁ hab'₂ hdet
  apply hne
  haveI := hP'₁
  haveI := hP'₂
  apply hloc _ _ (Ideal.comap_isPrime φ₀ _) (Ideal.comap_isPrime φ₀ _)
  ext x
  simp only [Ideal.mem_comap]
  rw [hsq x]
  have h1 : φ (γ (c x)) ∈ P₁ ↔ γ (c x) ∈ Ideal.comap φ P₁ := Ideal.mem_comap.symm
  have h2 : φ (γ (c x)) ∈ P₂ ↔ γ (c x) ∈ Ideal.comap φ P₂ := Ideal.mem_comap.symm
  rw [h1, h2, hEq]

end

namespace WasmEqSeam

theorem core_fin {A K C₀ : Type} [CommRing A] [CommRing K] [Algebra A K] [CommRing C₀]
    (C : Subalgebra A K) (τK : K →+* K) (cc : C₀ →+* ↥C)
    (hτalg : ∀ a : A, τK (algebraMap A K a) = algebraMap A K a)
    (hτc : ∀ b : C₀, ∃ b' : C₀, τK ((cc b : ↥C) : K) = ((cc b' : ↥C) : K))
    (hgen : ∀ x : ↥C, x ∈ Subring.closure (Set.range (algebraMap A ↥C) ∪ Set.range cc)) :
    ∀ a : K, a ∈ C → τK a ∈ C := by
  intro a ha
  have key : ∀ x : ↥C, x ∈ Subring.closure (Set.range (algebraMap A ↥C) ∪ Set.range cc) → τK (x : K) ∈ C := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · rw [Subalgebra.coe_algebraMap, hτalg]
        exact C.algebraMap_mem a
      · obtain ⟨b', hb'⟩ := hτc b
        rw [hb']
        exact (cc b').2
    | zero => rw [ZeroMemClass.coe_zero, map_zero]; exact C.zero_mem
    | one => rw [OneMemClass.coe_one, map_one]; exact C.one_mem
    | add x y _ _ hx hy => rw [Subalgebra.coe_add, map_add]; exact C.add_mem hx hy
    | neg x _ hx => rw [Subalgebra.coe_neg, map_neg]; exact C.neg_mem hx
    | mul x y _ _ hx hy => rw [Subalgebra.coe_mul, map_mul]; exact C.mul_mem hx hy
  exact key ⟨a, ha⟩ (hgen ⟨a, ha⟩)

theorem core_fix {A C C₀ : Type} [CommRing A] [CommRing C] [Algebra A C] [CommRing C₀]
    (I : Ideal C) (τ' : C →+* C) (cc : C₀ →+* C)
    (hτalg : ∀ a : A, τ' (algebraMap A C a) = algebraMap A C a)
    (hτc : ∀ b : C₀, τ' (cc b) - cc b ∈ I)
    (hgen : ∀ x : C, x ∈ Subring.closure (Set.range (algebraMap A C) ∪ Set.range cc)) :
    ∀ x : C, τ' x - x ∈ I := by
  intro x
  have hx := hgen x
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rw [hτalg, sub_self]; exact I.zero_mem
    · exact hτc b
  | zero => rw [map_zero, sub_self]; exact I.zero_mem
  | one => rw [map_one, sub_self]; exact I.zero_mem
  | add x y _ _ hx hy =>
    have : τ' (x + y) - (x + y) = (τ' x - x) + (τ' y - y) := by rw [map_add]; ring
    rw [this]; exact I.add_mem hx hy
  | neg x _ hx =>
    have : τ' (-x) - (-x) = -(τ' x - x) := by rw [map_neg]; ring
    rw [this]; exact I.neg_mem hx
  | mul x y _ _ hx hy =>
    have : τ' (x * y) - x * y = (τ' x - x) * τ' y + x * (τ' y - y) := by rw [map_mul]; ring
    rw [this]; exact I.add_mem (I.mul_mem_right _ hx) (I.mul_mem_left _ hy)

theorem core_lin {A C C₀ S : Type} [CommRing A] [CommRing C] [Algebra A C] [CommRing C₀] [CommRing S]
    (f g : C →+* S) (cc : C₀ →+* C)
    (halg : ∀ a : A, f (algebraMap A C a) = g (algebraMap A C a))
    (hc : ∀ b : C₀, f (cc b) = g (cc b))
    (hgen : ∀ x : C, x ∈ Subring.closure (Set.range (algebraMap A C) ∪ Set.range cc)) :
    ∀ x : C, f x = g x := by
  intro x
  have hx := hgen x
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact halg a
    · exact hc b
  | zero => rw [map_zero, map_zero]
  | one => rw [map_one, map_one]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | neg x _ hx => rw [map_neg, map_neg, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

theorem algEquiv_eq_id_of_adjoin {L E : Type} [Field L] [Field E] [Algebra L E]
    (K : IntermediateField L E) (Sgen : Set E) (hK : K = IntermediateField.adjoin L Sgen)
    (τ : ↥K ≃ₐ[L] ↥K) (hfix : ∀ (x : E) (hx : x ∈ K), x ∈ Sgen → τ ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∀ k : ↥K, τ k = k := by
  let Fix : IntermediateField L ↥K :=
    (AlgHom.equalizer (τ : ↥K →ₐ[L] ↥K) (AlgHom.id L ↥K)).toIntermediateField (by
      intro x hx
      rw [AlgHom.mem_equalizer] at hx ⊢
      simp only [AlgHom.coe_id, id_eq, AlgEquiv.coe_algHom, map_inv₀] at hx ⊢
      rw [hx])
  have hmem : ∀ k : ↥K, k ∈ Fix ↔ τ k = k := by
    intro k
    show k ∈ AlgHom.equalizer (τ : ↥K →ₐ[L] ↥K) (AlgHom.id L ↥K) ↔ τ k = k
    rw [AlgHom.mem_equalizer]
    rfl
  have hle : K ≤ IntermediateField.lift Fix := by
    conv_lhs => rw [hK]
    rw [IntermediateField.adjoin_le_iff]
    intro x hxS
    have hxK : x ∈ K := by rw [hK]; exact IntermediateField.subset_adjoin L Sgen hxS
    have := (IntermediateField.mem_lift (E := Fix) ⟨x, hxK⟩).mpr ((hmem _).mpr (hfix x hxK hxS))
    exact this
  have heq : IntermediateField.lift Fix = K := le_antisymm (IntermediateField.lift_le Fix) hle
  have htop : Fix = ⊤ := by
    apply IntermediateField.lift_injective K
    rw [heq, IntermediateField.lift_top]
  intro k
  exact (hmem k).mp (htop.symm ▸ IntermediateField.mem_top)

end WasmEqSeam

set_option maxHeartbeats 16000000 in
theorem WASM_eq_riders
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (t : A) (ht : ∃ w : A, IsUnit w ∧ t ^ (q - 1) = (q : A) * w)
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (L₀ : Type) [Field L₀] [CharZero L₀] [IsCyclotomicExtension {q * ℓ} ℚ L₀]
    (ζ₀ : L₀) (hζ₀ : IsPrimitiveRoot ζ₀ q)
    (ξ₀ : L₀) (hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ))
    (hζξ₀ : ζ₀ = ξ₀ ^ ℓ)
    (K₀ : IntermediateField L₀ (LaurentSeries L₀))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀ (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Algebra A₀ L₀] [IsFractionRing A₀ L₀]
    (hA₀q : (q : A₀) ∈ IsLocalRing.maximalIdeal A₀) (hζ₀A : ∃ x : A₀, algebraMap A₀ L₀ x = ζ₀)
    [Algebra A₀ ↥K₀] [IsScalarTower A₀ L₀ ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L₀)) = ModularCurve.coeffEmb L₀ ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ₀ : A₀) (hϖ₀ : IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀})
    (z₀ : ↥(AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀))
    (ϖz₀ : (AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
    (hϖz₀ : ϖz₀ = ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ⊤ z₀ trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A₀ (↥K₀) j₀).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom ϖ₀)))
    (hz₀ : ϖz₀ ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
    (y₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₀ (↥K₀) j₀))
    (hy₀ : (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀ = z₀)
    (hss₀ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* Ω),
      RingHom.ker φ = y₀.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ (↥K₀) j₀) ∈ ModularCurve.ssJSet q Ω)
    (i : L₀ →+* L) (hiζ : i ζ₀ = ζ) (hiξ : i ξ₀ = ξ)
    [Algebra A₀ A] [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    (hA₀A : ∀ a : A₀, algebraMap A L (algebraMap A₀ A a) = i (algebraMap A₀ L₀ a))
    (hϖ₀t : ∃ w : A, IsUnit w ∧ algebraMap A₀ A ϖ₀ = t * w)
    (cK : ↥K₀ →+* ↥K)
    (hcK : ∀ x : ↥K₀, ((cK x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap i ((x : ↥K₀) : LaurentSeries L₀))
    (hcKj : cK j₀ = j)
    (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hc : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
      ((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = cK (a : ↥K₀))
    (hcy : Ideal.comap c y.asIdeal = y₀.asIdeal)
    (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) ≃+*
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hβ : ∀ (a : A) (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),
      β (a ⊗ₜ[A₀] b) = algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a * c b)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] (σ₀ : A₀ →+* W₀)
    (hσ₀ϖ : IsLocalRing.maximalIdeal W₀ = Ideal.span {σ₀ ϖ₀})
    (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀) (hu₀ : IsUnit u₀) (hv₀ : IsUnit v₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ (q + 2))
    (e₀ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀) ≃+*
      MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
    (hriders₀ :
      let STK₀ := ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
      let CMP₀ := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
      let toC₀ : STK₀ →+* CMP₀ := algebraMap STK₀ CMP₀
      let S₀ := (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
      let mkS₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
      let germY₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* STK₀ :=
        ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)
      (∀ a : A₀, e₀ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
          (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ⊤ z₀ trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A₀ (↥K₀) j₀).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ₀ a))) ∧
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K₀ ≃ₐ[L₀] ↥K₀, ModularCurve.FullLevel.IsLevelAutAt L₀ q ζ₀ q (q ^ 2 * M') H₁ γ⁻¹ K₀ τ →
          ∀ a : ↥K₀, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) ∧
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
        ∀ τ : ↥K₀ ≃ₐ[L₀] ↥K₀, ModularCurve.FullLevel.IsLevelAutAt L₀ q ζ₀ q (q ^ 2 * M') H₁ γ⁻¹ K₀ τ →
          ∀ hpres : (∀ a : ↥K₀, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),
            ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
              (((τ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) - a ∈ y₀.asIdeal) ∧
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K₀ ≃ₐ[L₀] ↥K₀, ModularCurve.FullLevel.IsLevelAutAt L₀ q ζ₀ q (q ^ 2 * M') H₁ γ⁻¹ K₀ τ →
          ∀ hpres : (∀ a : ↥K₀, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
              (((τ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) - a ∈ y₀.asIdeal) →
              ∃ (θ : S₀ ≃+* S₀) (c : W₀) (M : Matrix (Fin 2) (Fin 2) W₀),
                (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
                  θ (e₀ (toC₀ (germY₀ a))) = e₀ (toC₀ (germY₀ (((τ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres) a)))) ∧
                (∀ w : W₀, θ (mkS₀ (MvPowerSeries.C w)) = mkS₀ (MvPowerSeries.C w)) ∧
                (∀ jj : Fin 2, θ (mkS₀ (MvPowerSeries.X jj)) -
                    mkS₀ (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                  (Ideal.span {mkS₀ (MvPowerSeries.X 0), mkS₀ (MvPowerSeries.X 1)}) ^ 2) ∧
                (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₀) ∧
                (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₀) ∈ IsLocalRing.maximalIdeal W₀) ∧
                (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W₀) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K₀, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₀)) ∧
      (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S₀), P₁.IsPrime → P₂.IsPrime →

        (mkS₀ (MvPowerSeries.X 0) ∉ P₁ ∨ mkS₀ (MvPowerSeries.X 1) ∉ P₁) →
        (mkS₀ (MvPowerSeries.X 0) ∉ P₂ ∨ mkS₀ (MvPowerSeries.X 1) ∉ P₂) →
        mkS₀ (MvPowerSeries.C (σ₀ ϖ₀)) ∈ P₁ → mkS₀ (MvPowerSeries.C (σ₀ ϖ₀)) ∈ P₂ →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
            mkS₀ (MvPowerSeries.C ((a₁ : ℤ) : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₀) * MvPowerSeries.X 1 + h)
              ∈ P₁) →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
            mkS₀ (MvPowerSeries.C ((a₂ : ℤ) : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₀) * MvPowerSeries.X 1 + h)
              ∈ P₂) →
        ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
          Ideal.comap ((e₀ : CMP₀ →+* S₀).comp toC₀) P₁ ≠ Ideal.comap ((e₀ : CMP₀ →+* S₀).comp toC₀) P₂) ∧

      (∀ P : Ideal S₀, P.IsPrime → (mkS₀ (MvPowerSeries.X 0) ∉ P ∨ mkS₀ (MvPowerSeries.X 1) ∉ P) →
        mkS₀ (MvPowerSeries.C (σ₀ ϖ₀)) ∈ P →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
            mkS₀ (MvPowerSeries.C (1 : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₀) * MvPowerSeries.X 1 + h) ∈ P) →
        ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
          toC₀ (germY₀ a) ∈ Ideal.comap (e₀ : CMP₀ →+* S₀) P ↔
            ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A₀,
              (((a : ↥K₀) : LaurentSeries L₀).coeff n) = algebraMap A₀ L₀ m))

    (ψ : W₀ →+* (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (hψσ₀ : ∀ a : A₀, ψ (σ₀ a) = (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (algebraMap A₀ A a))
    (hψloc : ∀ w : W₀, w ∈ IsLocalRing.maximalIdeal W₀ → ψ w ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (f u v : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
    (hrel : MvPowerSeries.map ψ (MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀) =
      MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u)

    (hconst :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a))))

    (hcompat :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (s : MvPowerSeries (Fin 2) W₀),
        e₀ (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
          ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) x)) =
          Ideal.Quotient.mk _ s →
        e (toC (germY (c x))) = mkS (MvPowerSeries.map ψ s)))

    (hconstY :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
      ∀ a : A, e (toC (germY (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a))) =
        mkS (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a)))
    (hNoeth : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal) →
              ∃ (θ : S ≃+* S) (c : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (M : Matrix (Fin 2) (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)),

                (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                  θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                (∀ w : (AdicCompletion (IsLocalRing.maximalIdeal A) A), θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                    mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                  (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
                (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
                (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A))) := by
  intro STK CMP toC S mkS germY
  classical
  obtain ⟨-, hfin₀, hfix₀, hlin₀, -, -⟩ := hriders₀

  have hmemK : ∀ x : ↥K₀, ModularCurve.coeffMap i ((x : ↥K₀) : LaurentSeries L₀) ∈ K := by
    intro x; rw [← hcK]; exact (cK x).2
  have hcK' : ∀ x : ↥K₀, cK x = ⟨ModularCurve.coeffMap i ((x : ↥K₀) : LaurentSeries L₀), hmemK x⟩ :=
    fun x => Subtype.ext (hcK x)

  have hι' : ∃ ι : L →+* ℂ, ι (i ξ₀) = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)) := by
    rw [hiξ]; exact hι
  obtain ⟨-, hrestr⟩ :=
    ModularCurve.FullLevel.AuxLevelOne.exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd
      q M' hqM' ℓ hℓ12 hℓM' L₀ ξ₀ hξ₀ L i hι' H₁ hH₁ K₀ hK₀ K hK
  have hτpkg : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
        ∃ τ₀ : ↥K₀ ≃ₐ[L₀] ↥K₀,
          ModularCurve.FullLevel.IsLevelAutAt L₀ q ζ₀ q (q ^ 2 * M') H₁ γ⁻¹ K₀ τ₀ ∧
          ∀ x : ↥K₀, τ (cK x) = cK (τ₀ x) := by
    intro γ hγ τ hτ
    have hτ' : ModularCurve.FullLevel.IsLevelAutAt L q ((i ξ₀) ^ ℓ) q (q ^ 2 * M') H₁ γ⁻¹ K τ := by
      rw [hiξ, ← hζξ]; exact hτ
    obtain ⟨τ₀, hτ₀, heq⟩ := hrestr γ hγ τ hτ'
    refine ⟨τ₀, by rw [hζξ₀]; exact hτ₀, fun x => ?_⟩
    apply Subtype.ext
    rw [hcK' x, heq x (hmemK x), hcK]

  have hτalgK : ∀ (τ : ↥K ≃ₐ[L] ↥K) (a : A), τ (algebraMap A ↥K a) = algebraMap A ↥K a := by
    intro τ a
    rw [IsScalarTower.algebraMap_apply A L ↥K a]
    exact τ.commutes _

  have hgen : ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), x ∈ Subring.closure (Set.range (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∪ Set.range c) := by
    intro x
    obtain ⟨t', rfl⟩ := β.surjective x
    induction t' using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Subring.zero_mem _
    | tmul a b =>
      rw [hβ]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨a, rfl⟩)) (Subring.subset_closure (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => rw [map_add]; exact Subring.add_mem _ hx hy

  obtain ⟨hKadj, -⟩ := ModularCurve.laurentBaseChange_eq_adjoin_image_coeffMap_and_exists_ringHom L₀ L i
    (ModularCurve.xHFunctionField (q ^ 2 * M') H₁) K₀ hK₀ K hK
  have hfixall : ∀ (τ : ↥K ≃ₐ[L] ↥K) (τ₀ : ↥K₀ ≃ₐ[L₀] ↥K₀), (∀ x : ↥K₀, τ (cK x) = cK (τ₀ x)) →
      (∀ k₀ : ↥K₀, τ₀ k₀ = k₀) → ∀ k : ↥K, τ k = k := by
    intro τ τ₀ hτcK hall
    refine WasmEqSeam.algEquiv_eq_id_of_adjoin K _ hKadj τ ?_
    intro x hx hxS
    obtain ⟨x₀, hx₀, rfl⟩ := hxS
    have h1 : (⟨ModularCurve.coeffMap i x₀, hx⟩ : ↥K) = cK ⟨x₀, hx₀⟩ := Subtype.ext (by rw [hcK])
    rw [h1]
    exact (hτcK _).trans (congrArg cK (hall _))
  refine ⟨?_, ?_, ?_⟩
  ·
    intro γ hγ τ hτ
    obtain ⟨τ₀, hτ₀, hτcK⟩ := hτpkg γ hγ τ hτ
    have hpres₀ := hfin₀ γ hγ τ₀ hτ₀
    refine WasmEqSeam.core_fin (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (τ : ↥K →+* ↥K) c (fun a => hτalgK τ a) ?_ hgen
    intro b
    refine ⟨((τ₀ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres₀) b, ?_⟩
    rw [hc, hc]
    exact hτcK b
  ·
    intro γ hγ hγℓ τ hτ hpres
    obtain ⟨τ₀, hτ₀, hτcK⟩ := hτpkg γ hγ τ hτ
    have hpres₀ := hfin₀ γ hγ τ₀ hτ₀
    have hfix := hfix₀ γ hγ hγℓ τ₀ hτ₀ hpres₀
    refine WasmEqSeam.core_fix y.asIdeal ((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) c ?_ ?_ hgen
    · intro a
      apply Subtype.ext
      show τ ((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = ((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K)
      rw [Subalgebra.coe_algebraMap]
      exact hτalgK τ a
    · intro b
      have h1 : ((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) (c b) = c (((τ₀ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres₀) b) := by
        apply Subtype.ext
        show τ ((c b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = ((c (((τ₀ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres₀) b) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K)
        rw [hc, hc]
        exact hτcK b
      rw [h1, ← map_sub]
      have h2 := hfix b
      rw [← hcy, Ideal.mem_comap] at h2
      exact h2
  ·
    intro γ hγ τ hτ hpres hgeom
    obtain ⟨τ₀, hτ₀, hτcK⟩ := hτpkg γ hγ τ hτ
    have hpres₀ := hfin₀ γ hγ τ₀ hτ₀
    have hτalg : ∀ a : A, ((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a) = algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a := by
      intro a
      apply Subtype.ext
      show τ ((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = ((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K)
      rw [Subalgebra.coe_algebraMap]
      exact hτalgK τ a
    have hτc : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), ((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) (c b) = c (((τ₀ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres₀) b) := by
      intro b
      apply Subtype.ext
      show τ ((c b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = ((c (((τ₀ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres₀) b) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K)
      rw [hc, hc]
      exact hτcK b
    have hgeom₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), (((τ₀ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres₀) b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) - b ∈ y₀.asIdeal := by
      intro b
      rw [← hcy, Ideal.mem_comap, map_sub, ← hτc]
      exact hgeom (c b)
    obtain ⟨θ₀, c₀, M₀, h0i, h0ii, h0iii, h0iv, h0v, h0vi, h0vii⟩ := hlin₀ γ hγ τ₀ hτ₀ hpres₀ hgeom₀

    haveI := hNoeth
    have hg : Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u} =
        Ideal.span {MvPowerSeries.map ψ (MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀)} := by
      rw [hrel]
    obtain ⟨θ, hθC, hθcompat, hθX⟩ :=
      MvPowerSeries.exists_ringEquiv_quotient_span_comp_map_eq_of_ringEquiv_of_linearPart_of_span_eq
        W₀ (AdicCompletion (IsLocalRing.maximalIdeal A) A) ψ (MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀) (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u) hg
        θ₀ M₀ h0ii h0iii

    have hcompat' : ∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (s : MvPowerSeries (Fin 2) W₀), e₀ ((algebraMap ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) x)) = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})) s →
        e (toC (germY (c x))) = mkS (MvPowerSeries.map ψ s) := hcompat
    have hconstY' : ∀ a : A, e (toC (germY (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a))) = mkS (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a)) :=
      hconstY
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* S, ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), Φ a = e (toC (germY a)) :=
      ⟨((e : CMP →+* S).comp (toC.comp germY)), fun a => rfl⟩
    have hlin : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), θ (Φ a) = Φ (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a) := by
      refine WasmEqSeam.core_lin (θ.toRingHom.comp Φ) (Φ.comp ((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres)) c ?_ ?_ hgen
      · intro a
        show θ (Φ (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a)) = Φ (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a))
        rw [hτalg a, hΦ, hconstY' a, hθC]
      · intro b
        show θ (Φ (c b)) = Φ (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) (c b))
        obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (e₀ ((algebraMap ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) b)))
        obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (e₀ ((algebraMap ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) (((τ₀ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres₀) b))))
        have e1 : e (toC (germY (c b))) = mkS (MvPowerSeries.map ψ s) := hcompat' b s hs.symm
        have e2 : e (toC (germY (c (((τ₀ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres₀) b)))) = mkS (MvPowerSeries.map ψ s') := hcompat' (((τ₀ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres₀) b) s' hs'.symm
        have e3 : θ₀ ((Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})) s) = (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})) s' := by
          rw [hs, hs']
          exact h0i b
        rw [hτc b, hΦ, hΦ, e1, e2]
        exact hθcompat s s' e3
    refine ⟨θ, ψ c₀, fun ii jj => ψ (M₀ ii jj), ?_, hθC, hθX, ?_, ?_, ?_, ?_⟩
    · intro a
      rw [← hΦ, ← hΦ]
      exact hlin a
    · have h := hψloc _ h0iv
      rwa [map_sub, map_pow, map_one] at h
    · intro ii jj
      have h := hψloc _ (h0v ii jj)
      rwa [map_sub, map_mul, map_intCast] at h
    · intro hγℓ
      have h := hψloc _ (h0vi hγℓ)
      rwa [map_sub, map_one] at h
    · intro hγq hne hmem
      have hne₀ : ¬ ∀ k₀ : ↥K₀, τ₀ k₀ = k₀ := fun hall => hne (hfixall τ τ₀ hτcK hall)
      have hunit : IsUnit (c₀ - 1) := IsLocalRing.notMem_maximalIdeal.mp (h0vii hγq hne₀)
      have hunit' : IsUnit (ψ c₀ - 1) := by
        have h := hunit.map ψ
        rwa [map_sub, map_one] at h
      exact (IsLocalRing.notMem_maximalIdeal.mpr hunit') hmem

set_option maxHeartbeats 80000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (t : A) (ht : ∃ w : A, IsUnit w ∧ t ^ (q - 1) = (q : A) * w)
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (L₀ : Type) [Field L₀] [CharZero L₀] [IsCyclotomicExtension {q * ℓ} ℚ L₀]
    (ζ₀ : L₀) (hζ₀ : IsPrimitiveRoot ζ₀ q)
    (ξ₀ : L₀) (hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ))
    (hζξ₀ : ζ₀ = ξ₀ ^ ℓ)
    (K₀ : IntermediateField L₀ (LaurentSeries L₀))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀ (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Algebra A₀ L₀] [IsFractionRing A₀ L₀]
    (hA₀q : (q : A₀) ∈ IsLocalRing.maximalIdeal A₀) (hζ₀A : ∃ x : A₀, algebraMap A₀ L₀ x = ζ₀)
    [Algebra A₀ ↥K₀] [IsScalarTower A₀ L₀ ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L₀)) = ModularCurve.coeffEmb L₀ ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ₀ : A₀) (hϖ₀ : IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀})
    (z₀ : ↥(AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀))
    (ϖz₀ : (AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
    (hϖz₀ : ϖz₀ = ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ⊤ z₀ trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A₀ (↥K₀) j₀).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom ϖ₀)))
    (hz₀ : ϖz₀ ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
    (y₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₀ (↥K₀) j₀))
    (hy₀ : (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀ = z₀)
    (hss₀ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* Ω),
      RingHom.ker φ = y₀.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ (↥K₀) j₀) ∈ ModularCurve.ssJSet q Ω)

    (i : L₀ →+* L) (hiζ : i ζ₀ = ζ) (hiξ : i ξ₀ = ξ)
    [Algebra A₀ A] [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    (hA₀A : ∀ a : A₀, algebraMap A L (algebraMap A₀ A a) = i (algebraMap A₀ L₀ a))
    (hϖ₀t : ∃ w : A, IsUnit w ∧ algebraMap A₀ A ϖ₀ = t * w)
    (cK : ↥K₀ →+* ↥K)
    (hcK : ∀ x : ↥K₀, ((cK x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap i ((x : ↥K₀) : LaurentSeries L₀))
    (hcKj : cK j₀ = j)
    (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hc : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
      ((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = cK (a : ↥K₀))
    (hcy : Ideal.comap c y.asIdeal = y₀.asIdeal)

    (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) ≃+*
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hβ : ∀ (a : A) (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),
      β (a ⊗ₜ[A₀] b) = algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a * c b)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] (σ₀ : A₀ →+* W₀)
    (hσ₀ϖ : IsLocalRing.maximalIdeal W₀ = Ideal.span {σ₀ ϖ₀})
    (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀) (hu₀ : IsUnit u₀) (hv₀ : IsUnit v₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ (q + 2))
    (e₀ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀) ≃+*
      MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
    (hriders₀ :
      let STK₀ := ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
      let CMP₀ := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
      let toC₀ : STK₀ →+* CMP₀ := algebraMap STK₀ CMP₀
      let S₀ := (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
      let mkS₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
      let germY₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* STK₀ :=
        ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)

      (∀ a : A₀, e₀ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
          (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ⊤ z₀ trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A₀ (↥K₀) j₀).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ₀ a))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K₀ ≃ₐ[L₀] ↥K₀, ModularCurve.FullLevel.IsLevelAutAt L₀ q ζ₀ q (q ^ 2 * M') H₁ γ⁻¹ K₀ τ →
          ∀ a : ↥K₀, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
        ∀ τ : ↥K₀ ≃ₐ[L₀] ↥K₀, ModularCurve.FullLevel.IsLevelAutAt L₀ q ζ₀ q (q ^ 2 * M') H₁ γ⁻¹ K₀ τ →
          ∀ hpres : (∀ a : ↥K₀, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),
            ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
              (((τ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) - a ∈ y₀.asIdeal) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K₀ ≃ₐ[L₀] ↥K₀, ModularCurve.FullLevel.IsLevelAutAt L₀ q ζ₀ q (q ^ 2 * M') H₁ γ⁻¹ K₀ τ →
          ∀ hpres : (∀ a : ↥K₀, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
              (((τ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) - a ∈ y₀.asIdeal) →
              ∃ (θ : S₀ ≃+* S₀) (c : W₀) (M : Matrix (Fin 2) (Fin 2) W₀),

                (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
                  θ (e₀ (toC₀ (germY₀ a))) = e₀ (toC₀ (germY₀ (((τ : ↥K₀ →+* ↥K₀).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres) a)))) ∧

                (∀ w : W₀, θ (mkS₀ (MvPowerSeries.C w)) = mkS₀ (MvPowerSeries.C w)) ∧

                (∀ jj : Fin 2, θ (mkS₀ (MvPowerSeries.X jj)) -
                    mkS₀ (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                  (Ideal.span {mkS₀ (MvPowerSeries.X 0), mkS₀ (MvPowerSeries.X 1)}) ^ 2) ∧
                (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₀) ∧
                (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₀) ∈ IsLocalRing.maximalIdeal W₀) ∧
                (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W₀) ∧

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K₀, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₀)) ∧

      (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S₀), P₁.IsPrime → P₂.IsPrime →

        (mkS₀ (MvPowerSeries.X 0) ∉ P₁ ∨ mkS₀ (MvPowerSeries.X 1) ∉ P₁) →
        (mkS₀ (MvPowerSeries.X 0) ∉ P₂ ∨ mkS₀ (MvPowerSeries.X 1) ∉ P₂) →
        mkS₀ (MvPowerSeries.C (σ₀ ϖ₀)) ∈ P₁ → mkS₀ (MvPowerSeries.C (σ₀ ϖ₀)) ∈ P₂ →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
            mkS₀ (MvPowerSeries.C ((a₁ : ℤ) : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₀) * MvPowerSeries.X 1 + h)
              ∈ P₁) →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
            mkS₀ (MvPowerSeries.C ((a₂ : ℤ) : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₀) * MvPowerSeries.X 1 + h)
              ∈ P₂) →
        ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
          Ideal.comap ((e₀ : CMP₀ →+* S₀).comp toC₀) P₁ ≠ Ideal.comap ((e₀ : CMP₀ →+* S₀).comp toC₀) P₂) ∧

      (∀ P : Ideal S₀, P.IsPrime → (mkS₀ (MvPowerSeries.X 0) ∉ P ∨ mkS₀ (MvPowerSeries.X 1) ∉ P) →
        mkS₀ (MvPowerSeries.C (σ₀ ϖ₀)) ∈ P →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
            mkS₀ (MvPowerSeries.C (1 : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₀) * MvPowerSeries.X 1 + h) ∈ P) →
        ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
          toC₀ (germY₀ a) ∈ Ideal.comap (e₀ : CMP₀ →+* S₀) P ↔
            ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A₀,
              (((a : ↥K₀) : LaurentSeries L₀).coeff n) = algebraMap A₀ L₀ m)) :
    ∃ (ψ : W₀ →+* (AdicCompletion (IsLocalRing.maximalIdeal A) A))
      (f u v : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (_ : IsUnit u) (_ : IsUnit v)
      (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)), MvPowerSeries.X 1}) ^ (q + 2))
      (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u}),
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ a : A₀, ψ (σ₀ a) = (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (algebraMap A₀ A a)) ∧
      (∀ w : W₀, w ∈ IsLocalRing.maximalIdeal W₀ → ψ w ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
      f = MvPowerSeries.map ψ f₀ ∧

      (∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (s : MvPowerSeries (Fin 2) W₀),
        e₀ (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
          ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) x)) =
          Ideal.Quotient.mk _ s →
        e (toC (germY (c x))) = mkS (MvPowerSeries.map ψ s)) ∧

      (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal) →
              ∃ (θ : S ≃+* S) (c : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (M : Matrix (Fin 2) (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)),

                (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                  θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                (∀ w : (AdicCompletion (IsLocalRing.maximalIdeal A) A), θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                    mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                  (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
                (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
                (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A))) ∧

      (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

        (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
        (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
        mkS (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ϖ)) ∈ P₁ → mkS (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ϖ)) ∈ P₂ →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C ((a₁ : ℤ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * MvPowerSeries.X 1 + h)
              ∈ P₁) →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C ((a₂ : ℤ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * MvPowerSeries.X 1 + h)
              ∈ P₂) →
        ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
          Ideal.comap ((e : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e : CMP →+* S).comp toC) P₂) ∧

      (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
        mkS (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ϖ)) ∈ P →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C (1 : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * MvPowerSeries.X 1 + h) ∈ P) →
        ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
          toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
            ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
              (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) := by
  classical
  subst hy₀ hy
  obtain ⟨w₀, hw₀u, hw₀⟩ := hϖ₀t
  have hr₀ := hriders₀
  obtain ⟨hCONST₀, hEQfin₀, hEQfix₀, hEQlin₀, hBRdist₀, hBRanchor₀⟩ := hr₀
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ

  have ht𝔪 : t ∈ IsLocalRing.maximalIdeal A := by
    obtain ⟨w, -, hw⟩ := ht
    exact (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem (q - 1)
      (hw ▸ Ideal.mul_mem_right _ _ hAq)

  have hι₀ : ∃ ι : L₀ →+* ℂ, ι ζ₀ = Complex.exp (2 * Real.pi * Complex.I / q) := by
    obtain ⟨ι, hιξ⟩ := hι
    refine ⟨ι.comp i, ?_⟩
    have hℓ0 : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
    have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    rw [RingHom.comp_apply, hζξ₀, map_pow, hiξ, map_pow, hιξ, ← Complex.exp_nat_mul]
    congr 1
    field_simp

  obtain ⟨hy₀max, hϖ₀y₀⟩ :=
    ModularCurve.FullLevel.AuxLevelOne.isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_ringHom_of_dvd q M' hqM' ℓ hℓ12 hℓM'
      L₀ ζ₀ hζ₀ hι₀ H₁ hH₁ K₀ hK₀ A₀ hA₀q hζ₀A j₀ hj₀ ϖ₀ hϖ₀ _ ϖz₀ hϖz₀ hz₀ y₀ rfl hss₀
  haveI := hy₀max

  haveI : Module.Finite ℚ L₀ := IsCyclotomicExtension.finite {q * ℓ} ℚ L₀
  haveI : Algebra.IsAlgebraic ℚ L₀ := Algebra.IsAlgebraic.of_finite ℚ L₀
  haveI : NeZero (q ^ 2 * M') := ⟨Nat.mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  obtain ⟨htj₀, hFD₀, hsep₀⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
      (q ^ 2 * M') H₁ L₀ K₀ hK₀ A₀ j₀ hj₀
  haveI hFT₀ : Algebra.FiniteType A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) :=
    (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A₀ L₀ (↥K₀) j₀ htj₀ hFD₀ hsep₀).1
  haveI : PerfectField (IsLocalRing.ResidueField A₀) :=
    IsLocalRing.perfectField_residueField_of_isAlgebraic_rat L₀ A₀ (IsFractionRing.injective A₀ L₀) q hA₀q
  haveI : Module.IsTorsionFree A₀ ↥K₀ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq A₀ L₀ ↥K₀]
    exact (algebraMap L₀ ↥K₀).injective.comp (IsFractionRing.injective A₀ L₀)
  haveI : Module.Flat A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) := inferInstance

  obtain ⟨_, hNoethÂ, -⟩ :=
    AdicCompletion.exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing A (IsLocalRing.maximalIdeal A)

  obtain ⟨E₀, hE₀const, hE₀Y⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq A₀ (↥K₀) j₀ _ y₀ rfl
  obtain ⟨E₁, hE₁const, hE₁Y⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq A (↥K) j _ y rfl
  have hgermconst₀ : ∀ a : A₀, (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ⊤ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀) trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A₀ (↥K₀) j₀).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a))) =
      (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀) ⟨y₀, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) a) := by
    intro a
    apply (E₀.commRingCatIsoToRingEquiv).injective
    change E₀.hom.hom _ = E₀.hom.hom _
    rw [hE₀const, hE₀Y, IsScalarTower.algebraMap_apply A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (Localization.AtPrime y₀.asIdeal)]
  have hgermconst : ∀ a : A, (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
      (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) ⟨y, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)) (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a) := by
    intro a
    apply (E₁.commRingCatIsoToRingEquiv).injective
    change E₁.hom.hom _ = E₁.hom.hom _
    rw [hE₁const, hE₁Y, IsScalarTower.algebraMap_apply A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal)]
  have hϖy : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := by
    by_contra hnot
    have hu : IsUnit (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal) (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime y.asIdeal) y.asIdeal _).mpr hnot
    rw [← hE₁Y, ← hgermconst, ← hϖz] at hu
    have hu' : IsUnit ϖz := (isUnit_map_iff E₁.commRingCatIsoToRingEquiv ϖz).mp hu
    exact (IsLocalRing.mem_maximalIdeal _).mp hz hu'

  have h5bd₀ := AlgebraicCurve.TwoChartIntegralModel.exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_dominates
      A₀ (↥K₀) j₀ y₀ ⟨y₀, trivial, rfl⟩ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (RingHom.id _) (fun _ _ h => h)
      (fun x => ⟨x, 1, by simpa using (Ideal.ne_top_iff_one _).mp hy₀max.ne_top, by simp⟩)
      (by simpa only [Ideal.comap_id] using hy₀max)
  simp only [RingHom.id_apply] at h5bd₀
  obtain ⟨ez₀, hez₀⟩ := h5bd₀

  let e₀' : AdicCompletion y₀.asIdeal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) ≃+* MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀} :=
    ez₀.symm.trans e₀
  have he₀' : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), e₀' (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AdicCompletion y₀.asIdeal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) b) =
      e₀ (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀))) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀) ⟨y₀, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) b)) := by
    intro b
    show e₀ (ez₀.symm _) = _
    congr 1
    rw [RingEquiv.symm_apply_eq]
    exact (hez₀ b).symm

  have hg₀cc : MvPowerSeries.constantCoeff (MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀) ∈ IsLocalRing.maximalIdeal W₀ := by
    have h1 := WASM.constantCoeff_eq_zero_of_mem_pow (q + 2) (by omega) _ hf₀
    have h2 : MvPowerSeries.constantCoeff (DrinfeldCurve.LocalChart.drinfeldForm q W₀) = 0 := by
      have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
      unfold DrinfeldCurve.LocalChart.drinfeldForm
      simp [MvPowerSeries.constantCoeff_X, hq0]
    rw [map_sub, h2, sub_zero] at h1
    simp only [map_sub, map_mul, MvPowerSeries.constantCoeff_C, h1, zero_mul, sub_zero]
    refine Ideal.mul_mem_right _ _ ?_
    rw [hσ₀ϖ]; exact Ideal.mem_span_singleton_self _
  obtain ⟨ρ, hρsurj, hρker, hρcongr⟩ :=
    AdicCompletion.exists_ringHom_residueField_surjective_of_ringEquiv_mvPowerSeries_quotient
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) y₀.asIdeal W₀ (MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀) hg₀cc e₀'

  letI algA₀W₀ : Algebra A₀ W₀ := σ₀.toAlgebra
  have hσ₀alg : ∀ a : A₀, algebraMap A₀ W₀ a = σ₀ a := fun _ => rfl
  have hρA : ∀ a : A₀, ρ (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) a) = IsLocalRing.residue W₀ (algebraMap A₀ W₀ a) := by
    intro a
    apply hρcongr
    rw [he₀', ← hgermconst₀, hCONST₀ a, hσ₀alg, sub_self]
    exact Ideal.zero_mem _
  haveI : IsLocalHom (algebraMap A₀ W₀) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hmem : a ∈ IsLocalRing.maximalIdeal A₀ := (IsLocalRing.mem_maximalIdeal _).mpr hna
    rw [hϖ₀, Ideal.mem_span_singleton'] at hmem
    obtain ⟨r, rfl⟩ := hmem
    have hmem' : σ₀ (r * ϖ₀) ∈ IsLocalRing.maximalIdeal W₀ := by
      rw [map_mul, hσ₀ϖ]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem' ha
  have hW₀ : IsLocalRing.maximalIdeal W₀ = (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ W₀) := by
    rw [hσ₀ϖ, hϖ₀, Ideal.map_span, Set.image_singleton, hσ₀alg]
  obtain ⟨hfinW₀, hsepW₀⟩ := WASM.finite_and_isSeparable_residueField A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) W₀ ρ hρsurj hρA
  haveI := hfinW₀
  haveI := hsepW₀

  haveI := y.isPrime
  haveI hPprime : (y.asIdeal.comap (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).IsPrime := Ideal.comap_isPrime _ _
  have hy₀𝔪 : ∀ a ∈ IsLocalRing.maximalIdeal A₀, algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) a ∈ y₀.asIdeal := by
    intro a ha
    rw [hϖ₀, Ideal.mem_span_singleton'] at ha
    obtain ⟨r, rfl⟩ := ha
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hϖ₀y₀
  have hP₀ : ∀ b ∈ y₀.asIdeal, (1 : A) ⊗ₜ[A₀] b ∈ y.asIdeal.comap (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) := by
    intro b hb
    refine Ideal.mem_comap.mpr ?_
    show β ((1 : A) ⊗ₜ[A₀] b) ∈ y.asIdeal
    rw [hβ, map_one, one_mul, ← Ideal.mem_comap, hcy]; exact hb
  have hPA : ∀ a ∈ IsLocalRing.maximalIdeal A, a ⊗ₜ[A₀] (1 : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) ∈ y.asIdeal.comap (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) := by
    intro a ha
    refine Ideal.mem_comap.mpr ?_
    show β (a ⊗ₜ[A₀] (1 : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))) ∈ y.asIdeal
    rw [hβ, map_one, mul_one]
    rw [hϖ, Ideal.mem_span_singleton'] at ha
    obtain ⟨r, rfl⟩ := ha
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hϖy
  obtain ⟨χ, hχA₀, hPker⟩ :=
    Algebra.TensorProduct.exists_ringHom_residueField_eq_ker_lift_of_isPrime_of_isAlgClosed A₀ A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) y₀.asIdeal hy₀𝔪
      (y.asIdeal.comap (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))) hP₀ hPA

  have hχy₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), ρ b = 0 → χ b = 0 := by
    intro b hb
    have hb' : b ∈ y₀.asIdeal := by rw [← hρker]; exact hb
    have h1 := hP₀ b hb'
    rw [hPker, RingHom.mem_ker] at h1
    simpa using h1
  obtain ⟨χbar, hχbar⟩ := WASM.exists_comp_eq_of_surjective ρ hρsurj χ hχy₀
  have hχbarA₀ : ∀ a : A₀, χbar (IsLocalRing.residue W₀ (algebraMap A₀ W₀ a)) =
      IsLocalRing.residue A (algebraMap A₀ A a) := by
    intro a; rw [← hρA, hχbar, hχA₀]

  obtain ⟨ψ, hψσ, hψloc, hψres⟩ :=
    IsLocalRing.exists_ringHom_adicCompletion_of_isDiscreteValuationRing_of_maximalIdeal_eq_map_of_residueField
      A₀ A hinj W₀ hW₀ χbar hχbarA₀

  have he₀'A : ∀ a : A₀, e₀' (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AdicCompletion y₀.asIdeal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) a)) =
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀}) (MvPowerSeries.C (algebraMap A₀ W₀ a)) := by
    intro a; rw [he₀', ← hgermconst₀, hCONST₀ a, hσ₀alg]
  have hχcompat : ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (w : W₀),
      e₀' (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AdicCompletion y₀.asIdeal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) b) - Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀}) (MvPowerSeries.C w) ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1} ⊔
          (IsLocalRing.maximalIdeal W₀).map (MvPowerSeries.C : W₀ →+* MvPowerSeries (Fin 2) W₀)).map
          (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})) →
      ∃ a : A, IsLocalRing.residue A a = χ b ∧
        ψ w - algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
    intro b w hbw
    obtain ⟨a, ha, ha'⟩ := hψres w
    exact ⟨a, by rw [ha, ← hρcongr b w hbw, hχbar], ha'⟩
  obtain ⟨h𝔪max, e5, he5A, he5B⟩ :=
    AdicCompletion.exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat A₀ A hinj ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) y₀.asIdeal W₀ hW₀
      (MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀) e₀' he₀'A ψ hψσ χ hχA₀ hχcompat
  rw [← hPker] at h𝔪max

  obtain ⟨ez, hez⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_dominates
      A (↥K) j y ⟨y, trivial, rfl⟩ (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) β.injective
      (fun x => ⟨β.symm x, 1, by simpa using (Ideal.ne_top_iff_one _).mp y.isPrime.ne_top, by simp⟩) h𝔪max

  let f : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) := MvPowerSeries.map ψ f₀
  let u : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) := MvPowerSeries.map ψ u₀
  let v : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    MvPowerSeries.C (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) w₀) * MvPowerSeries.map ψ v₀
  have hu : IsUnit u := hu₀.map _
  have hv : IsUnit v := ((hw₀u.map _).map _).mul (hv₀.map _)
  have hf : f - DrinfeldCurve.LocalChart.drinfeldForm q (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)), MvPowerSeries.X 1}) ^ (q + 2) := by
    have hD : MvPowerSeries.map ψ (DrinfeldCurve.LocalChart.drinfeldForm q W₀) =
        DrinfeldCurve.LocalChart.drinfeldForm q (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
      unfold DrinfeldCurve.LocalChart.drinfeldForm
      simp only [map_sub, map_mul, map_pow, MvPowerSeries.map_X]
    have h1 := Ideal.mem_map_of_mem (MvPowerSeries.map ψ) hf₀
    rw [Ideal.map_pow, Ideal.map_span, Set.image_pair, MvPowerSeries.map_X, MvPowerSeries.map_X, map_sub, hD] at h1
    exact h1
  have hψσ' : ∀ a : A₀, ψ (σ₀ a) = algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) (algebraMap A₀ A a) := fun a => hψσ a
  have hrel : MvPowerSeries.map ψ (MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀) =
      MvPowerSeries.C (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) t) * v - f * u := by
    simp only [map_sub, map_mul, MvPowerSeries.map_C, f, u, v, hψσ', hw₀, map_mul]
    ring

  have hspan : Ideal.span {MvPowerSeries.map ψ (MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀)} =
      Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u} := by rw [hrel]
  obtain ⟨e, he⟩ : ∃ e : (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ≃+*
      MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u},
      ∀ x, e x = Ideal.quotEquivOfEq hspan (e5 (WASM.adicCongr hPker (ez x))) :=
    ⟨ez.trans ((WASM.adicCongr hPker).trans (e5.trans (Ideal.quotEquivOfEq hspan))), fun _ => rfl⟩
  have hβA : ∀ a : A, algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a = (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) (algebraMap A (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) a) := by
    intro a
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show _ = β _
    rw [hβ, map_one, mul_one]
  have hβc : ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), c x = (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ((1 : A) ⊗ₜ[A₀] x) := by
    intro x; show _ = β _; rw [hβ, map_one, one_mul]
  have hez' : ∀ b : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)), ez (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y)) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) ⟨y, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)) ((β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) b))) =
      algebraMap (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (AdicCompletion (y.asIdeal.comap (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))) (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))) b := fun b => hez b
  have hCONST : ∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y)) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
      Ideal.Quotient.mk _ (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a)) := by
    intro a
    have h0 : (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
        (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) ⟨y, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)) ((β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) (algebraMap A (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) a)) :=
      (hgermconst a).trans (congrArg (fun w => (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) ⟨y, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)) w) (hβA a))
    have h1 := (congrArg (fun w => ez (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y)) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) w)) h0).trans (hez' (algebraMap A (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) a))
    refine (he _).trans ((congrArg (fun w => Ideal.quotEquivOfEq hspan (e5 (WASM.adicCongr hPker w))) h1).trans ?_)
    rw [WASM.adicCongr_algebraMap, he5A, Ideal.quotEquivOfEq_mk]
  have hCOMPAT : ∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (s : MvPowerSeries (Fin 2) W₀),
      e₀ (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀))) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀) ⟨y₀, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) x)) = Ideal.Quotient.mk _ s →
      e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y)) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) ⟨y, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)) (c x))) = Ideal.Quotient.mk _ (MvPowerSeries.map ψ s) := by
    intro x s hxs
    have h1 := (congrArg (fun w => ez (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y)) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) ⟨y, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)) w))) (hβc x)).trans
      (hez' ((1 : A) ⊗ₜ[A₀] x))
    refine (he _).trans ((congrArg (fun w => Ideal.quotEquivOfEq hspan (e5 (WASM.adicCongr hPker w))) h1).trans ?_)
    rw [WASM.adicCongr_algebraMap, he5B x s ((he₀' x).trans hxs), Ideal.quotEquivOfEq_mk]
  have hCONSTY : ∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y)) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) ⟨y, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)) (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a))) =
      Ideal.Quotient.mk _ (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a)) := by
    intro a; rw [← hgermconst]; exact hCONST a

  haveI := y₀.isPrime
  have hnoeth : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := WASM.isNoetherianRing_of_baseChange A₀ A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) c β hβ
  have hqW₀ : (q : W₀) ∈ IsLocalRing.maximalIdeal W₀ := by
    rw [← map_natCast (algebraMap A₀ W₀) q]
    exact map_nonunit (algebraMap A₀ W₀) _ hA₀q
  have hqW : (q : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
    rw [← map_natCast (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) q, AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ hAq
  have hπ : ∃ r : (AdicCompletion (IsLocalRing.maximalIdeal A) A), ψ (σ₀ ϖ₀) = algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ * r := by
    have ht' : t ∈ Ideal.span {ϖ} := hϖ ▸ ht𝔪
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp ht'
    refine ⟨algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) (r * w₀), ?_⟩
    rw [hψσ', hw₀, ← hr, ← map_mul]
    congr 1; ring
  have hrelmem : MvPowerSeries.map ψ (MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀) ∈
      Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u} := by
    rw [← hrel]; exact Ideal.mem_span_singleton_self _

  obtain ⟨hEQfin, hEQfix, hEQlin⟩ := WASM_eq_riders q M' hqM' ℓ hℓ12 hℓM' L ζ hζ ξ hξ hζξ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ t ht _ ϖz hϖz hz y rfl hss
      L₀ ζ₀ hζ₀ ξ₀ hξ₀ hζξ₀ K₀ hK₀ A₀ hA₀q hζ₀A j₀ hj₀ ϖ₀ hϖ₀ _ ϖz₀ hϖz₀ hz₀ y₀ rfl hss₀
      i hiζ hiξ hinj hA₀A ⟨w₀, hw₀u, hw₀⟩ cK hcK hcKj c hc hcy β hβ
      W₀ σ₀ hσ₀ϖ f₀ u₀ v₀ hu₀ hv₀ hf₀ e₀ hriders₀
      ψ hψσ' hψloc f u v e hrel hCONST hCOMPAT hCONSTY hNoethÂ

  have hBRdist := WASM_brdist_transport q W₀ (AdicCompletion (IsLocalRing.maximalIdeal A) A) ψ (σ₀ ϖ₀) hσ₀ϖ hqW₀ hqW f₀ u₀ v₀ hu₀ hf₀
      (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u) hrelmem (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ) hπ
      ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
      ((e₀ : (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀))) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀))) →+* (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})).comp (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀))) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀)))))
      ((e : (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) →+* (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})).comp (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y)) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y)))))
      (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀) ⟨y₀, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom))
      (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) ⟨y, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)) c
      (fun p₁ p₂ _ _ hp => WASM.eq_of_comap_eq_of_iso_localization y₀.asIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀))
        (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀) ⟨y₀, trivial, rfl⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) E₀.commRingCatIsoToRingEquiv (fun b => hE₀Y b) p₁ p₂ hp)
      (fun x s hxs => hCOMPAT x s hxs) hBRdist₀
  refine ⟨ψ, f, u, v, hu, hv, hf, e, hψσ', hψloc, rfl, hCOMPAT, hCONST, hEQfin, hEQfix, hEQlin, hBRdist, ?_⟩

  intro P hP hX hϖP htan
  have hQ : (P.comap (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u}))).IsPrime :=
    Ideal.comap_isPrime _ _
  have hQg : MvPowerSeries.map ψ (MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀) ∈
      P.comap (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})) := by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hrelmem]; exact P.zero_mem
  have hQπ : MvPowerSeries.C (ψ (σ₀ ϖ₀)) ∈
      P.comap (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})) := by
    obtain ⟨r, hr⟩ := hπ
    rw [Ideal.mem_comap, hr, map_mul, map_mul]
    exact P.mul_mem_right _ hϖP
  obtain ⟨h₀, hh₀, hh₀P⟩ :=
    DrinfeldCurve.LocalChart.exists_mem_sq_map_add_mem_of_linearPart_mem_of_isPrime q W₀ (AdicCompletion (IsLocalRing.maximalIdeal A) A) ψ (σ₀ ϖ₀) hσ₀ϖ
      hqW₀ hqW f₀ u₀ v₀ hu₀ hf₀ _ hQ hQg (by simpa only [Ideal.mem_comap] using hX) hQπ 1 0
      (by simpa only [Int.cast_one, Int.cast_zero, Ideal.mem_comap] using htan)
  have hBR' : ∃ h₀ ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
        (MvPowerSeries.map ψ (MvPowerSeries.C (1 : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₀) * MvPowerSeries.X 1 + h₀)) ∈ P :=
    ⟨h₀, hh₀, by simpa only [Int.cast_one, Int.cast_zero, Ideal.mem_comap] using hh₀P⟩
  exact ModularCurve.FullLevel.AuxLevelOne.forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_baseChange_of_cyclotomic_of_isPrimitiveRoot_mul_of_dvd
      q M' hqM' ℓ hℓ12 hℓM' L ζ hζ ξ hξ hζξ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ t ht _ ϖz hϖz hz y rfl hss
      L₀ ζ₀ hζ₀ ξ₀ hξ₀ hζξ₀ K₀ hK₀ A₀ hA₀q hζ₀A j₀ hj₀ ϖ₀ hϖ₀ _ ϖz₀ hϖz₀ hz₀ y₀ rfl hss₀
      i hiζ hiξ hinj hA₀A ⟨w₀, hw₀u, hw₀⟩ cK hcK hcKj c hc hcy β hβ
      W₀ σ₀ hσ₀ϖ f₀ u₀ v₀ hu₀ hv₀ hf₀ e₀ ψ hψσ' f u v e hrelmem hBRanchor₀ hCONST hCOMPAT hnoeth P hP hX hϖP htan hBR'

end S_ModularCurve_FullLevel_AuxLevelOne_exists_ringEquiv_adicCompletion_stalk_drinfeldChart_baseChange_of_cyclotomicWitness_of_isAlgClosed_of_isPrimitiveRoot_mul_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_ringEquiv_adicCompletion_stalk_drinfeldChart_baseChange_of_cyclotomicWitness_of_isAlgClosed_of_isPrimitiveRoot_mul_of_dvd (solution)
