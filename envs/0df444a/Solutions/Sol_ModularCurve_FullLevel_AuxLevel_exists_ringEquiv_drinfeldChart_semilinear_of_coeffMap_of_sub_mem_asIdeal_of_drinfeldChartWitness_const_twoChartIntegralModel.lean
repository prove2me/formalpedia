-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_ringEquiv_drinfeldChart_semilinear_of_coeffMap_of_sub_mem_asIdeal_of_drinfeldChartWitness_const_twoChartIntegralModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/9a786786-3d89-5116-9768-465a6e062aee

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_germ_iotaFin_algebraMap_eq_germ_top_toBase_appTop
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv
import Theorems.Thm_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Theorems.Thm_HenselianLocalRing_existsUnique_isRoot_map_residue_eq_of_isRoot_of_derivative_ne_zero
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_ringEquiv_drinfeldChart_semilinear_of_coeffMap_of_sub_mem_asIdeal_of_drinfeldChartWitness_const_twoChartIntegralModel
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
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
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
      [IsAdicComplete (IsLocalRing.maximalIdeal W) W] (σ : A →+* W)
      (hσϖ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
      (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})

    (hconst :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
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
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))))
    :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
      ∀ (σL : L ≃+* L) (σA : A ≃+* A),

        (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →

        (∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A) →
        ∀ τ : ↥K ≃+* ↥K,

          (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),

            (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ.symm a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) →

            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal)) →
            ∃ (θ : S ≃+* S) (σW : W ≃+* W),

              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                θ (e (toC (germY a))) = e (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

              (∀ a : A, σW (σ a) = σ (σA a)) ∧
              (∀ w : W, σW w - w ∈ IsLocalRing.maximalIdeal W) ∧
              (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) := by
  classical
  intro STK CMP toC S mkS germY σL σA hcompat hinert τ hτ hpres hsymm hfix
  subst hy

  let R : Type := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
  let Loc : Type := Localization.AtPrime y.asIdeal
  let Ψ : R →+* S := (e : CMP →+* S).comp (toC.comp germY)
  let cW : W →+* S := mkS.comp (MvPowerSeries.C)
  have hΨ : ∀ a : R, Ψ a = e (toC (germY a)) := fun a => rfl
  have hcW : ∀ w : W, cW w = mkS (MvPowerSeries.C w) := fun w => rfl

  let τR : R ≃+* R :=
    { toFun := fun a => ⟨τ a, hpres a a.2⟩
      invFun := fun a => ⟨τ.symm a, hsymm a a.2⟩
      left_inv := fun a => Subtype.ext (τ.symm_apply_apply (a : ↥K))
      right_inv := fun a => Subtype.ext (τ.apply_symm_apply (a : ↥K))
      map_mul' := fun a b => Subtype.ext (by
        show τ ((a : ↥K) * (b : ↥K)) = τ (a : ↥K) * τ (b : ↥K)
        exact map_mul τ _ _)
      map_add' := fun a b => Subtype.ext (by
        show τ ((a : ↥K) + (b : ↥K)) = τ (a : ↥K) + τ (b : ↥K)
        exact map_add τ _ _) }
  have hτR : ∀ a : R, τR a = (τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a := fun a => rfl
  have hτR_coe : ∀ a : R, ((τR a : R) : ↥K) = τ a := fun a => rfl
  have hfixR : ∀ a : R, τR a - a ∈ y.asIdeal := fun a => by rw [hτR]; exact hfix a
  have hyτ : ∀ a : R, τR a ∈ y.asIdeal ↔ a ∈ y.asIdeal := by
    intro a
    have h := hfixR a
    constructor
    · intro h1; have := Ideal.sub_mem _ h1 h; rwa [sub_sub_cancel] at this
    · intro h1; have := Ideal.add_mem _ h h1; rwa [sub_add_cancel] at this
  have hyτsymm : ∀ a : R, τR.symm a ∈ y.asIdeal ↔ a ∈ y.asIdeal := by
    intro a
    conv_rhs => rw [← τR.apply_symm_apply a]
    exact (hyτ (τR.symm a)).symm
  have hmapy : y.asIdeal.primeCompl.map τR.toMonoidHom = y.asIdeal.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact fun h => ha ((hyτ a).mp h)
    · intro hx
      exact ⟨τR.symm x, fun h => hx ((hyτsymm x).mp h), τR.apply_symm_apply x⟩
  let τy : Loc ≃+* Loc := IsLocalization.ringEquivOfRingEquiv Loc Loc τR hmapy
  have hτy : ∀ a : R, τy (algebraMap R Loc a) = algebraMap R Loc (τR a) := fun a =>
    IsLocalization.ringEquivOfRingEquiv_eq hmapy a

  obtain ⟨est, hest_base, hest_chart⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin A (↥K) j y ⟨y, trivial, rfl⟩
  let eST : STK ≃+* Loc := est.commRingCatIsoToRingEquiv
  have heST : ∀ a : R, eST (germY a) = algebraMap R Loc a := fun a => hest_chart a
  have heST_base : ∀ r : A, eST ((((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤
      ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) trivial).hom
        (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r)))) = algebraMap A Loc r := fun r => hest_base r

  let τSTK : STK ≃+* STK := (eST.trans τy).trans eST.symm
  have hτSTK : ∀ a : R, τSTK (germY a) = germY (τR a) := by
    intro a
    show eST.symm (τy (eST (germY a))) = germY (τR a)
    rw [heST, hτy, ← heST, RingEquiv.symm_apply_apply]
  obtain ⟨τC, hτC⟩ := IsLocalRing.exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv τSTK
  let θ : S ≃+* S := (e.symm.trans τC).trans e
  have hθ : ∀ s : S, θ s = e (τC (e.symm s)) := fun s => rfl
  have hθΨ : ∀ a : R, θ (Ψ a) = Ψ (τR a) := by
    intro a
    rw [hΨ, hΨ, hθ, RingEquiv.symm_apply_apply]
    show e (τC (algebraMap STK CMP (germY a))) = e (algebraMap STK CMP (germY (τR a)))
    rw [hτC, hτSTK]

  have hσϖ𝔪 : σ ϖ ∈ IsLocalRing.maximalIdeal W := by rw [hσϖ]; exact Ideal.subset_span rfl
  have hσ𝔪 : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → σ a ∈ IsLocalRing.maximalIdeal W := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ hσϖ𝔪
  have hf0 : MvPowerSeries.constantCoeff f = 0 := by
    have h1 : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} :=
      Ideal.pow_le_self (by omega) hf
    have hker : Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} ≤
        RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) W →+* W) := by
      apply Ideal.span_le.mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> simp [RingHom.mem_ker, MvPowerSeries.constantCoeff_X]
    have h2 := hker h1
    rw [RingHom.mem_ker, map_sub] at h2
    have hF : MvPowerSeries.constantCoeff (DrinfeldCurve.LocalChart.drinfeldForm q W) = 0 := by
      simp [DrinfeldCurve.LocalChart.drinfeldForm, MvPowerSeries.constantCoeff_X]
    rwa [hF, sub_zero] at h2
  have hrel_nu : ¬ IsUnit (MvPowerSeries.C (σ ϖ) * v - f * u) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_sub, map_mul, map_mul, MvPowerSeries.constantCoeff_C, hf0,
      zero_mul, sub_zero]
    intro hu'
    exact (IsLocalRing.mem_maximalIdeal _).mp hσϖ𝔪 (isUnit_of_mul_isUnit_left hu')
  have hI0_ne_top : Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u} ≠ ⊤ := by
    intro htop
    rw [Ideal.span_singleton_eq_top] at htop
    exact hrel_nu htop
  haveI hSnt : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hI0_ne_top
  haveI hSloc : IsLocalRing S := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

  have hlift_unit : ∀ g : MvPowerSeries (Fin 2) W, IsUnit (mkS g) → IsUnit g := by
    intro g hgu
    by_contra hg
    obtain ⟨s', hs'⟩ := hgu.exists_right_inv
    obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective s'
    have h1 : mkS (g * g') = 1 := by rw [map_mul]; exact hs'
    rw [← (Ideal.Quotient.mk _).map_one, show mkS = Ideal.Quotient.mk _ from rfl, Ideal.Quotient.eq,
      Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1

    have hgm : g ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) W) := (IsLocalRing.mem_maximalIdeal _).mpr hg
    have hrm : MvPowerSeries.C (σ ϖ) * v - f * u ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) W) :=
      (IsLocalRing.mem_maximalIdeal _).mpr hrel_nu
    have : (1 : MvPowerSeries (Fin 2) W) ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) W) := by
      have h2 : g * g' - c * (MvPowerSeries.C (σ ϖ) * v - f * u) = 1 := by rw [hc, sub_sub_cancel]
      rw [← h2]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hgm) (Ideal.mul_mem_left _ _ hrm)
    exact (IsLocalRing.mem_maximalIdeal _).mp this isUnit_one
  have hcW_mem : ∀ w : W, cW w ∈ IsLocalRing.maximalIdeal S ↔ w ∈ IsLocalRing.maximalIdeal W := by
    intro w
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, hcW]
    constructor
    · intro h hu'; exact h ((hu'.map MvPowerSeries.C).map mkS)
    · intro h hu'
      apply h
      have := hlift_unit _ hu'
      rwa [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C] at this
  have hcWϖ : cW (σ ϖ) ∈ IsLocalRing.maximalIdeal S := (hcW_mem _).mpr hσϖ𝔪
  have hqS : (q : S) ∈ IsLocalRing.maximalIdeal S := by
    have : (q : S) = cW (σ (q : A)) := by simp [hcW]
    rw [this, hcW_mem]
    exact hσ𝔪 _ hAq

  have hgermY_unit : ∀ a : R, a ∉ y.asIdeal → IsUnit (germY a) := by
    intro a ha
    have h1 : IsUnit (algebraMap R Loc a) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff Loc y.asIdeal a).mpr ha
    have h2 := h1.map eST.symm
    rwa [← heST, RingEquiv.symm_apply_apply] at h2
  have hgermY_mem : ∀ a : R, a ∈ y.asIdeal → germY a ∈ IsLocalRing.maximalIdeal STK := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu'
    have hu'' := hu'.map eST
    rw [heST] at hu''
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff Loc y.asIdeal a).mp hu'') ha
  have htoC_nu : ∀ m : STK, m ∈ IsLocalRing.maximalIdeal STK → ¬ IsUnit (toC m) := by
    intro m hm hu'
    have hu'' := hu'.map (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal STK) 1).toRingHom
    have : (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal STK) 1).toRingHom (toC m) = 0 := by
      show (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal STK) 1) (algebraMap STK CMP m) = 0
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, AdicCompletion.evalₐ_of,
        Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact hm
    rw [this] at hu''
    have h1 : (IsLocalRing.maximalIdeal STK) ^ 1 ≠ ⊤ := by
      rw [pow_one]; exact Ideal.IsPrime.ne_top inferInstance
    haveI : Nontrivial (STK ⧸ IsLocalRing.maximalIdeal STK ^ 1) := Ideal.Quotient.nontrivial_iff.mpr h1
    exact not_isUnit_zero hu''
  have he_mem : ∀ c : CMP, ¬ IsUnit c → e c ∈ IsLocalRing.maximalIdeal S := by
    intro c hc
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu'
    apply hc
    have := hu'.map (e.symm : S →+* CMP)
    simpa using this
  have hΨ_mem : ∀ a : R, a ∈ y.asIdeal → Ψ a ∈ IsLocalRing.maximalIdeal S := by
    intro a ha
    rw [hΨ]
    exact he_mem _ (htoC_nu _ (hgermY_mem a ha))
  have hΨ_unit : ∀ a : R, a ∉ y.asIdeal → IsUnit (Ψ a) := by
    intro a ha
    rw [hΨ]
    exact ((hgermY_unit a ha).map toC).map (e : CMP →+* S)

  have hΨA : ∀ a : A, Ψ (algebraMap A R a) = cW (σ a) := by
    intro a
    rw [hΨ, hcW]
    have h1 := AlgebraicCurve.TwoChartIntegralModel.germ_iotaFin_algebraMap_eq_germ_top_toBase_appTop A (↥K) j
      ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) y rfl a
    have h2 : germY (algebraMap A R a) = (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤
      ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) trivial).hom
        (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) := h1
    rw [h2]
    exact hconst a
  have hτRA : ∀ a : A, τR (algebraMap A R a) = algebraMap A R (σA a) := by
    intro a
    apply Subtype.ext
    rw [hτR_coe]
    apply Subtype.ext
    rw [hτ]
    have e1 : ((algebraMap A R a : R) : ↥K) = algebraMap L ↥K (algebraMap A L a) := by
      rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L ↥K]
    have e2 : ((algebraMap A R (σA a) : R) : ↥K) = algebraMap L ↥K (algebraMap A L (σA a)) := by
      rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L ↥K]
    rw [e1, e2, hcompat]
    show ModularCurve.coeffMap σL.toRingHom (algebraMap L (LaurentSeries L) (algebraMap A L a)) =
      algebraMap L (LaurentSeries L) (σL (algebraMap A L a))
    exact ModularCurve.coeffMap_algebraMap σL.toRingHom (algebraMap A L a)
  have hθA : ∀ a : A, θ (cW (σ a)) = cW (σ (σA a)) := by
    intro a
    rw [← hΨA, hθΨ, hτRA, hΨA]

  have hθ𝔪 : ∀ s : S, s ∈ IsLocalRing.maximalIdeal S → θ s ∈ IsLocalRing.maximalIdeal S := by
    intro s hs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
    intro hu'
    apply hs
    have := hu'.map (θ.symm : S →+* S)
    simpa using this

  have hfrac : ∀ r : STK, ∃ c : R, ∃ s : R, s ∉ y.asIdeal ∧ e (toC r) * Ψ s = Ψ c := by
    intro r
    obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl (eST r)
    refine ⟨c, s, s.2, ?_⟩
    have hrs : r * germY (s : R) = germY c := by
      apply eST.injective
      rw [map_mul, heST, heST, ← hcs]
      exact IsLocalization.mk'_spec Loc c s
    rw [hΨ, hΨ, ← map_mul, ← map_mul, hrs]

  have happrox1 : ∀ s : S, ∃ r : STK, s - e (toC r) ∈ IsLocalRing.maximalIdeal S := by
    intro s
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
      ((AdicCompletion.evalₐ (IsLocalRing.maximalIdeal STK) 1) (e.symm s))
    refine ⟨r, ?_⟩
    have hnu : ¬ IsUnit (e.symm s - toC r) := by
      intro hu'
      have hu'' := hu'.map (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal STK) 1).toRingHom
      have : (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal STK) 1).toRingHom (e.symm s - toC r) = 0 := by
        show (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal STK) 1) (e.symm s - algebraMap STK CMP r) = 0
        rw [map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          AdicCompletion.evalₐ_of, ← hr, sub_self]
      rw [this] at hu''
      have h1 : (IsLocalRing.maximalIdeal STK) ^ 1 ≠ ⊤ := by
        rw [pow_one]; exact Ideal.IsPrime.ne_top inferInstance
      haveI : Nontrivial (STK ⧸ IsLocalRing.maximalIdeal STK ^ 1) := Ideal.Quotient.nontrivial_iff.mpr h1
      exact not_isUnit_zero hu''
    have := he_mem _ hnu
    rwa [map_sub, RingEquiv.apply_symm_apply] at this
  let res : S →+* IsLocalRing.ResidueField S := IsLocalRing.residue S
  have hres_sub : ∀ a b : S, res a = res b ↔ a - b ∈ IsLocalRing.maximalIdeal S := fun a b =>
    Ideal.Quotient.mk_eq_mk_iff_sub_mem a b
  have hres_zero : ∀ a : S, res a = 0 ↔ a ∈ IsLocalRing.maximalIdeal S := fun a =>
    Ideal.Quotient.eq_zero_iff_mem
  have hresR : ∀ a : R, res (θ (Ψ a)) = res (Ψ a) := by
    intro a
    rw [hres_sub, hθΨ, ← map_sub]
    exact hΨ_mem _ (hfixR a)
  have hresSTK : ∀ r : STK, res (θ (e (toC r))) = res (e (toC r)) := by
    intro r
    obtain ⟨c, s, hs, hrs'⟩ := hfrac r
    have hu2 : IsUnit (res (Ψ s)) := (hΨ_unit _ hs).map res
    have h5 : res (θ (e (toC r))) * res (Ψ s) = res (e (toC r)) * res (Ψ s) := by
      calc res (θ (e (toC r))) * res (Ψ s) = res (θ (e (toC r))) * res (θ (Ψ s)) := by rw [hresR]
        _ = res (θ (Ψ c)) := by rw [← map_mul, ← map_mul, hrs']
        _ = res (Ψ c) := hresR c
        _ = res (e (toC r)) * res (Ψ s) := by rw [← hrs', map_mul]
    exact hu2.mul_right_cancel h5
  have hres : ∀ s : S, θ s - s ∈ IsLocalRing.maximalIdeal S := by
    intro s
    obtain ⟨r, hm⟩ := happrox1 s
    have : θ s - s = (θ (e (toC r)) - e (toC r)) + (θ (s - e (toC r)) - (s - e (toC r))) := by
      rw [map_sub]; ring
    rw [this]
    exact Ideal.add_mem _ ((hres_sub _ _).mp (hresSTK r)) (Ideal.sub_mem _ (hθ𝔪 _ hm) hm)
  have hresθ : ∀ s : S, res (θ s) = res s := fun s => (hres_sub _ _).mpr (hres s)

  let κ : Type := IsLocalRing.ResidueField S
  have hqκ : (q : κ) = 0 := by
    have h := (hres_zero (q : S)).mpr hqS
    rwa [map_natCast] at h
  haveI hκchar : CharP κ q := (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr hqκ
  letI : Algebra (ZMod q) κ := ZMod.algebra κ q
  let F₀ : IntermediateField (ZMod q) κ := algebraicClosure (ZMod q) κ
  have hF₀ : ∀ x : κ, x ∈ F₀ ↔ IsAlgebraic (ZMod q) x := fun x => mem_algebraicClosure_iff

  have hZalg : ∀ (x : κ) (p : Polynomial ℤ), p.IsPrimitive → Polynomial.eval₂ (Int.castRingHom κ) x p = 0 →
      IsAlgebraic (ZMod q) x := by
    intro x p hp hx
    refine ⟨p.map (Int.castRingHom (ZMod q)), ?_, ?_⟩
    · intro h0
      have hdvd : Polynomial.C (q : ℤ) ∣ p := by
        rw [Polynomial.C_dvd_iff_dvd_coeff]
        intro i
        have : (p.map (Int.castRingHom (ZMod q))).coeff i = 0 := by rw [h0, Polynomial.coeff_zero]
        rw [Polynomial.coeff_map] at this
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp this
      have hu := (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hp) _ hdvd
      rw [Int.isUnit_iff] at hu
      have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
      omega
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      convert hx using 2 <;> first | rfl | (ext n; simp)

  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  haveI hAcz : CharZero A := ⟨fun m n h => Nat.cast_injective (R := L)
    (by simpa only [map_natCast] using congrArg (algebraMap A L) h)⟩
  have hAF : ∀ a : A, res (cW (σ a)) ∈ F₀ := by
    intro a
    haveI hfd : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional (S := {q * ℓ}) (K := ℚ) L
    have halgQ : IsAlgebraic ℚ (algebraMap A L a) := Algebra.IsAlgebraic.isAlgebraic _
    haveI : IsScalarTower ℤ ℚ L := IsScalarTower.of_algebraMap_eq (fun n => by simp)
    have halgZ : IsAlgebraic ℤ (algebraMap A L a) := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr halgQ
    obtain ⟨p, hp0, hpa⟩ := halgZ

    have hpaA : Polynomial.eval₂ (Int.castRingHom A) a p = 0 := by
      apply hinjAL
      rw [Polynomial.hom_eval₂, map_zero]
      rw [Polynomial.aeval_def] at hpa
      convert hpa using 2 <;> first | rfl | (ext n; simp)
    have hprim := Polynomial.eval₂_primPart_eq_zero (f := Int.castRingHom A) (Int.cast_injective) hp0 hpaA
    rw [hF₀]
    apply hZalg _ p.primPart (Polynomial.isPrimitive_primPart p)
    have := congrArg (res.comp (cW.comp σ)) hprim
    rw [Polynomial.hom_eval₂, map_zero] at this
    convert this using 2 <;> first | rfl | (ext n; simp)

  let jR : R := AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j
  have hjF : res (Ψ jR) ∈ F₀ := by
    let Ω : Type := AlgebraicClosure κ
    haveI : CharP Ω q := charP_of_injective_algebraMap (algebraMap κ Ω).injective q
    let φΩ : R →+* Ω := (algebraMap κ Ω).comp (res.comp Ψ)
    have hker : RingHom.ker φΩ = y.asIdeal := by
      ext a
      rw [RingHom.mem_ker]
      show algebraMap κ Ω (res (Ψ a)) = 0 ↔ a ∈ y.asIdeal
      rw [map_eq_zero_iff _ (algebraMap κ Ω).injective, hres_zero]
      constructor
      · intro h
        by_contra ha
        exact (IsLocalRing.mem_maximalIdeal _).mp h (hΨ_unit a ha)
      · exact hΨ_mem a
    have hjss := hss Ω φΩ hker
    have hjpow := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q hjss

    have hjpow' : (res (Ψ jR)) ^ (q ^ 2) = res (Ψ jR) := by
      apply (algebraMap κ Ω).injective
      rw [map_pow]
      exact hjpow
    rw [hF₀]
    refine ⟨Polynomial.X ^ (q ^ 2) - Polynomial.X, ?_, ?_⟩
    · apply Polynomial.Monic.ne_zero
      apply Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow _)
      rw [Polynomial.degree_X_pow, Polynomial.degree_X]
      have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (Fact.out : q.Prime).one_lt
      exact_mod_cast this
    · simp [hjpow']

  have hRF : ∀ a : R, res (Ψ a) ∈ F₀ := by
    intro a
    let g : R →+* κ := res.comp Ψ
    have hadj : Algebra.adjoin A ({(j : ↥K)} : Set ↥K) ≤ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j :=
      AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg A (↥K) {(j : ↥K)}

    have hgen : ∀ (x : ↥K) (hx : x ∈ Algebra.adjoin A ({(j : ↥K)} : Set ↥K)), g ⟨x, hadj hx⟩ ∈ F₀ := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact hjF
      | algebraMap r =>
          have : (⟨algebraMap A (↥K) r, hadj (Subalgebra.algebraMap_mem _ r)⟩ : R) = algebraMap A R r :=
            Subtype.ext (Subalgebra.coe_algebraMap _ r).symm
          rw [this]
          show res (Ψ (algebraMap A R r)) ∈ F₀
          rw [hΨA]; exact hAF r
      | add x y hx hy hpx hpy =>
          have : (⟨x + y, hadj (Subalgebra.add_mem _ hx hy)⟩ : R) = ⟨x, hadj hx⟩ + ⟨y, hadj hy⟩ := rfl
          rw [this, map_add]; exact F₀.add_mem hpx hpy
      | mul x y hx hy hpx hpy =>
          have : (⟨x * y, hadj (Subalgebra.mul_mem _ hx hy)⟩ : R) = ⟨x, hadj hx⟩ * ⟨y, hadj hy⟩ := rfl
          rw [this, map_mul]; exact F₀.mul_mem hpx hpy

    have hint : IsIntegral (Algebra.adjoin A ({(j : ↥K)} : Set ↥K)) (a : ↥K) := a.2
    obtain ⟨p, hpm, hpa⟩ := hint

    let incl : ↥(Algebra.adjoin A ({(j : ↥K)} : Set ↥K)) →+* R := (Subalgebra.inclusion hadj).toRingHom
    have hincl : ∀ c, ((incl c : R) : ↥K) = (c : ↥K) := fun c => rfl
    have hpaR : Polynomial.eval₂ incl a p = 0 := by
      apply Subtype.val_injective
      have h1 := Polynomial.hom_eval₂ p incl (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j).val.toRingHom a

      have h2 : (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j).val.toRingHom.comp incl =
          algebraMap (↥(Algebra.adjoin A ({(j : ↥K)} : Set ↥K))) ↥K := by
        ext c; rfl
      rw [h2] at h1
      show (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j).val.toRingHom (Polynomial.eval₂ incl a p) = (0 : R).val
      rw [h1]
      exact hpa

    have hroot : Polynomial.eval₂ (g.comp incl) (g a) p = 0 := by
      rw [← Polynomial.hom_eval₂, hpaR, map_zero]

    set pκ : Polynomial κ := p.map (g.comp incl) with hpκ
    have hpκm : pκ.Monic := hpm.map _
    have hlifts : pκ ∈ Polynomial.lifts (algebraMap F₀ κ) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [hpκ, Polynomial.coeff_map]
      have hm : (g.comp incl) (p.coeff n) ∈ F₀ := hgen _ (p.coeff n).2
      exact ⟨⟨_, hm⟩, rfl⟩
    obtain ⟨p', hp'map, -, hp'm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hpκm
    have hga : IsIntegral F₀ (g a) := by
      refine ⟨p', hp'm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map, hp'map, hpκ, ← Polynomial.eval₂_eq_eval_map]
      exact hroot
    have halg' : IsAlgebraic F₀ (g a) := hga.isAlgebraic
    have hmem : g a ∈ algebraicClosure F₀ κ := mem_algebraicClosure_iff.mpr halg'
    rw [algebraicClosure.algebraicClosure_eq_bot, IntermediateField.mem_bot] at hmem
    obtain ⟨z, hz⟩ := hmem
    show g a ∈ F₀
    rw [← hz]
    exact z.2

  have hSF : ∀ s : S, res s ∈ F₀ := by
    intro s
    obtain ⟨r, hm⟩ := happrox1 s
    obtain ⟨c, s', hs', hrs'⟩ := hfrac r
    have h1 : res s = res (e (toC r)) := (hres_sub _ _).mpr hm
    have hu : res (Ψ s') ≠ 0 := fun h0 => (IsLocalRing.mem_maximalIdeal _).mp ((hres_zero _).mp h0) (hΨ_unit _ hs')
    have h2 : res (e (toC r)) = res (Ψ c) * (res (Ψ s'))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hu, ← map_mul, hrs']
    rw [h1, h2]
    exact F₀.mul_mem (hRF c) (F₀.inv_mem (hRF s'))

  have hpowκ : ∀ x : κ, ∃ n : ℕ, 0 < n ∧ x ^ (q ^ n) = x := by
    intro x
    have halg : IsAlgebraic (ZMod q) x := by
      obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective x
      exact (hF₀ _).mp (hSF s)
    let Kx : IntermediateField (ZMod q) κ := IntermediateField.adjoin (ZMod q) ({x} : Set κ)
    haveI : FiniteDimensional (ZMod q) Kx := IntermediateField.adjoin.finiteDimensional halg.isIntegral
    haveI : Finite Kx := Module.finite_of_finite (ZMod q)
    letI : Fintype Kx := Fintype.ofFinite _
    haveI : CharP Kx q := charP_of_injective_algebraMap (algebraMap (ZMod q) Kx).injective q
    obtain ⟨n, -, hcard⟩ := FiniteField.card Kx q
    refine ⟨(n : ℕ), n.pos, ?_⟩
    let xK : Kx := ⟨x, IntermediateField.mem_adjoin_simple_self (ZMod q) x⟩
    have h := FiniteField.pow_card xK
    rw [hcard] at h
    have := congrArg (fun t : Kx => (t : κ)) h
    simpa using this

  have hpowS : ∀ s : S, ∃ n : ℕ, 0 < n ∧ s ^ (q ^ n) - s ∈ IsLocalRing.maximalIdeal S := by
    intro s
    obtain ⟨n, hn, h⟩ := hpowκ (res s)
    refine ⟨n, hn, ?_⟩
    rw [← hres_zero, map_sub, map_pow, h, sub_self]
  have hpowW : ∀ w : W, ∃ n : ℕ, 0 < n ∧ w ^ (q ^ n) - w ∈ IsLocalRing.maximalIdeal W := by
    intro w
    obtain ⟨n, hn, h⟩ := hpowS (cW w)
    refine ⟨n, hn, ?_⟩
    rw [← hcW_mem, map_sub, map_pow]
    exact h

  haveI hWhens : HenselianLocalRing W := HenselianLocalRing.of_isAdicComplete_maximalIdeal W
  have hqW : (q : W) ∈ IsLocalRing.maximalIdeal W := by
    have : (q : W) = σ (q : A) := by simp
    rw [this]; exact hσ𝔪 _ hAq
  have hteich : ∀ w : W, ∃ t : W, (∃ n : ℕ, 0 < n ∧ t ^ (q ^ n) = t) ∧ t - w ∈ IsLocalRing.maximalIdeal W := by
    intro w
    obtain ⟨n, hn, hw⟩ := hpowW w
    let h : Polynomial W := Polynomial.X ^ (q ^ n) - Polynomial.X
    have hqn1 : 1 < q ^ n := Nat.one_lt_pow hn.ne' (Fact.out : q.Prime).one_lt
    have hmonic : h.Monic := by
      apply Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow _)
      rw [Polynomial.degree_X_pow, Polynomial.degree_X]
      exact_mod_cast hqn1
    have hmapid : h.map (algebraMap W W) = h := by simp
    have hroot : ((h.map (algebraMap W W)).map (IsLocalRing.residue W)).IsRoot (IsLocalRing.residue W w) := by
      rw [hmapid, Polynomial.IsRoot, Polynomial.eval_map]
      simp only [h, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
      rw [← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact hw
    have hsimple : ¬ ((h.map (algebraMap W W)).derivative.map (IsLocalRing.residue W)).IsRoot (IsLocalRing.residue W w) := by
      rw [hmapid]
      have hder : h.derivative = Polynomial.C ((q ^ n : ℕ) : W) * Polynomial.X ^ (q ^ n - 1) - 1 := by
        simp only [h, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X,
          Polynomial.C_eq_natCast]
      have hqres : IsLocalRing.residue W ((q ^ n : ℕ) : W) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff, Nat.cast_pow]
        exact Ideal.pow_mem_of_mem _ hqW _ hn
      rw [hder, Polynomial.IsRoot, Polynomial.eval_map]
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_one, hqres, zero_mul, zero_sub]
      exact neg_ne_zero.mpr one_ne_zero
    obtain ⟨t, ⟨ht, htres⟩, -⟩ :=
      HenselianLocalRing.existsUnique_isRoot_map_residue_eq_of_isRoot_of_derivative_ne_zero W h hmonic
        (IsLocalRing.residue W w) hroot hsimple
    refine ⟨t, ⟨n, hn, ?_⟩, ?_⟩
    · rw [hmapid, Polynomial.IsRoot] at ht
      simp only [h, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] at ht
      exact sub_eq_zero.mp ht
    · rw [← IsLocalRing.residue_eq_zero_iff, map_sub, htres, sub_self]

  have hrootuniq : ∀ (N : ℕ) (a b : S), (N : S) ∈ IsLocalRing.maximalIdeal S → a ^ N = a → b ^ N = b →
      a - b ∈ IsLocalRing.maximalIdeal S → a = b := by
    intro N a b hN ha hb hab

    have hgs := geom_sum₂_mul a b N
    rw [ha, hb] at hgs

    have hsum : res (∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) = 0 := by
      have hab' : res a = res b := (hres_sub _ _).mpr hab
      rw [map_sum]
      simp only [map_mul, map_pow, hab']
      have : ∀ i ∈ Finset.range N, res b ^ i * res b ^ (N - 1 - i) = res b ^ (N - 1) := by
        intro i hi
        rw [← pow_add]; congr 1
        have := Finset.mem_range.mp hi; omega
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have : (N : κ) = 0 := by
        have := (hres_zero (N : S)).mpr hN
        rwa [map_natCast] at this
      rw [this, zero_mul]
    have hunit : IsUnit (1 - ∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) := by
      by_contra hnu
      have hm : (1 - ∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) ∈ IsLocalRing.maximalIdeal S :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [← hres_zero, map_sub, map_one, hsum, sub_zero] at hm
      exact one_ne_zero hm
    have hzero : (1 - ∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) * (a - b) = 0 := by
      rw [sub_mul, one_mul, hgs, sub_self]
    exact sub_eq_zero.mp ((hunit.mul_right_eq_zero).mp hzero)
  have hθT : ∀ t : W, (∃ n : ℕ, 0 < n ∧ t ^ (q ^ n) = t) → θ (cW t) = cW t := by
    rintro t ⟨n, hn, ht⟩
    apply hrootuniq (q ^ n)
    · rw [Nat.cast_pow]; exact Ideal.pow_mem_of_mem _ hqS _ hn
    · rw [← map_pow, ← map_pow, ht]
    · rw [← map_pow, ht]
    · exact hres _

  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp hinjAL
  obtain ⟨htj, hFD, hsep⟩ :=
    ModularCurve.FullLevel.AuxLevel.transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_charZero
      q M' ℓ L K hK A j hj
  obtain ⟨hFTfin, hFTinf⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep
  letI algASTK : Algebra A STK := RingHom.toAlgebra
    (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) trivial).hom.comp
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
  obtain ⟨hSTKnoeth, -, hSTKdom, hinjASTK⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
      A (↥K) hinjAK j hFTfin hFTinf ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) (fun r => rfl)
  haveI := hSTKnoeth
  haveI hCMPnoeth : IsNoetherianRing CMP :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing (IsLocalRing.maximalIdeal STK)
  haveI hSnoeth : IsNoetherianRing S := isNoetherianRing_of_ringEquiv CMP e
  have hKrull : ∀ x : S, (∀ n : ℕ, x ∈ IsLocalRing.maximalIdeal S ^ n) → x = 0 := by
    intro x hx
    have h := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal S) (Ideal.IsPrime.ne_top inferInstance)
    have : x ∈ (⨅ i : ℕ, IsLocalRing.maximalIdeal S ^ i) := Ideal.mem_iInf.mpr hx
    rw [h] at this
    exact this

  have hΨA' : ∀ a : A, Ψ (algebraMap A R a) = e (toC (algebraMap A STK a)) := by
    intro a
    rw [hΨ]
    congr 2
    exact AlgebraicCurve.TwoChartIntegralModel.germ_iotaFin_algebraMap_eq_germ_top_toBase_appTop A (↥K) j
      ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) y rfl a
  haveI : IsHausdorff (IsLocalRing.maximalIdeal STK) STK :=
    IsHausdorff.of_isDomain (IsLocalRing.maximalIdeal STK) (Ideal.IsPrime.ne_top inferInstance)
  have htoCinj : ∀ r : STK, toC r = 0 → r = 0 := by
    intro r hr
    have h1 : AdicCompletion.of (IsLocalRing.maximalIdeal STK) STK r = 0 := by
      rw [← hr]
      show _ = algebraMap STK CMP r
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have h2 : AdicCompletion.of (IsLocalRing.maximalIdeal STK) STK r = AdicCompletion.of (IsLocalRing.maximalIdeal STK) STK 0 := by
      rw [h1, map_zero]
    exact AdicCompletion.of_injective (IsLocalRing.maximalIdeal STK) STK h2
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_isField A
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hϖ, h0, Ideal.span_singleton_eq_bot]
  have hcWσpow : ∀ n : ℕ, cW (σ ϖ) ^ n ≠ 0 := by
    intro n h0
    rw [← map_pow, ← map_pow, ← hΨA, hΨA'] at h0
    have h1 : toC (algebraMap A STK (ϖ ^ n)) = 0 := by
      have := congrArg e.symm h0
      rwa [RingEquiv.symm_apply_apply, map_zero] at this
    have h2 := hinjASTK (by rw [htoCinj _ h1, map_zero] : algebraMap A STK (ϖ ^ n) = algebraMap A STK 0)
    exact hϖ0 (pow_eq_zero_iff'.mp h2).1
  have hcWinj : Function.Injective cW := by
    intro w₁ w₂ h
    by_contra hne
    have hd : w₁ - w₂ ≠ 0 := sub_ne_zero.mpr hne
    have hirr : Irreducible (σ ϖ) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hσϖ
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hirr
    have h0 : cW (w₁ - w₂) = 0 := by rw [map_sub, h, sub_self]
    rw [hu, map_mul, map_pow] at h0
    exact hcWσpow n (((Units.isUnit u).map cW).mul_right_eq_zero.mp h0)

  have hϖ𝔪A : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.subset_span rfl
  have hσϖA : ∃ a₁ : A, σA ϖ = ϖ * a₁ := by
    have : σA ϖ ∈ IsLocalRing.maximalIdeal A := by
      have := Ideal.add_mem _ (hinert ϖ) hϖ𝔪A; rwa [sub_add_cancel] at this
    rw [hϖ, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by rw [← hc, mul_comm]⟩
  have hσϖA' : ∃ a₂ : A, σA.symm ϖ = ϖ * a₂ := by
    have : σA.symm ϖ ∈ IsLocalRing.maximalIdeal A := by
      have h1 := hinert (σA.symm ϖ)
      rw [RingEquiv.apply_symm_apply] at h1
      have := Ideal.sub_mem _ hϖ𝔪A h1; rwa [sub_sub_cancel] at this
    rw [hϖ, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by rw [← hc, mul_comm]⟩
  have hstab : ∀ ψ : S ≃+* S, (∀ t : W, (∃ n : ℕ, 0 < n ∧ t ^ (q ^ n) = t) → ψ (cW t) = cW t) →
      (∃ a : W, ψ (cW (σ ϖ)) = cW (σ ϖ * a)) → ∀ w : W, ∃ w' : W, ψ (cW w) = cW w' := by
    intro ψ hψT haψ w
    obtain ⟨a, hψϖ⟩ := haψ
    have hdig : ∀ r : W, ∃ t r' : W, ψ (cW t) = cW t ∧ r = t + σ ϖ * r' := by
      intro r
      obtain ⟨t, hT, htr⟩ := hteich r
      rw [hσϖ, Ideal.mem_span_singleton'] at htr
      obtain ⟨c, hc⟩ := htr
      exact ⟨t, -c, hψT t hT, by rw [mul_neg, mul_comm, hc]; ring⟩
    choose T Rm hT hTR using hdig
    let step : W × W → ℕ → W × W := fun sr k => (sr.1 + T sr.2 * (σ ϖ * a) ^ k, Rm sr.2)
    let seq : ℕ → W × W := fun n => Nat.rec (0, w) (fun k sr => step sr k) n
    have hseq0 : seq 0 = (0, w) := rfl
    have hseqS : ∀ k, seq (k + 1) = ((seq k).1 + T (seq k).2 * (σ ϖ * a) ^ k, Rm (seq k).2) := fun k => rfl
    have hinv : ∀ n, ψ (cW w) = cW (seq n).1 + cW ((σ ϖ * a) ^ n) * ψ (cW (seq n).2) := by
      intro n
      induction n with
      | zero => rw [hseq0]; simp
      | succ k ih =>
        rw [hseqS]
        dsimp only
        rw [ih]
        have hr : (seq k).2 = T (seq k).2 + σ ϖ * Rm (seq k).2 := hTR _
        conv_lhs => rw [hr]
        rw [map_add cW, map_add ψ, hT, map_mul cW, map_mul ψ, hψϖ]
        simp only [map_add, map_mul, map_pow]
        ring
    have hcauchy : ∀ m n, m ≤ n → (seq m).1 - (seq n).1 ∈ IsLocalRing.maximalIdeal W ^ m := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        rw [hseqS]
        dsimp only
        have : (seq m).1 - ((seq n).1 + T (seq n).2 * (σ ϖ * a) ^ n) =
            ((seq m).1 - (seq n).1) - T (seq n).2 * (σ ϖ * a) ^ n := by ring
        rw [this]
        refine Ideal.sub_mem _ ih (Ideal.mul_mem_left _ _ ?_)
        exact Ideal.pow_le_pow_right hmn (Ideal.pow_mem_pow (Ideal.mul_mem_right _ _ hσϖ𝔪) n)
    obtain ⟨w', hw'⟩ := IsPrecomplete.prec' (I := IsLocalRing.maximalIdeal W) (fun n => (seq n).1) (by
      intro m n hmn
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
      exact hcauchy m n hmn)
    refine ⟨w', ?_⟩
    have hcWpow : ∀ (n : ℕ) (x : W), x ∈ IsLocalRing.maximalIdeal W ^ n → cW x ∈ IsLocalRing.maximalIdeal S ^ n := by
      intro n x hx
      have := Ideal.mem_map_of_mem cW hx
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun z hz => Ideal.mem_comap.mpr ((hcW_mem z).mpr hz)) n this
    have hall : ∀ n, ψ (cW w) - cW w' ∈ IsLocalRing.maximalIdeal S ^ n := by
      intro n
      have h1 : (seq n).1 - w' ∈ IsLocalRing.maximalIdeal W ^ n := by
        have := hw' n
        rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at this
        exact this
      rw [hinv n]
      have : cW (seq n).1 + cW ((σ ϖ * a) ^ n) * ψ (cW (seq n).2) - cW w' =
          cW ((seq n).1 - w') + cW ((σ ϖ * a) ^ n) * ψ (cW (seq n).2) := by rw [map_sub]; ring
      rw [this]
      refine Ideal.add_mem _ (hcWpow _ _ h1) (Ideal.mul_mem_right _ _ ?_)
      rw [map_pow, map_mul]
      exact Ideal.pow_mem_pow (Ideal.mul_mem_right _ _ hcWϖ) n
    exact sub_eq_zero.mp (hKrull _ hall)
  have hθϖ : ∃ a : W, θ (cW (σ ϖ)) = cW (σ ϖ * a) := by
    obtain ⟨a₁, ha₁⟩ := hσϖA
    exact ⟨σ a₁, by rw [hθA, ha₁, map_mul]⟩
  have hθ'T : ∀ t : W, (∃ n : ℕ, 0 < n ∧ t ^ (q ^ n) = t) → θ.symm (cW t) = cW t := by
    intro t ht
    rw [RingEquiv.symm_apply_eq]
    exact (hθT t ht).symm
  have hθ'ϖ : ∃ a : W, θ.symm (cW (σ ϖ)) = cW (σ ϖ * a) := by
    obtain ⟨a₂, ha₂⟩ := hσϖA'
    refine ⟨σ a₂, ?_⟩
    rw [RingEquiv.symm_apply_eq, ← map_mul σ, ← ha₂, hθA, RingEquiv.apply_symm_apply]
  obtain ⟨g, hg⟩ : ∃ g : W → W, ∀ w, θ (cW w) = cW (g w) :=
    ⟨fun w => Classical.choose (hstab θ hθT hθϖ w), fun w => Classical.choose_spec (hstab θ hθT hθϖ w)⟩
  obtain ⟨g', hg'⟩ : ∃ g' : W → W, ∀ w, θ.symm (cW w) = cW (g' w) :=
    ⟨fun w => Classical.choose (hstab θ.symm hθ'T hθ'ϖ w), fun w => Classical.choose_spec (hstab θ.symm hθ'T hθ'ϖ w)⟩

  let σW : W ≃+* W :=
    { toFun := g
      invFun := g'
      left_inv := fun w => hcWinj (by rw [← hg', ← hg, RingEquiv.symm_apply_apply])
      right_inv := fun w => hcWinj (by rw [← hg, ← hg', RingEquiv.apply_symm_apply])
      map_mul' := fun a b => hcWinj (by rw [← hg, map_mul cW a b, map_mul θ, hg, hg, ← map_mul])
      map_add' := fun a b => hcWinj (by rw [← hg, map_add cW a b, map_add θ, hg, hg, ← map_add]) }
  have hσW : ∀ w, σW w = g w := fun w => rfl
  refine ⟨θ, σW, ?_, ?_, ?_, ?_⟩
  · intro a
    exact hθΨ a
  · intro a
    apply hcWinj
    rw [hσW, ← hg, hθA]
  · intro w
    rw [hσW, ← hcW_mem, map_sub, ← hg]
    exact hres _
  · intro w
    rw [hσW, ← hcW, ← hcW, hg]

end S_ModularCurve_FullLevel_AuxLevel_exists_ringEquiv_drinfeldChart_semilinear_of_coeffMap_of_sub_mem_asIdeal_of_drinfeldChartWitness_const_twoChartIntegralModel
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_ringEquiv_drinfeldChart_semilinear_of_coeffMap_of_sub_mem_asIdeal_of_drinfeldChartWitness_const_twoChartIntegralModel (solution)
