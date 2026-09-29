-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.linearPart_row_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_anchor_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/149aa761-7203-59d2-b74d-1d281c05e7fe

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_germ_iotaFin_algebraMap_eq_germ_top_toBase_appTop
import Theorems.Thm_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_isMaximal_and_mem_and_isNoetherianRing_stalk_and_dense_and_mem_iff_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
import Theorems.Thm_DrinfeldCurve_LocalChart_branchPrimes_of_sub_drinfeldForm_mem_pow
import Theorems.Thm_RingHom_eq_of_forall_exists_sub_mem_pow_of_comp_eq
import Theorems.Thm_DrinfeldCurve_LocalChart_mem_of_mk_sum_C_mul_X_mem_span_sq
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_linearPart_row_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_anchor_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
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
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
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

    (hanchor :

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

      (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
        mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
        ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
          toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
            ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
              (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m))
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
            ∀ (θ : S ≃+* S),

              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                θ (e (toC (germY a))) = e (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) →
              ∀ M : Matrix (Fin 2) (Fin 2) W,

                (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                    mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                  (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) →
                M 1 0 ∈ IsLocalRing.maximalIdeal W ∧ M 1 1 - 1 ∈ IsLocalRing.maximalIdeal W := by
  classical
  intro STK CMP toC S mkS germY σL σA hcompat hinert τ hτ hpres θ h1 M hM
  subst hy

  let R : Type := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
  let Loc : Type := Localization.AtPrime y.asIdeal
  let Ψ : R →+* S := (e : CMP →+* S).comp (toC.comp germY)
  let cW : W →+* S := mkS.comp (MvPowerSeries.C)
  have hΨ : ∀ a : R, Ψ a = e (toC (germY a)) := fun a => rfl
  have hcW : ∀ w : W, cW w = mkS (MvPowerSeries.C w) := fun w => rfl
  have hp : q.Prime := Fact.out

  obtain ⟨hymax, hyϖ, hSTKnoeth, hDENSE, hPT⟩ :=
    ModularCurve.FullLevel.AuxLevelOne.isMaximal_and_mem_and_isNoetherianRing_stalk_and_dense_and_mem_iff_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
      q M' hqM' ℓ hℓ12 hℓM' L ζ hζ ξ hξ hζξ H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ
      ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) ϖz hϖz hz y rfl hss
  haveI := hSTKnoeth
  haveI hyp : y.asIdeal.IsPrime := y.isPrime

  obtain ⟨est, hest_base, hest_chart⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin A (↥K) j y ⟨y, trivial, rfl⟩
  let eST : STK ≃+* Loc := est.commRingCatIsoToRingEquiv
  have heST : ∀ a : R, eST (germY a) = algebraMap R Loc a := fun a => hest_chart a

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

  obtain ⟨hCMPloc, hCMPhom, hCMPcomplete, hCMPmap, hCMPdense1⟩ :=
    IsLocalRing.exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq STK
  haveI := hCMPloc
  haveI hCMPnoeth : IsNoetherianRing CMP :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing (IsLocalRing.maximalIdeal STK)
  haveI hSnoeth : IsNoetherianRing S := isNoetherianRing_of_ringEquiv CMP e
  have he𝔪 : (IsLocalRing.maximalIdeal CMP).map (e : CMP →+* S) = IsLocalRing.maximalIdeal S :=
    IsLocalRing.map_ringEquiv_maximalIdeal e

  have hFG : (IsLocalRing.maximalIdeal STK).FG := IsNoetherian.noetherian _
  have hdenseCMP : ∀ (c : CMP) (n : ℕ), ∃ r : STK, c - toC r ∈ (IsLocalRing.maximalIdeal CMP) ^ n := by
    intro c n
    obtain ⟨r, hr⟩ := Submodule.mkQ_surjective ((IsLocalRing.maximalIdeal STK) ^ n • (⊤ : Submodule STK STK))
      (AdicCompletion.eval (IsLocalRing.maximalIdeal STK) STK n c)
    refine ⟨r, ?_⟩
    have hker : c - toC r ∈ LinearMap.ker (AdicCompletion.eval (IsLocalRing.maximalIdeal STK) STK n) := by
      rw [LinearMap.mem_ker, map_sub]
      have : toC r = AdicCompletion.of (IsLocalRing.maximalIdeal STK) STK r := by
        show algebraMap STK CMP r = _
        rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [this, AdicCompletion.eval_of, ← hr, sub_self]
    rw [← AdicCompletion.pow_smul_top_eq_ker_eval hFG] at hker

    have hsub : ((IsLocalRing.maximalIdeal STK) ^ n • (⊤ : Submodule STK CMP)) =
        (((IsLocalRing.maximalIdeal STK) ^ n).map (algebraMap STK CMP)).restrictScalars STK :=
      Ideal.smul_top_eq_map _
    rw [hsub, Submodule.restrictScalars_mem, Ideal.map_pow] at hker
    have : (IsLocalRing.maximalIdeal STK).map (algebraMap STK CMP) = IsLocalRing.maximalIdeal CMP := hCMPmap
    rw [this] at hker
    exact hker
  have hdenseS : ∀ (s : S) (n : ℕ), ∃ a : R, s - Ψ a ∈ (IsLocalRing.maximalIdeal S) ^ n := by
    intro s n
    obtain ⟨r, hr⟩ := hdenseCMP (e.symm s) n
    obtain ⟨a, ha⟩ := hDENSE r n
    refine ⟨a, ?_⟩
    have h1 : toC (r - germY a) ∈ (IsLocalRing.maximalIdeal CMP) ^ n := by
      rw [← hCMPmap, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha
    have h2 : e.symm s - toC (germY a) ∈ (IsLocalRing.maximalIdeal CMP) ^ n := by
      have : e.symm s - toC (germY a) = (e.symm s - toC r) + toC (r - germY a) := by rw [map_sub]; ring
      rw [this]; exact add_mem hr h1
    have h3 := Ideal.mem_map_of_mem (e : CMP →+* S) h2
    rw [Ideal.map_pow, he𝔪, map_sub] at h3
    rw [hΨ]
    convert h3 using 2 <;> first | rfl | exact (e.apply_symm_apply s).symm

  have hqW : (q : W) ∈ IsLocalRing.maximalIdeal W := by
    have : (q : W) = σ (q : A) := by rw [map_natCast]
    rw [this]; exact hσ𝔪 _ hAq
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_isField A
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hϖ, h0, Ideal.span_singleton_eq_bot]
  have hσϖ0 : σ ϖ ≠ 0 := by
    intro h0
    have : IsLocalRing.maximalIdeal W = ⊥ := by rw [hσϖ, h0, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_isField W (IsLocalRing.isField_iff_maximalIdeal_eq.mpr this)
  obtain ⟨hBR1, -, -, -⟩ :=
    DrinfeldCurve.LocalChart.branchPrimes_of_sub_drinfeldForm_mem_pow q W (σ ϖ) hσϖ hqW (σ ϖ) hσϖ𝔪 hσϖ0
      f u v hu hv hf
  obtain ⟨P₀, hP₀prime, hP₀X, hP₀ϖ, h₀, hh₀, hP₀lin⟩ := hBR1 1 0 (by
    rintro ⟨h1, -⟩
    exact hp.one_lt.ne' (Int.natCast_dvd_natCast.mp (by simpa using h1) |> Nat.dvd_one.mp))
  have hP₀lin' : mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h₀) ∈ P₀ := by
    simpa only [Int.cast_one, Int.cast_zero] using hP₀lin
  have HA := hanchor P₀ hP₀prime hP₀X hP₀ϖ ⟨h₀, hh₀, hP₀lin'⟩
  have hGiff : ∀ a : R, Ψ a ∈ P₀ ↔
      ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((a : R) : ↥K) : LaurentSeries L).coeff n = algebraMap A L m := by
    intro a
    rw [hΨ, ← Ideal.mem_comap]
    exact HA a

  have hcoeR : ∀ a : A, (((algebraMap A R a : R) : ↥K) : LaurentSeries L) = HahnSeries.single 0 (algebraMap A L a) := by
    intro a
    rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L ↥K]
    show algebraMap L (LaurentSeries L) (algebraMap A L a) = _
    exact ModularCurve.algebraMap_laurentSeries_eq_single L (algebraMap A L a)
  have hϖG : Ψ (algebraMap A R ϖ) ∈ P₀ := by
    rw [hGiff]
    intro n
    rw [hcoeR, HahnSeries.coeff_single]
    by_cases hn : n = 0
    · exact ⟨ϖ, by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ, by rw [if_pos hn]⟩
    · exact ⟨0, zero_mem _, by rw [if_neg hn, map_zero]⟩
  have hϖL : algebraMap A L ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr hϖ0
  have hint : ∀ (a : R) (n : ℤ), ∃ m : A, (((a : R) : ↥K) : LaurentSeries L).coeff n = algebraMap A L m := by
    intro a n
    have hmem : Ψ (algebraMap A R ϖ * a) ∈ P₀ := by rw [map_mul]; exact Ideal.mul_mem_right _ _ hϖG
    obtain ⟨m, hm, hcoef⟩ := (hGiff _).mp hmem n
    have hmul : (((algebraMap A R ϖ * a : R) : ↥K) : LaurentSeries L).coeff n =
        algebraMap A L ϖ * (((a : R) : ↥K) : LaurentSeries L).coeff n := by
      rw [Subalgebra.coe_mul, IntermediateField.coe_mul, hcoeR, HahnSeries.coeff_single_zero_mul]
    rw [hmul] at hcoef
    rw [hϖ, Ideal.mem_span_singleton'] at hm
    obtain ⟨m', rfl⟩ := hm
    refine ⟨m', ?_⟩
    apply mul_left_cancel₀ hϖL
    rw [hcoef, map_mul, mul_comm]
  have hτcoe : ∀ a : R, (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : R) : ↥K) = τ a := fun a => rfl
  have hdiffG : ∀ a : R, Ψ ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a) - Ψ a ∈ P₀ := by
    intro a
    rw [← map_sub, hGiff]
    intro n
    obtain ⟨m, hm⟩ := hint a n
    refine ⟨σA m - m, hinert m, ?_⟩
    rw [Subalgebra.coe_sub, AddSubgroupClass.coe_sub, hτcoe, hτ, HahnSeries.coeff_sub, ModularCurve.coeffMap_coeff, hm,
      map_sub, hcompat]
    rfl
  have hθΨ : ∀ a : R, θ (Ψ a) - Ψ a ∈ P₀ := by
    intro a
    rw [hΨ, h1 a, ← hΨ, ← hΨ]
    exact hdiffG a

  haveI hP₀prime' : P₀.IsPrime := hP₀prime
  have hP₀le : P₀ ≤ IsLocalRing.maximalIdeal S := IsLocalRing.le_maximalIdeal hP₀prime.ne_top
  haveI : Nontrivial (S ⧸ P₀) := Ideal.Quotient.nontrivial_iff.mpr hP₀prime.ne_top
  haveI hQloc : IsLocalRing (S ⧸ P₀) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P₀) Ideal.Quotient.mk_surjective
  haveI : IsDomain (S ⧸ P₀) := Ideal.Quotient.isDomain P₀
  haveI : IsNoetherianRing (S ⧸ P₀) := inferInstance
  have hHaus := IsHausdorff.of_isDomain (R := S ⧸ P₀) (IsLocalRing.maximalIdeal (S ⧸ P₀)) (Ideal.IsPrime.ne_top inferInstance)
  haveI := hHaus
  have hθ𝔪 : ∀ s : S, s ∈ IsLocalRing.maximalIdeal S → θ s ∈ IsLocalRing.maximalIdeal S := by
    intro s hs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
    intro hu'
    apply hs
    have := hu'.map (θ.symm : S →+* S)
    simpa using this
  have hπ𝔪 : ∀ s : S, s ∈ IsLocalRing.maximalIdeal S → Ideal.Quotient.mk P₀ s ∈ IsLocalRing.maximalIdeal (S ⧸ P₀) := by
    intro s hs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu'
    obtain ⟨t', ht'⟩ := hu'.exists_right_inv
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t'
    rw [← map_mul, ← map_one (Ideal.Quotient.mk P₀), Ideal.Quotient.eq] at ht'
    have h1 : s * t - 1 ∈ IsLocalRing.maximalIdeal S := hP₀le ht'
    have h2 : s * t ∈ IsLocalRing.maximalIdeal S := Ideal.mul_mem_right _ _ hs
    have : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
      have := Ideal.sub_mem _ h2 h1; rwa [sub_sub_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this isUnit_one
  have hT0 : (Ideal.Quotient.mk P₀).comp θ.toRingHom = Ideal.Quotient.mk P₀ :=
    RingHom.eq_of_forall_exists_sub_mem_pow_of_comp_eq R S (S ⧸ P₀) Ψ (IsLocalRing.maximalIdeal S) hdenseS
      (IsLocalRing.maximalIdeal (S ⧸ P₀)) ((Ideal.Quotient.mk P₀).comp θ.toRingHom) (Ideal.Quotient.mk P₀)
      (fun s hs => hπ𝔪 _ (hθ𝔪 s hs)) (fun s hs => hπ𝔪 s hs)
      (by
        ext a
        simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [Ideal.Quotient.eq]
        exact hθΨ a)
  have hθP : ∀ s : S, θ s - s ∈ P₀ := by
    intro s
    have := RingHom.congr_fun hT0 s
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this
    exact (Ideal.Quotient.eq).mp this

  have hle : Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u} ≤
      RingHom.ker ((Ideal.Quotient.mk (Ideal.span {σ ϖ})).comp (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) W →+* W)) := by
    rw [Ideal.span_le]; rintro x hx; rcases hx with rfl
    simp [RingHom.mem_ker, hf0]
  have hXnu : ∀ jj : Fin 2, ¬ IsUnit (mkS (MvPowerSeries.X jj)) := by
    intro jj hunit
    have h := hunit.map (Ideal.Quotient.lift _ _ hle)
    rw [show mkS = Ideal.Quotient.mk _ from rfl, Ideal.Quotient.lift_mk] at h
    simp only [RingHom.coe_comp, Function.comp_apply, MvPowerSeries.constantCoeff_X, map_zero, isUnit_zero_iff] at h
    have : (1 : W ⧸ Ideal.span {σ ϖ}) = 0 := h.symm
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {σ ϖ})), Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp hσϖ𝔪 (isUnit_of_dvd_one this)
  have hX𝔪 : ∀ jj : Fin 2, mkS (MvPowerSeries.X jj) ∈ IsLocalRing.maximalIdeal S := fun jj =>
    (IsLocalRing.mem_maximalIdeal _).mpr (hXnu jj)
  obtain ⟨J, hJ⟩ : ∃ J : Ideal S, J = Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := ⟨_, rfl⟩
  have hJle : J ≤ IsLocalRing.maximalIdeal S := by
    rw [hJ, Ideal.span_le]; rintro x hx
    rcases hx with rfl | hx
    · exact hX𝔪 0
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact hX𝔪 1
  have hJfg : (J : Submodule S S).FG := by rw [hJ]; exact ⟨{mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}, by simp⟩
  have hJmap : J = (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map mkS := by
    rw [hJ, Ideal.map_span]; congr 1; ext x; simp [Set.image_insert_eq]
  have hX0J : mkS (MvPowerSeries.X 0) ∈ J := by rw [hJ]; exact Ideal.subset_span (by simp)
  have hX1J : mkS (MvPowerSeries.X 1) ∈ J := by rw [hJ]; exact Ideal.subset_span (by simp)
  have hh₀J : mkS h₀ ∈ J ^ 2 := by rw [hJmap, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hh₀
  have hq₀ : mkS (MvPowerSeries.X 0) + mkS h₀ ∈ P₀ := by
    have : MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h₀ =
        MvPowerSeries.X 0 + h₀ := by rw [map_one, map_zero, one_mul, zero_mul, add_zero]
    rw [← map_add, ← this]; exact hP₀lin'

  have hclaim : ∀ a b : W, mkS (MvPowerSeries.C a * MvPowerSeries.X 0 + MvPowerSeries.C b * MvPowerSeries.X 1) ∈ P₀ ⊔ J ^ 2 →
      b ∈ IsLocalRing.maximalIdeal W := by
    intro a b hab
    by_contra hb
    have hbU : IsUnit b := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hb

    have hX0 : mkS (MvPowerSeries.X 0) ∈ P₀ ⊔ J ^ 2 := by
      have : mkS (MvPowerSeries.X 0) = (mkS (MvPowerSeries.X 0) + mkS h₀) - mkS h₀ := by ring
      rw [this]; exact Ideal.sub_mem _ (Ideal.mem_sup_left hq₀) (Ideal.mem_sup_right hh₀J)

    have hX1 : mkS (MvPowerSeries.X 1) ∈ P₀ ⊔ J ^ 2 := by
      have hbX1 : mkS (MvPowerSeries.C b * MvPowerSeries.X 1) ∈ P₀ ⊔ J ^ 2 := by
        have : mkS (MvPowerSeries.C b * MvPowerSeries.X 1) =
            mkS (MvPowerSeries.C a * MvPowerSeries.X 0 + MvPowerSeries.C b * MvPowerSeries.X 1) -
              mkS (MvPowerSeries.C a) * mkS (MvPowerSeries.X 0) := by
          rw [map_add, map_mul, map_mul]; ring
        rw [this]; exact Ideal.sub_mem _ hab (Ideal.mul_mem_left _ _ hX0)
      obtain ⟨bi, hbi⟩ := hbU.exists_left_inv
      have : mkS (MvPowerSeries.X 1) = mkS (MvPowerSeries.C bi) * mkS (MvPowerSeries.C b * MvPowerSeries.X 1) := by
        rw [← map_mul, ← mul_assoc, ← map_mul, hbi, map_one, one_mul]
      rw [this]; exact Ideal.mul_mem_left _ _ hbX1
    have hJsub : (J : Submodule S S) ≤ P₀ ⊔ J • J := by
      have e2 : (J • J : Submodule S S) = J ^ 2 := by rw [pow_two]; rfl
      rw [e2, hJ, Ideal.span_le]
      rintro x hx
      rcases hx with rfl | hx
      · exact hJ ▸ hX0
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact hJ ▸ hX1
    have hNak : (J : Submodule S S) ≤ P₀ :=
      Submodule.le_of_le_smul_of_le_jacobson_bot hJfg
        (le_trans hJle (IsLocalRing.maximalIdeal_le_jacobson _)) hJsub
    rcases hP₀X with h | h
    · exact h (hNak hX0J)
    · exact h (hNak hX1J)

  have hrow : ∀ jj : Fin 2, mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) - mkS (MvPowerSeries.X jj) ∈ P₀ ⊔ J ^ 2 := by
    intro jj
    have e1 : mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) - mkS (MvPowerSeries.X jj) =
        (θ (mkS (MvPowerSeries.X jj)) - mkS (MvPowerSeries.X jj)) -
          (θ (mkS (MvPowerSeries.X jj)) - mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii)) := by ring
    rw [e1]
    refine Ideal.sub_mem _ (Ideal.mem_sup_left (hθP _)) (Ideal.mem_sup_right ?_)
    rw [hJ]; exact hM jj
  refine ⟨?_, ?_⟩
  ·
    apply hclaim (M 0 0 - 1) (M 1 0)
    have := hrow 0
    have e' : (∑ ii : Fin 2, MvPowerSeries.C (M ii 0) * MvPowerSeries.X ii) - MvPowerSeries.X 0 =
        MvPowerSeries.C (M 0 0 - 1) * MvPowerSeries.X 0 + MvPowerSeries.C (M 1 0) * MvPowerSeries.X 1 := by
      rw [Fin.sum_univ_two, map_sub, map_one]; ring
    have e : mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii 0) * MvPowerSeries.X ii) - mkS (MvPowerSeries.X 0) =
        mkS (MvPowerSeries.C (M 0 0 - 1) * MvPowerSeries.X 0 + MvPowerSeries.C (M 1 0) * MvPowerSeries.X 1) := by
      rw [← map_sub, e']
    rwa [e] at this
  · apply hclaim (M 0 1) (M 1 1 - 1)
    have := hrow 1
    have e' : (∑ ii : Fin 2, MvPowerSeries.C (M ii 1) * MvPowerSeries.X ii) - MvPowerSeries.X 1 =
        MvPowerSeries.C (M 0 1) * MvPowerSeries.X 0 + MvPowerSeries.C (M 1 1 - 1) * MvPowerSeries.X 1 := by
      rw [Fin.sum_univ_two, map_sub, map_one]; ring
    have e : mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii 1) * MvPowerSeries.X ii) - mkS (MvPowerSeries.X 1) =
        mkS (MvPowerSeries.C (M 0 1) * MvPowerSeries.X 0 + MvPowerSeries.C (M 1 1 - 1) * MvPowerSeries.X 1) := by
      rw [← map_sub, e']
    rwa [e] at this

end S_ModularCurve_FullLevel_AuxLevelOne_linearPart_row_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_anchor_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_linearPart_row_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_anchor_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd (solution)
