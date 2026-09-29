-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.linearPart_row_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_anchor_twoChartIntegralModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/fde14d8a-a2d0-561f-b808-e2adb48331e2

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_charZero
import Theorems.Thm_RingHom_eq_of_forall_exists_sub_mem_pow_of_comp_eq
import Theorems.Thm_DrinfeldCurve_LocalChart_branchPrimes_of_sub_drinfeldForm_mem_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_linearPart_row_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_anchor_twoChartIntegralModel
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

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
  intro STK CMP toC S mkS germY σL σA hcompat hinert τ hτ hpres θ hθe M hM
  subst hy

  let R : Type := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
  let Loc : Type := Localization.AtPrime y.asIdeal
  let Ψ : R →+* S := (e : CMP →+* S).comp (toC.comp germY)
  let cW : W →+* S := mkS.comp (MvPowerSeries.C)
  have hΨ : ∀ a : R, Ψ a = e (toC (germY a)) := fun a => rfl
  have hcW : ∀ w : W, cW w = mkS (MvPowerSeries.C w) := fun w => rfl

  obtain ⟨est, hest_base, hest_chart⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin A (↥K) j y ⟨y, trivial, rfl⟩
  let eST : STK ≃+* Loc := est.commRingCatIsoToRingEquiv
  have heST : ∀ a : R, eST (germY a) = algebraMap R Loc a := fun a => hest_chart a
  have heST_base : ∀ r : A, eST ((((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤
      ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) trivial).hom
        (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r)))) = algebraMap A Loc r := fun r => hest_base r

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

  have hfrac : ∀ r : STK, ∃ c : R, ∃ s : R, s ∉ y.asIdeal ∧ e (toC r) * Ψ s = Ψ c := by
    intro r
    obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl (eST r)
    refine ⟨c, s, s.2, ?_⟩
    have hrs : r * germY (s : R) = germY c := by
      apply eST.injective
      rw [map_mul, heST, heST, ← hcs]
      exact IsLocalization.mk'_spec Loc c s
    rw [hΨ, hΨ, ← map_mul, ← map_mul, hrs]
  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L

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

  have hmFG : (IsLocalRing.maximalIdeal STK).FG := IsNoetherian.noetherian _
  have hmap_le : Ideal.map ((e : CMP →+* S).comp toC) (IsLocalRing.maximalIdeal STK) ≤ IsLocalRing.maximalIdeal S := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro m hm
    exact Ideal.mem_comap.mpr (he_mem _ (htoC_nu m hm))
  have hdense : ∀ (x : S) (n : ℕ), ∃ r : STK, x - ((e : CMP →+* S).comp toC) r ∈ IsLocalRing.maximalIdeal S ^ n := by
    intro x n
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (IsLocalRing.maximalIdeal STK) STK n (e.symm x))
    refine ⟨r, ?_⟩
    have hker : e.symm x - toC r ∈ LinearMap.ker (AdicCompletion.eval (IsLocalRing.maximalIdeal STK) STK n) := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero, ← hr]
      show _ = AdicCompletion.eval _ STK n (algebraMap STK CMP r)
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, AdicCompletion.eval_of]
      rfl
    rw [← AdicCompletion.pow_smul_top_eq_ker_eval hmFG, Ideal.smul_top_eq_map] at hker
    have h2 : (e : CMP →+* S) (e.symm x - toC r) ∈ Ideal.map (e : CMP →+* S) (Ideal.map toC (IsLocalRing.maximalIdeal STK ^ n)) :=
      Ideal.mem_map_of_mem _ hker
    rw [map_sub, Ideal.map_map] at h2
    have h3 : (e : CMP →+* S) (e.symm x) = x := e.apply_symm_apply x
    rw [h3] at h2
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono hmap_le n h2
  haveI hShaus : IsHausdorff (IsLocalRing.maximalIdeal S) S := inferInstance

  let J : Ideal (MvPowerSeries (Fin 2) W) :=
    Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}
  have hJdef : J = Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} := rfl
  have hX0J : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ∈ J := Ideal.subset_span (by simp)
  have hX1J : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ∈ J := Ideal.subset_span (by simp)

  have hJ2 : ∀ p : MvPowerSeries (Fin 2) W, p ∈ J ^ 2 → ∃ t₀₀ t₀₁ t₁₁ : MvPowerSeries (Fin 2) W,
      p = MvPowerSeries.X 0 * MvPowerSeries.X 0 * t₀₀ + MvPowerSeries.X 0 * MvPowerSeries.X 1 * t₀₁ +
        MvPowerSeries.X 1 * MvPowerSeries.X 1 * t₁₁ := by
    intro p hp
    rw [pow_two, hJdef, Ideal.span_mul_span'] at hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact ⟨1, 0, 0, by ring⟩
        · exact ⟨0, 1, 0, by ring⟩
        · exact ⟨0, 1, 0, by ring⟩
        · exact ⟨0, 0, 1, by ring⟩
    | zero => exact ⟨0, 0, 0, by ring⟩
    | add x y _ _ hx hy =>
        obtain ⟨a, b, c₂, rfl⟩ := hx
        obtain ⟨a', b', c', rfl⟩ := hy
        exact ⟨a + a', b + b', c₂ + c', by ring⟩
    | smul r x _ hx =>
        obtain ⟨a, b, c₂, rfl⟩ := hx
        exact ⟨r * a, r * b, r * c₂, by simp only [smul_eq_mul]; ring⟩
  have hJ2coeff : ∀ p : MvPowerSeries (Fin 2) W, p ∈ J ^ 2 →
      MvPowerSeries.coeff (Finsupp.single 0 1) p = 0 ∧ MvPowerSeries.coeff (Finsupp.single 1 1) p = 0 := by
    intro p hp
    obtain ⟨t₀₀, t₀₁, t₁₁, rfl⟩ := hJ2 p hp
    have hA : ∀ (i : Fin 2) (t : MvPowerSeries (Fin 2) W) (m : Fin 2 →₀ ℕ), m i < 2 →
        MvPowerSeries.coeff m (MvPowerSeries.X i * MvPowerSeries.X i * t) = 0 := by
      intro i t m hm
      have hd : (MvPowerSeries.X i : MvPowerSeries (Fin 2) W) ^ 2 ∣ MvPowerSeries.X i * MvPowerSeries.X i * t :=
        ⟨t, by ring⟩
      exact (MvPowerSeries.X_pow_dvd_iff.mp hd) m hm
    have hB : ∀ (i : Fin 2) (t : MvPowerSeries (Fin 2) W) (m : Fin 2 →₀ ℕ), m i = 0 →
        MvPowerSeries.coeff m (MvPowerSeries.X 0 * MvPowerSeries.X 1 * t) = 0 := by
      intro i t m hm
      have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      have hd : (MvPowerSeries.X i : MvPowerSeries (Fin 2) W) ∣ MvPowerSeries.X 0 * MvPowerSeries.X 1 * t := by
        rcases hi with rfl | rfl
        · exact ⟨MvPowerSeries.X 1 * t, by ring⟩
        · exact ⟨MvPowerSeries.X 0 * t, by ring⟩
      exact (MvPowerSeries.X_dvd_iff.mp hd) m hm
    have hA' : ∀ (i k : Fin 2) (t : MvPowerSeries (Fin 2) W), i ≠ k →
        MvPowerSeries.coeff (Finsupp.single k 1) (MvPowerSeries.X i * MvPowerSeries.X i * t) = 0 := by
      intro i k t hik
      have hd : (MvPowerSeries.X i : MvPowerSeries (Fin 2) W) ∣ MvPowerSeries.X i * MvPowerSeries.X i * t :=
        ⟨MvPowerSeries.X i * t, by ring⟩
      exact (MvPowerSeries.X_dvd_iff.mp hd) _ (by rw [Finsupp.single_apply, if_neg (Ne.symm hik)])
    refine ⟨?_, ?_⟩
    · rw [map_add, map_add, hA 0 t₀₀ _ (by rw [Finsupp.single_eq_same]; omega),
        hB 1 t₀₁ _ (by rw [Finsupp.single_apply, if_neg (by decide)]), hA' 1 0 t₁₁ (by decide)]
      ring
    · rw [map_add, map_add, hA' 0 1 t₀₀ (by decide),
        hB 0 t₀₁ _ (by rw [Finsupp.single_apply, if_neg (by decide)]), hA 1 t₁₁ _ (by rw [Finsupp.single_eq_same]; omega)]
      ring

  have hfJ2 : f ∈ J ^ 2 := by
    have h1 : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈ J ^ 2 := Ideal.pow_le_pow_right (by omega) hf
    have hX01 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 ∈ J ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hX0J hX1J
    have h2 : DrinfeldCurve.LocalChart.drinfeldForm q W ∈ J ^ 2 := by
      have hq1 : q = (q - 1) + 1 := (Nat.sub_add_cancel (Fact.out : q.Prime).one_lt.le).symm
      have : DrinfeldCurve.LocalChart.drinfeldForm q W =
          MvPowerSeries.X 0 * MvPowerSeries.X 1 * (MvPowerSeries.X 1 ^ (q - 1)) -
          MvPowerSeries.X 0 * MvPowerSeries.X 1 * (MvPowerSeries.X 0 ^ (q - 1)) := by
        unfold DrinfeldCurve.LocalChart.drinfeldForm
        conv_lhs => rw [hq1]
        ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hX01) (Ideal.mul_mem_right _ _ hX01)
    have := Ideal.add_mem _ h1 h2
    rwa [sub_add_cancel] at this

  have h𝔑 : Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} = J.map mkS := by
    rw [hJdef, Ideal.map_span]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨_, Or.inl rfl, rfl⟩
      · exact ⟨_, Or.inr rfl, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

  have h𝔑le : Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ≤ IsLocalRing.maximalIdeal S := by
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rcases hx with rfl | rfl <;>
    · intro hu'
      have := hlift_unit _ hu'
      rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at this
      exact not_isUnit_zero this
  have h𝔑ge : IsLocalRing.maximalIdeal S ≤ Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := by
    intro s hs
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hpnu : ¬ IsUnit p := fun hu' => (IsLocalRing.mem_maximalIdeal _).mp hs (hu'.map mkS)
    rw [MvPowerSeries.isUnit_iff_constantCoeff] at hpnu
    have hc0 : MvPowerSeries.constantCoeff p ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hpnu
    rw [hσϖ, Ideal.mem_span_singleton'] at hc0
    obtain ⟨a, ha⟩ := hc0

    have hpJ : p - MvPowerSeries.C (MvPowerSeries.constantCoeff p) ∈ J := by

      have hz : MvPowerSeries.constantCoeff (p - MvPowerSeries.C (MvPowerSeries.constantCoeff p)) = 0 := by
        rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self]

      set g₀ := p - MvPowerSeries.C (MvPowerSeries.constantCoeff p) with hg₀
      let g1 : MvPowerSeries (Fin 2) W := fun m => if m 1 = 0 then 0 else MvPowerSeries.coeff m g₀
      have h1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ∣ g1 := by
        rw [MvPowerSeries.X_dvd_iff]
        intro m hm
        show (if m 1 = 0 then 0 else MvPowerSeries.coeff m g₀) = 0
        rw [if_pos hm]
      have h0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ∣ (g₀ - g1) := by
        rw [MvPowerSeries.X_dvd_iff]
        intro m hm
        rw [map_sub]
        show MvPowerSeries.coeff m g₀ - (if m 1 = 0 then 0 else MvPowerSeries.coeff m g₀) = 0
        by_cases hm1 : m 1 = 0
        · rw [if_pos hm1, sub_zero]
          have : m = 0 := by
            ext i; fin_cases i
            · exact hm
            · exact hm1
          rw [this]; exact hz
        · rw [if_neg hm1, sub_self]
      obtain ⟨c0, hc0'⟩ := h0
      obtain ⟨c1, hc1⟩ := h1
      rw [hJdef, Ideal.mem_span_pair]
      refine ⟨c0, c1, ?_⟩
      rw [mul_comm c0, mul_comm c1, ← hc0', ← hc1]; ring

    have hσϖ𝔑 : mkS (MvPowerSeries.C (σ ϖ)) ∈ Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := by
      have hrel : mkS (MvPowerSeries.C (σ ϖ) * v) = mkS (f * u) := by
        rw [show mkS = Ideal.Quotient.mk _ from rfl, Ideal.Quotient.eq]
        exact Ideal.subset_span rfl
      have hvu : IsUnit (mkS v) := hv.map mkS
      have : mkS (MvPowerSeries.C (σ ϖ)) = mkS (f * u) * ↑(hvu.unit⁻¹) := by
        rw [← hrel, map_mul, mul_assoc, IsUnit.mul_val_inv, mul_one]
      rw [this, h𝔑]
      apply Ideal.mul_mem_right
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.pow_le_self two_ne_zero hfJ2))
    have hsplit : p = MvPowerSeries.C (σ ϖ) * MvPowerSeries.C a + (p - MvPowerSeries.C (MvPowerSeries.constantCoeff p)) := by
      rw [← map_mul, ← ha]; ring
    rw [hsplit, map_add, map_mul]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hσϖ𝔑) ?_
    rw [h𝔑]; exact Ideal.mem_map_of_mem _ hpJ
  have h𝔑eq : Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} = IsLocalRing.maximalIdeal S :=
    le_antisymm h𝔑le h𝔑ge

  let τC : R →+* R := τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres
  have hτC : ∀ a : R, ((τC a : R) : ↥K) = τ (a : ↥K) := fun a => rfl
  have hθΨ : ∀ a : R, θ (Ψ a) = Ψ (τC a) := fun a => hθe a
  have hθ𝔪 : ∀ s : S, s ∈ IsLocalRing.maximalIdeal S → θ s ∈ IsLocalRing.maximalIdeal S := by
    intro s hs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
    intro hu'
    apply hs
    have := hu'.map (θ.symm : S →+* S)
    simpa using this
  have hqW : (q : W) ∈ IsLocalRing.maximalIdeal W := by
    have : (q : W) = σ (q : A) := by simp
    rw [this]; exact hσ𝔪 _ hAq
  have hσϖ0 : σ ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_isField W
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hσϖ, h0, Ideal.span_singleton_eq_bot]
  have hϖ0 : ϖ ≠ 0 := fun h0 => hσϖ0 (by rw [h0, map_zero])
  have hϖ𝔪A : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.subset_span rfl
  obtain ⟨hBR1, -, -, -⟩ := DrinfeldCurve.LocalChart.branchPrimes_of_sub_drinfeldForm_mem_pow q W (σ ϖ) hσϖ hqW
    (σ ϖ) hσϖ𝔪 hσϖ0 f u v hu hv hf
  have h10 : ¬ ((q : ℤ) ∣ 1 ∧ (q : ℤ) ∣ 0) := by
    rintro ⟨h1, -⟩
    have : (q : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have : 2 ≤ (q : ℤ) := by exact_mod_cast (Fact.out : q.Prime).two_le
    omega
  obtain ⟨P₀, hP₀prime, hP₀X, hP₀ϖ, h₀, hh₀J, hh₀P⟩ := hBR1 1 0 h10
  have hh₀P' : mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h₀) ∈ P₀ := by
    simpa only [Int.cast_one, Int.cast_zero] using hh₀P
  have hG : ∀ a : R, Ψ a ∈ P₀ ↔ ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
      (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m := by
    intro a
    have := hanchor P₀ hP₀prime hP₀X hP₀ϖ ⟨h₀, hh₀J, hh₀P'⟩ a
    rw [hΨ]
    exact this

  have hϖL0 : algebraMap A L ϖ ≠ 0 := fun h0 => hϖ0 (hinjAL (by rw [h0, map_zero]))
  have hcoeK : ∀ l : L, ((algebraMap L ↥K l : ↥K) : LaurentSeries L) = HahnSeries.single 0 l := by
    intro l
    rw [← ModularCurve.algebraMap_laurentSeries_eq_single]
    rfl
  have hcoeAR : ∀ a : A, (((algebraMap A R a : R) : ↥K) : LaurentSeries L) = HahnSeries.single 0 (algebraMap A L a) := by
    intro a
    rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L ↥K, hcoeK]
  have hϖG : Ψ (algebraMap A R ϖ) ∈ P₀ := by
    rw [hG]
    intro n
    rw [hcoeAR, HahnSeries.coeff_single]
    by_cases hn : n = 0
    · rw [if_pos hn]; exact ⟨ϖ, hϖ𝔪A, rfl⟩
    · rw [if_neg hn]; exact ⟨0, Ideal.zero_mem _, by rw [map_zero]⟩
  have hint : ∀ (a : R) (n : ℤ), ∃ b : A, (((a : ↥K)) : LaurentSeries L).coeff n = algebraMap A L b := by
    intro a n
    have hmem : Ψ (algebraMap A R ϖ * a) ∈ P₀ := by rw [map_mul]; exact Ideal.mul_mem_right _ _ hϖG
    obtain ⟨m, hm, hmeq⟩ := (hG _).mp hmem n
    have hco : ((((algebraMap A R ϖ * a : R)) : ↥K) : LaurentSeries L).coeff n =
        algebraMap A L ϖ * (((a : ↥K)) : LaurentSeries L).coeff n := by
      rw [Subalgebra.coe_mul, IntermediateField.coe_mul, hcoeAR, HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul,
        smul_eq_mul]
    rw [hϖ, Ideal.mem_span_singleton'] at hm
    obtain ⟨b, rfl⟩ := hm
    refine ⟨b, ?_⟩
    rw [hco, map_mul] at hmeq

    have : algebraMap A L ϖ * (((a : ↥K)) : LaurentSeries L).coeff n = algebraMap A L ϖ * algebraMap A L b := by
      rw [hmeq, mul_comm]
    exact mul_left_cancel₀ hϖL0 this
  have hτG : ∀ a : R, Ψ (τC a - a) ∈ P₀ := by
    intro a
    rw [hG]
    intro n
    obtain ⟨b, hb⟩ := hint a n
    refine ⟨σA b - b, hinert b, ?_⟩
    have e1 : (((τC a - a : R) : ↥K) : LaurentSeries L) =
        ((τ (a : ↥K) : ↥K) : LaurentSeries L) - ((a : ↥K) : LaurentSeries L) := by
      rw [Subalgebra.coe_sub, hτC]
      rfl
    rw [e1, HahnSeries.coeff_sub, hτ, ModularCurve.coeffMap_coeff, hb, map_sub, hcompat]
    rfl

  have hP𝔪 : P₀ ≤ IsLocalRing.maximalIdeal S := IsLocalRing.le_maximalIdeal hP₀prime.ne_top
  let π₀ : S →+* S ⧸ P₀ := Ideal.Quotient.mk P₀
  have hπ₀ : ∀ a b : S, π₀ a = π₀ b ↔ a - b ∈ P₀ := fun a b => Ideal.Quotient.mk_eq_mk_iff_sub_mem a b
  have hRP : ∀ a : R, π₀ (θ (Ψ a)) = π₀ (Ψ a) := by
    intro a
    rw [hπ₀, hθΨ, ← map_sub]
    exact hτG a
  have hSTKP : ∀ r : STK, π₀ (θ (e (toC r))) = π₀ (e (toC r)) := by
    intro r
    obtain ⟨c₀, s, hs, hrs⟩ := hfrac r
    have hu : IsUnit (π₀ (Ψ s)) := (hΨ_unit _ hs).map π₀
    apply hu.mul_right_cancel
    calc π₀ (θ (e (toC r))) * π₀ (Ψ s) = π₀ (θ (e (toC r))) * π₀ (θ (Ψ s)) := by rw [hRP]
      _ = π₀ (θ (Ψ c₀)) := by rw [← map_mul, ← map_mul, hrs]
      _ = π₀ (Ψ c₀) := hRP c₀
      _ = π₀ (e (toC r)) * π₀ (Ψ s) := by rw [← hrs, map_mul]
  haveI hQnt : Nontrivial (S ⧸ P₀) := Ideal.Quotient.nontrivial_iff.mpr hP₀prime.ne_top
  haveI hQloc : IsLocalRing (S ⧸ P₀) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P₀) Ideal.Quotient.mk_surjective
  have hπ₀𝔪 : ∀ s : S, s ∈ IsLocalRing.maximalIdeal S → π₀ s ∈ IsLocalRing.maximalIdeal (S ⧸ P₀) := by
    intro s hs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
    intro hu'
    apply hs
    obtain ⟨t, ht⟩ := hu'.exists_right_inv
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    have ht' : π₀ (s * t') = π₀ 1 := by rw [map_mul, map_one]; exact ht
    rw [hπ₀] at ht'
    have hm : s * t' - 1 ∈ IsLocalRing.maximalIdeal S := hP𝔪 ht'
    have hst : IsUnit (s * t') := by
      by_contra hnu
      have h1 : s * t' ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
        have := Ideal.sub_mem _ h1 hm; rwa [sub_sub_cancel] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp this isUnit_one
    exact isUnit_of_mul_isUnit_left hst
  have hGH : π₀.comp (θ : S →+* S) = π₀ :=
    RingHom.eq_of_forall_exists_sub_mem_pow_of_comp_eq STK S (S ⧸ P₀) ((e : CMP →+* S).comp toC)
      (IsLocalRing.maximalIdeal S) hdense (IsLocalRing.maximalIdeal (S ⧸ P₀)) (π₀.comp (θ : S →+* S)) π₀
      (fun s hs => hπ₀𝔪 _ (hθ𝔪 s hs)) (fun s hs => hπ₀𝔪 _ hs) (RingHom.ext fun r => hSTKP r)
  have hθP : ∀ s : S, θ s - s ∈ P₀ := by
    intro s
    rw [← hπ₀]
    exact congrArg (fun F : S →+* S ⧸ P₀ => F s) hGH

  have hsum2 : ∀ (N : Matrix (Fin 2) (Fin 2) W) (jj : Fin 2),
      mkS (∑ ii : Fin 2, MvPowerSeries.C (N ii jj) * MvPowerSeries.X ii) =
        cW (N 0 jj) * mkS (MvPowerSeries.X 0) + cW (N 1 jj) * mkS (MvPowerSeries.X 1) := by
    intro N jj
    rw [Fin.sum_univ_two, map_add, map_mul, map_mul, hcW, hcW]
  let Q : Ideal S := P₀ ⊔ (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2
  have hQdef : Q = P₀ ⊔ (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2 := rfl
  have hX0Q : mkS (MvPowerSeries.X 0) ∈ Q := by
    have h1 : mkS h₀ ∈ (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2 := by
      rw [h𝔑, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hh₀J
    have h2 : mkS (MvPowerSeries.X 0) =
        mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h₀) - mkS h₀ := by
      simp only [map_add, map_mul, map_one, map_zero, one_mul, zero_mul, add_zero, add_sub_cancel_right]
    rw [h2]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hh₀P') (Ideal.mem_sup_right h1)
  have hkey : ∀ c : W, cW c * mkS (MvPowerSeries.X 1) ∈ Q → c ∈ IsLocalRing.maximalIdeal W := by
    intro c hc
    by_contra hcu
    have hcu' : IsUnit c := by
      by_contra h; exact hcu ((IsLocalRing.mem_maximalIdeal _).mpr h)
    have hX1Q : mkS (MvPowerSeries.X 1) ∈ Q := by
      have := Ideal.mul_mem_left _ (cW ↑(hcu'.unit⁻¹)) hc
      rwa [← mul_assoc, ← map_mul, IsUnit.val_inv_mul, map_one, one_mul] at this
    have h𝔑Q : Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ≤ Q := by
      apply Ideal.span_le.mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hX0Q
      · exact hX1Q
    rw [hQdef, h𝔑eq] at h𝔑Q
    have hle : IsLocalRing.maximalIdeal S ≤ P₀ := by
      apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _)
      rwa [Ideal.smul_eq_mul, ← pow_two]
    have hX0𝔪 : mkS (MvPowerSeries.X 0) ∈ IsLocalRing.maximalIdeal S := h𝔑le (Ideal.subset_span (by simp))
    have hX1𝔪 : mkS (MvPowerSeries.X 1) ∈ IsLocalRing.maximalIdeal S := h𝔑le (Ideal.subset_span (by simp))
    rcases hP₀X with h | h
    · exact h (hle hX0𝔪)
    · exact h (hle hX1𝔪)
  have hlinQ : ∀ jj : Fin 2,
      (cW (M 0 jj) * mkS (MvPowerSeries.X 0) + cW (M 1 jj) * mkS (MvPowerSeries.X 1)) - mkS (MvPowerSeries.X jj) ∈ Q := by
    intro jj
    have h1 : θ (mkS (MvPowerSeries.X jj)) - mkS (MvPowerSeries.X jj) ∈ P₀ := hθP _
    have h2 : θ (mkS (MvPowerSeries.X jj)) - (cW (M 0 jj) * mkS (MvPowerSeries.X 0) + cW (M 1 jj) * mkS (MvPowerSeries.X 1)) ∈
        (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2 := by
      rw [← hsum2]; exact hM jj
    have : (cW (M 0 jj) * mkS (MvPowerSeries.X 0) + cW (M 1 jj) * mkS (MvPowerSeries.X 1)) - mkS (MvPowerSeries.X jj) =
        (θ (mkS (MvPowerSeries.X jj)) - mkS (MvPowerSeries.X jj)) -
        (θ (mkS (MvPowerSeries.X jj)) - (cW (M 0 jj) * mkS (MvPowerSeries.X 0) + cW (M 1 jj) * mkS (MvPowerSeries.X 1))) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
  constructor
  · apply hkey
    have h := hlinQ 0
    have : cW (M 1 0) * mkS (MvPowerSeries.X 1) =
        ((cW (M 0 0) * mkS (MvPowerSeries.X 0) + cW (M 1 0) * mkS (MvPowerSeries.X 1)) - mkS (MvPowerSeries.X 0)) -
          cW (M 0 0) * mkS (MvPowerSeries.X 0) + mkS (MvPowerSeries.X 0) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.sub_mem _ h (Ideal.mul_mem_left _ _ hX0Q)) hX0Q
  · apply hkey
    have h := hlinQ 1
    have : cW (M 1 1 - 1) * mkS (MvPowerSeries.X 1) =
        ((cW (M 0 1) * mkS (MvPowerSeries.X 0) + cW (M 1 1) * mkS (MvPowerSeries.X 1)) - mkS (MvPowerSeries.X 1)) -
          cW (M 0 1) * mkS (MvPowerSeries.X 0) := by rw [map_sub, map_one]; ring
    rw [this]
    exact Ideal.sub_mem _ h (Ideal.mul_mem_left _ _ hX0Q)

end S_ModularCurve_FullLevel_AuxLevel_linearPart_row_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_anchor_twoChartIntegralModel
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_linearPart_row_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_anchor_twoChartIntegralModel (solution)
