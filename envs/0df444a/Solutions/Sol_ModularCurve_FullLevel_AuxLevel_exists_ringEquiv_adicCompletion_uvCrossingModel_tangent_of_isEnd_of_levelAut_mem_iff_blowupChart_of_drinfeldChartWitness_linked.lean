-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_ringEquiv_adicCompletion_uvCrossingModel_tangent_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/4300db7d-33d8-585f-a489-d9e28eb9f40c

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_ringHom_ringEquiv_adicCompletion_uvCrossingModel_tangent_coords_of_end_blowupChart_of_drinfeldChartWitness_linked
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_algEquiv_uvCrossingModel_compat_levelAut_pow_eq_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isUnit_iterate_apply_V_mul_sub_const_mem_sq_of_ringEquiv_compat_levelAut_of_isEnd_blowupChart_of_drinfeldChartWitness_linked
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_ringEquiv_adicCompletion_uvCrossingModel_tangent_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

open ModularCurve ModularCurve.FullLevel in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (hArig : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω),
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
        (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
        (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
        (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
        (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u}),

        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W) (M : Matrix (Fin 2) (Fin 2) W),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})

    (hW₁ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)

    (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hR1 :

      chartAlgFin A (↥K) j ≤ B ∧
      (∀ f : ↥K, ∃ g h : ↥B, (h : ↥K) ≠ 0 ∧ f * (h : ↥K) = (g : ↥K)))
    (hR2 :

      Algebra.FormallySmooth A ↥B ∧ Algebra.FinitePresentation A ↥B ∧
      Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}))
    (hR3 :

      (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
      maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
      IsDiscreteValuationRing ↥W ∧
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
        ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)))
    (hEQ :

      (∀ (inst : Algebra (GaloisField q 2) (ResidueField A)),
        ∃ (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),
          Function.Surjective ρ ∧
          (∀ b : ↥B, ρ b = 0 ↔ (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ a : A, ρ (algebraMap A ↥B a) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a)) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
                (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          ∀ f : ↥K, f ∈ B → τ f ∈ B) ∧
      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧
      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
              b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W))

    (n : ℕ) (hn1 : 1 ≤ n) (hnq : n ∣ q + 1)
    (γ₀ : SL(2, ℤ)) (hγ₀q : γ₀ ∈ CongruenceSubgroup.Gamma q) (hγ₀M : γ₀ ∈ CongruenceSubgroup.Gamma0 M')
    (τ₀ : ↥K ≃ₐ[L] ↥K) (hτ₀ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ₀⁻¹ K τ₀)
    (hτ₀W : ∀ f : ↥K, f ∈ W ↔ τ₀ f ∈ W)
    (hcyc1 : ∀ f : ↥K, f ∈ B → (τ₀ ^ n) f = f)
    (hcyc2 : ∀ k : ℕ, 0 < k → k < n → ∃ f : ↥K, f ∈ B ∧ (τ₀ ^ k) f ≠ f)

    (m : ℕ) (hm1 : 1 ≤ m) (hmt : ∃ w : A, IsUnit w ∧ ϖ ^ m = ϖt * w)
    (O : Subring ↥K)
    (hO : (∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
            let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
              {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
            ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
              (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
              (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
                ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
              ¬ (∀ f : ↥K, f ∈ B → f ∈ O)))
    (hOτ : ∀ f : ↥K, f ∈ O ↔ τ₀ f ∈ O) :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        (∃ (ζ₀ : (AdicCompletion (maximalIdeal A) A)) (_ : ζ₀ ^ n = 1) (_ : ∀ k : ℕ, 0 < k → k < n → IsUnit (ζ₀ ^ k - 1)),

          (∀ f : ↥K, f ∈ O → f ∈ W) ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
          (∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ O) ∧
          (∀ x : L, algebraMap L ↥K x ∈ O ↔ ∃ a : A, algebraMap A L a = x) ∧
          (∀ (f : ↥K) (hf : f ∈ O), ∃ (a : A) (ha : algebraMap A ↥K a ∈ O), ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, ha⟩)) ∧

          (∃ (hϖO : algebraMap A ↥K ϖ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ) (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)))
             (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))ˣ) (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃ₐ[(AdicCompletion (maximalIdeal A) A)] (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) (ζ₀' : (AdicCompletion (maximalIdeal A) A)) (_ : ζ₀ * ζ₀' = 1)
             (_ : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))),
            cx * cy = (⟨_, hϖO⟩ : ↥O) ^ m * (u : ↥O) ∧
            (∀ (a : A) (ha : algebraMap A ↥K a ∈ O), ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩) = UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a)) ∧
            ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) * UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ∧
            ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) * UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ∧
            (∀ hcy : (cy : ↥K) ∈ W, (⟨(cy : ↥K), hcy⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
            (∀ hcx : (cx : ↥K) ∈ W, (⟨(cx : ↥K), hcx⟩ : ↥W) ∉ maximalIdeal ↥W) ∧
            (∀ (f : ↥K) (hf : f ∈ O) (hf' : τ₀ f ∈ O),
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hf'⟩) = θ₀ (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨f, hf⟩))) ∧
            θ₀ (UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ζ₀ * UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ∈
              (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) ^ 2 ∧
            θ₀ (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ζ₀' * UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ∈
              (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) ^ 2 ∧

            (∀ (c : W₁) (θ : S ≃+* S) (Mx : Matrix (Fin 2) (Fin 2) W₁)
                (hpres : ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                  τ₀ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ₀ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                  (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) →
              (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) →
              (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                  mkS (∑ ii : Fin 2, MvPowerSeries.C (Mx ii jj) * MvPowerSeries.X ii) ∈
                (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) →
              (∀ ii jj : Fin 2, Mx ii jj - c * ((γ₀ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) →
              ∀ a : A, c - σ₁ a ∈ IsLocalRing.maximalIdeal W₁ →
                ¬ IsUnit (ζ₀' - algebraMap A (AdicCompletion (maximalIdeal A) A) a)))) := by
  classical

  have hW₁c := hW₁
  obtain ⟨-, -, -, -, -, -, hHC⟩ := hW₁c
  obtain ⟨hjK, hjC, -⟩ := hHC

  have hL := ModularCurve.FullLevel.AuxLevel.exists_ringHom_ringEquiv_adicCompletion_uvCrossingModel_tangent_coords_of_end_blowupChart_of_drinfeldChartWitness_linked q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss hArig z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB W hBW hR1 hR2 hR3 hEQ hjK hjC m hm1 hmt O hO
  obtain ⟨hOW, iL, iN, hCO, hconstO, hresO, Λ, hΛC, hΛcont, ι, hιc, ⟨ρ, p₀, p₁, α, β, hρσ, hρloc, hpdir, hprat, hαp, hβp, hιX0, hιX1, hιCw⟩,
    hϖO, cx, cy, u, γU, γV, hcxy, hιx, hιy, hcyW, hcxW⟩ := hL
  haveI := iL
  haveI := iN

  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  obtain ⟨instDom, instDVR, instCpl, hirrhat, -, -⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete A ϖ hirr
  have hπu : ¬ IsUnit ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) := fun hu =>
    hirrhat.not_isUnit (isUnit_pow_iff (by omega) |>.mp hu)
  haveI iLM : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) := ModularCurve.UVCrossingModel.isLocalRing_of_not_isUnit hπu

  obtain ⟨θ₀, hA1, hA2, hA3⟩ := ModularCurve.FullLevel.AuxLevel.exists_algEquiv_uvCrossingModel_compat_levelAut_pow_eq_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss hArig z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB W hBW hR1 hR2 hR3 hEQ n hn1 hnq γ₀ hγ₀q hγ₀M τ₀ hτ₀ hτ₀W hcyc1 hcyc2 m hm1 hmt O hO hOτ
    hOW iL iN hCO ι hιc hϖO cx cy γU γV hιx hιy hcyW hcxW
  have hA1' : ∀ (f : ↥K) (hf : f ∈ O) (hf' : τ₀ f ∈ O),
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hf'⟩) = (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨f, hf⟩)) :=
    fun f hf hf' => hA1 f hf hf'

  have hRD := ModularCurve.FullLevel.AuxLevel.exists_isUnit_iterate_apply_V_mul_sub_const_mem_sq_of_ringEquiv_compat_levelAut_of_isEnd_blowupChart_of_drinfeldChartWitness_linked
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss hArig z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB W hBW hR1 hR2 hR3 hEQ n hn1 hnq γ₀ hγ₀q hγ₀M τ₀ hτ₀ hτ₀W hcyc1 hcyc2 m hm1 hmt O hO hOτ
  obtain ⟨b, hb, c, hRD1, hRDu, hRD2⟩ := hRD iLM iL iN hCO Λ hΛC hΛcont ι hιc ρ p₀ p₁ α β hρσ hρloc hpdir hαp hβp hιX0 hιX1 hιCw
    (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) hA1'

  have hnA : IsUnit ((n : ℕ) : A) := by
    have hq1 : IsUnit ((q : A) + 1) := by
      have hneg : -(q : A) ∈ nonunits A := by
        rw [← IsLocalRing.mem_maximalIdeal]; exact (maximalIdeal A).neg_mem hAq
      have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(q : A)) hneg
      rwa [sub_neg_eq_add, add_comm] at this
    obtain ⟨d, hd⟩ := hnq
    refine isUnit_of_dvd_unit ⟨(d : A), ?_⟩ hq1
    have hd' : ((q + 1 : ℕ) : A) = ((n * d : ℕ) : A) := by rw [hd]
    push_cast at hd'
    exact hd'
  have hnAh : IsUnit ((n : ℕ) : (AdicCompletion (maximalIdeal A) A)) := by
    simpa using hnA.map (algebraMap A (AdicCompletion (maximalIdeal A) A))

  have hθc : ∀ w : (AdicCompletion (maximalIdeal A) A), (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) (UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) w) = UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) w :=
    fun w => θ₀.commutes w
  have hθU : (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) (UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ∉
      Ideal.span {UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m), UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ)} := hA2
  have hfix : ((θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) ^ n) (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b) = UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) * b := hA3 _
  have hfaith : ∀ k : ℕ, 0 < k → k < n → c k - 1 ∉ maximalIdeal (AdicCompletion (maximalIdeal A) A) :=
    fun k hk hkn hmem => (IsLocalRing.mem_maximalIdeal _).mp hmem (hRDu k hk hkn)
  obtain ⟨ζ₀, ζ₀', hζn, hζp, hζζ', hζU, hζV, hhook⟩ :=
    ModularCurve.UVCrossingModel.exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq
      (AdicCompletion (maximalIdeal A) A) (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) hirrhat m hm1 (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) hθc hθU n hn1 hnAh b hb hfix c
      hRD1 hfaith

  refine ⟨ζ₀, hζn, hζp, hOW, iL, iN, hCO, hconstO, hresO, hϖO, cx, cy, u, ι, γU, γV, θ₀, ζ₀', hζζ', iLM,
    hcxy, hιc, hιx, hιy, hcyW, hcxW, hA1, hζU, hζV, ?_⟩
  intro c' θ Mx hpres hcompat hlinW hlin hMc a hca
  have h1 := hRD2 c' θ Mx hpres hcompat hlinW hlin hMc a hca
  have h2 := hhook (algebraMap A (AdicCompletion (maximalIdeal A) A) a) h1
  exact (IsLocalRing.mem_maximalIdeal _).mp h2

end S_ModularCurve_FullLevel_AuxLevel_exists_ringEquiv_adicCompletion_uvCrossingModel_tangent_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_ringEquiv_adicCompletion_uvCrossingModel_tangent_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked (solution)
