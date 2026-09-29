-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.isUnit_of_notMem_maximalIdeal_exceptional_igusa_of_end_blowupChart_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a7495680-c5f7-5419-b939-2c48671a2cb7

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

import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_primes_exceptional_igusa_trichotomy_of_end_blowupChart_linked_of_dvd
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_monic_aeval_not_mem_maximalIdeal_of_not_isMaximal_centre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_isUnit_of_notMem_maximalIdeal_exceptional_igusa_of_end_blowupChart_of_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply"

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
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
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
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
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

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

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
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
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
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
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

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

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
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
          (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ)
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
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ f : ↥K, f ∈ B → τ f ∈ B) ∧
      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧
      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
              b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W))
    (O : Subring ↥K)

    (hO : ∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
      let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
      ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
        (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
        (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
          ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
        ¬ (∀ f : ↥K, f ∈ B → f ∈ O))

    (hOW : ∀ f : ↥K, f ∈ O → f ∈ W) (hOloc : IsLocalRing ↥O) (hOnoe : IsNoetherianRing ↥O)
    (hCO : ∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ O)

    (hIgStab : ∀ V : ValuationSubring ↥K, (∀ x : L, algebraMap L ↥K x ∈ V ↔ ∃ a : A, algebraMap A L a = x) →
        (∃ hϖV : algebraMap A ↥K ϖ ∈ V, (⟨algebraMap A ↥K ϖ, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →

        (∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ V) →
        (∃ c : ↥(chartAlgFin A (↥K) j), ∀ p : Polynomial A, p.Monic →
          ∃ hp : Polynomial.aeval ((c : ↥K)) (p.map (algebraMap A ↥K)) ∈ V, (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
        ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ f : ↥K, f ∈ V ↔ τ f ∈ V) :

      ∀ (s : ↥(chartAlgFin A (↥K) j)) (k : ℕ) (z : ↥(chartAlgFin A (↥K) j)), s * z = algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ^ k →
        ∀ (a : ↥(chartAlgFin A (↥K) j)), a ∈ J → ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0 →
          ∀ (P : Ideal ↥((Algebra.adjoin ↥(chartAlgFin A (↥K) j)
              {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)), P.IsMaximal →
            (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥((Algebra.adjoin ↥(chartAlgFin A (↥K) j)
              {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A),
                h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) →
            ∀ (N : ℕ), ((s : ↥(chartAlgFin A (↥K) j)) : ↥K) * ((((a : ↥(chartAlgFin A (↥K) j)) : ↥K)) ^ N)⁻¹ ∈ O →
              (∀ hW : ((s : ↥(chartAlgFin A (↥K) j)) : ↥K) * ((((a : ↥(chartAlgFin A (↥K) j)) : ↥K)) ^ N)⁻¹ ∈ W, (⟨_, hW⟩ : ↥W) ∉ maximalIdeal ↥W) →
              (∀ V : ValuationSubring ↥K, (∀ x : L, algebraMap L ↥K x ∈ V ↔ ∃ a : A, algebraMap A L a = x) →
          (∀ hϖV : algebraMap A ↥K ϖ ∈ V, (⟨algebraMap A ↥K ϖ, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
          (∀ hjV : (j : ↥K) ∈ V, (∀ p : Polynomial A, p.Monic →
          ∀ hp : Polynomial.aeval (j : ↥K) (p.map (algebraMap A ↥K)) ∈ V,
          (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                (∀ f : ↥K, f ∈ O → f ∈ V) →
                ∀ hV : ((s : ↥(chartAlgFin A (↥K) j)) : ↥K) * ((((a : ↥(chartAlgFin A (↥K) j)) : ↥K)) ^ N)⁻¹ ∈ V, (⟨_, hV⟩ : ↥V) ∉ maximalIdeal ↥V)) →
              (((a : ↥(chartAlgFin A (↥K) j)) : ↥K)) ^ N * (((s : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∈ O := by
  classical
  intro s k zc hsz a haJ ha0 P hPmax hOiff N hxO hxW hxV
  have hE2 := ModularCurve.FullLevel.AuxLevelOne.exists_primes_exceptional_igusa_trichotomy_of_end_blowupChart_linked_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss hArig z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB W hBW hR1 hR2 hR3 hEQ O hO
  obtain ⟨-, 𝔮E, 𝔮I, hEp, hIp, hEI, hEchar, hϖI, ⟨b, hby, hbI⟩, -, -, htri⟩ := hE2
  haveI := hEp
  haveI := hIp
  haveI := hOnoe
  haveI := hOloc
  obtain ⟨-, hϖW, -, hyW, -⟩ := hR3

  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    have : maximalIdeal A = ⊥ := by rw [hϖ, h0, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_isField A (IsLocalRing.isField_iff_maximalIdeal_eq.mpr this)
  have hϖK0 : algebraMap A ↥K ϖ ≠ 0 := fun h0 => hϖ0 (hinjAK (by simpa using h0))
  have hszK : ((s : ↥(chartAlgFin A (↥K) j)) : ↥K) * ((zc : ↥(chartAlgFin A (↥K) j)) : ↥K) = algebraMap A ↥K ϖ ^ k := by
    have := congrArg (fun c : ↥(chartAlgFin A (↥K) j) => (c : ↥K)) hsz
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap] using this
  have hs0 : ((s : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0 := by
    intro h0
    have : algebraMap A ↥K ϖ ^ k = 0 := by rw [← hszK, h0, zero_mul]
    exact pow_ne_zero _ hϖK0 this
  set x : ↥K := ((s : ↥(chartAlgFin A (↥K) j)) : ↥K) * ((((a : ↥(chartAlgFin A (↥K) j)) : ↥K)) ^ N)⁻¹ with hxdef
  have hx0 : x ≠ 0 := mul_ne_zero hs0 (inv_ne_zero (pow_ne_zero _ ha0))
  have hϖO : algebraMap A ↥K ϖ ∈ O := hCO (algebraMap A ↥(chartAlgFin A (↥K) j) ϖ)
  have hOV_unit : ∀ (V : ValuationSubring ↥K), (∀ f : ↥K, f ∈ O → f ∈ V) →
      ∀ (f : ↥K) (hf : f ∈ O), IsUnit (⟨f, hf⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∉ maximalIdeal ↥V := by
    intro V hOV f hf hu hfV hmem
    obtain ⟨u, hu⟩ := hu
    have hinv : ((u⁻¹ : (↥O)ˣ) : ↥O).1 * f = 1 := by
      have := congrArg (fun t : ↥O => (t : ↥K)) u.inv_mul
      simpa [hu] using this
    have : IsUnit (⟨f, hfV⟩ : ↥V) :=
      IsUnit.of_mul_eq_one_right ⟨_, hOV _ ((u⁻¹ : (↥O)ˣ) : ↥O).2⟩ (Subtype.ext hinv)
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem this

  suffices hu : IsUnit (⟨x, hxO⟩ : ↥O) by
    obtain ⟨u, hu⟩ := hu
    have hmul : x * (((u⁻¹ : (↥O)ˣ) : ↥O) : ↥K) = 1 := by
      have := congrArg (fun t : ↥O => (t : ↥K)) u.mul_inv
      simpa [hu] using this
    have hinv : (((u⁻¹ : (↥O)ˣ) : ↥O) : ↥K) = x⁻¹ := (eq_inv_of_mul_eq_one_right hmul)
    have hx' : x⁻¹ = (((a : ↥(chartAlgFin A (↥K) j)) : ↥K)) ^ N * (((s : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ := by
      rw [hxdef, mul_inv, inv_inv, mul_comm]
    rw [← hx', ← hinv]
    exact ((u⁻¹ : (↥O)ˣ) : ↥O).2
  by_contra hnu

  set X : ↥O := ⟨x, hxO⟩ with hXdef
  have hXne : Ideal.span ({X} : Set ↥O) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hnu
  obtain ⟨⟨𝔮, h𝔮⟩⟩ := Ideal.nonempty_minimalPrimes hXne
  have h𝔮p : 𝔮.IsPrime := h𝔮.1.1
  haveI := h𝔮p
  have hX𝔮 : X ∈ 𝔮 := h𝔮.1.2 (Ideal.subset_span rfl)
  have hht : 𝔮.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span ({X} : Set ↥O)) 𝔮 h𝔮
  have hϖ𝔮 : ∀ h : algebraMap A ↥K ϖ ∈ O, (⟨algebraMap A ↥K ϖ, h⟩ : ↥O) ∈ 𝔮 := by
    intro h
    have haz : (((a : ↥(chartAlgFin A (↥K) j)) : ↥K)) ^ N * ((zc : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O :=
      O.mul_mem (O.pow_mem (hCO a) N) (hCO zc)
    have hpow : (⟨algebraMap A ↥K ϖ, h⟩ : ↥O) ^ k = X * ⟨_, haz⟩ := by
      apply Subtype.ext
      show algebraMap A ↥K ϖ ^ k = x * ((((a : ↥(chartAlgFin A (↥K) j)) : ↥K)) ^ N * ((zc : ↥(chartAlgFin A (↥K) j)) : ↥K))
      rw [← hszK, hxdef]; field_simp
    exact h𝔮p.mem_of_pow_mem k (hpow ▸ Ideal.mul_mem_right _ _ hX𝔮)

  have hne_E : 𝔮 ≠ 𝔮E := by
    intro h
    have : X ∈ 𝔮E := h ▸ hX𝔮
    exact hxW (hOW _ hxO) ((hEchar x hxO (hOW _ hxO)).mp this)

  have hne_I : 𝔮 ≠ 𝔮I := by
    intro h
    have hXI : X ∈ 𝔮I := h ▸ hX𝔮
    obtain ⟨V, hV⟩ := (LocalSubring.ofPrime O 𝔮I).exists_le_valuationSubring
    obtain ⟨hle, hloc⟩ := hV
    have hOV : ∀ f : ↥K, f ∈ O → f ∈ V := fun f hf => hle (LocalSubring.le_ofPrime O 𝔮I hf)

    have hIV : ∀ (f : ↥K) (hf : f ∈ O), (⟨f, hf⟩ : ↥O) ∈ 𝔮I →
        ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V := by
      intro f hf hfI hfV
      have h1 : algebraMap ↥O ↥(LocalSubring.ofPrime O 𝔮I).toSubring ⟨f, hf⟩ ∈
          maximalIdeal ↥(LocalSubring.ofPrime O 𝔮I).toSubring :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔮I _).mpr hfI
      rw [IsLocalRing.mem_maximalIdeal] at h1 ⊢
      intro hu
      apply h1
      haveI := hloc
      apply (isUnit_map_iff (Subring.inclusion hle) _).mp
      have : (Subring.inclusion hle (algebraMap ↥O ↥(LocalSubring.ofPrime O 𝔮I).toSubring ⟨f, hf⟩) : ↥V.toLocalSubring.toSubring) = ⟨f, hfV⟩ :=
        Subtype.ext rfl
      rw [this]
      exact hu
    have hIV' : ∀ (f : ↥K) (hf : f ∈ O), (⟨f, hf⟩ : ↥O) ∉ 𝔮I →
        ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∉ maximalIdeal ↥V := by
      intro f hf hfI hfV hmem
      apply hfI
      have h1 : algebraMap ↥O ↥(LocalSubring.ofPrime O 𝔮I).toSubring ⟨f, hf⟩ ∈
          maximalIdeal ↥(LocalSubring.ofPrime O 𝔮I).toSubring := by
        rw [IsLocalRing.mem_maximalIdeal]
        intro hu
        have hu' := hu.map (Subring.inclusion hle)
        have : (Subring.inclusion hle (algebraMap ↥O ↥(LocalSubring.ofPrime O 𝔮I).toSubring ⟨f, hf⟩) : ↥V.toLocalSubring.toSubring) = ⟨f, hfV⟩ :=
          Subtype.ext rfl
        rw [this] at hu'
        exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu'
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔮I _).mp h1

    have hAV : ∀ a' : A, algebraMap A ↥K a' ∈ V := fun a' => hOV _ (hCO (algebraMap A ↥(chartAlgFin A (↥K) j) a'))
    have hϖV : ∀ hϖV : algebraMap A ↥K ϖ ∈ V, (⟨algebraMap A ↥K ϖ, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V :=
      fun hh => hIV _ hϖO (hϖI hϖO) hh
    have hconst : ∀ xL : L, algebraMap L ↥K xL ∈ V ↔ ∃ a' : A, algebraMap A L a' = xL := by
      intro xL
      constructor
      · intro hxV
        rcases ValuationRing.isInteger_or_isInteger A xL with ⟨a', ha'⟩ | ⟨a', ha'⟩
        · exact ⟨a', ha'⟩
        ·
          by_cases hxL0 : xL = 0
          · exact ⟨0, by simp [hxL0]⟩
          by_cases hua : IsUnit a'
          · obtain ⟨u, rfl⟩ := hua
            refine ⟨((u⁻¹ : Aˣ) : A), ?_⟩
            have : algebraMap A L (u : A) * xL = 1 := by rw [ha', inv_mul_cancel₀ hxL0]
            calc algebraMap A L ((u⁻¹ : Aˣ) : A) = algebraMap A L ((u⁻¹ : Aˣ) : A) * (algebraMap A L (u : A) * xL) := by rw [this, mul_one]
              _ = xL := by rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
          · exfalso
            have ha'm : a' ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hua
            rw [hϖ, Ideal.mem_span_singleton'] at ha'm
            obtain ⟨c, hc⟩ := ha'm

            have h1 : algebraMap L ↥K xL * (algebraMap A ↥K c * algebraMap A ↥K ϖ) = 1 := by
              rw [← map_mul, hc, IsScalarTower.algebraMap_apply A L ↥K, ha', ← map_mul, mul_inv_cancel₀ hxL0, map_one]
            have hmem : (⟨algebraMap L ↥K xL * (algebraMap A ↥K c * algebraMap A ↥K ϖ),
                V.mul_mem _ _ hxV (V.mul_mem _ _ (hAV c) (hAV ϖ))⟩ : ↥V) ∈ maximalIdeal ↥V := by
              have : (⟨algebraMap L ↥K xL * (algebraMap A ↥K c * algebraMap A ↥K ϖ),
                  V.mul_mem _ _ hxV (V.mul_mem _ _ (hAV c) (hAV ϖ))⟩ : ↥V) =
                  ⟨algebraMap L ↥K xL * algebraMap A ↥K c, V.mul_mem _ _ hxV (hAV c)⟩ * ⟨algebraMap A ↥K ϖ, hAV ϖ⟩ :=
                Subtype.ext (by show _ = (_ * _) * _; ring)
              rw [this]; exact Ideal.mul_mem_left _ _ (hϖV (hAV ϖ))
            have : (⟨_, V.mul_mem _ _ hxV (V.mul_mem _ _ (hAV c) (hAV ϖ))⟩ : ↥V) = 1 := Subtype.ext h1
            rw [this] at hmem
            exact (maximalIdeal.isMaximal ↥V).ne_top ((Ideal.eq_top_iff_one _).mpr hmem)
      · rintro ⟨a', rfl⟩
        rw [← IsScalarTower.algebraMap_apply A L ↥K]; exact hAV a'

    have hVC : ∀ c : ↥(chartAlgFin A (↥K) j), (c : ↥K) ∈ V := fun c => hOV _ (hCO c)
    let ψ : ↥(chartAlgFin A (↥K) j) →+* ↥V :=
      { toFun := fun c => ⟨(c : ↥K), hVC c⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun a b => Subtype.ext rfl
        map_zero' := Subtype.ext rfl
        map_add' := fun a b => Subtype.ext rfl }
    let yV : Ideal ↥(chartAlgFin A (↥K) j) := Ideal.comap ψ (maximalIdeal ↥V)
    have hyV : ∀ c : ↥(chartAlgFin A (↥K) j), c ∈ yV ↔ ∀ hc : (c : ↥K) ∈ V, (⟨(c : ↥K), hc⟩ : ↥V) ∈ maximalIdeal ↥V := by
      intro c; rw [Ideal.mem_comap]
      exact ⟨fun h _ => h, fun h => h (hVC c)⟩
    have hyV_le : yV ≤ y := by
      intro c hc
      rw [hyV] at hc
      by_contra hcy

      obtain ⟨a₀, ha₀J, ha₀0, P₀, hP₀max, hOiff₀, hOy₀, -⟩ := hO
      have hcBa : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
          {x : ↥K | ∃ i ∈ J, x * ((a₀ : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A :=
        (Subalgebra.mem_restrictScalars A).mpr (Subalgebra.algebraMap_mem _ c)
      let ψ₀ : ↥(chartAlgFin A (↥K) j) →+* ↥((Algebra.adjoin ↥(chartAlgFin A (↥K) j)
          {x : ↥K | ∃ i ∈ J, x * ((a₀ : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A) :=
        { toFun := fun d => ⟨((d : ↥(chartAlgFin A (↥K) j)) : ↥K), (Subalgebra.mem_restrictScalars A).mpr (Subalgebra.algebraMap_mem _ d)⟩
          map_one' := Subtype.ext rfl
          map_mul' := fun a b => Subtype.ext rfl
          map_zero' := Subtype.ext rfl
          map_add' := fun a b => Subtype.ext rfl }
      have hyP : y ≤ P₀.comap ψ₀ := by
        intro d hd
        rw [Ideal.mem_comap]
        by_contra hdP
        have hd0 : ((d : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0 := by
          intro h0; apply hdP
          have : ψ₀ d = 0 := Subtype.ext h0
          rw [this]; exact Submodule.zero_mem _
        have hdinv : (((d : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∈ O := by
          rw [hOiff₀]
          refine ⟨1, ψ₀ d, hdP, ?_⟩
          show (((d : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ * ((d : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((1 : ↥((Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a₀ : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)) : ↥K)
          rw [inv_mul_cancel₀ hd0]; rfl
        exact hOy₀ d hd (hCO d) (IsUnit.of_mul_eq_one ⟨_, hdinv⟩ (Subtype.ext (mul_inv_cancel₀ hd0)))
      have hPC : P₀.comap ψ₀ ≠ ⊤ := Ideal.comap_ne_top ψ₀ hP₀max.ne_top
      have hyeq := hy.eq_of_le hPC hyP
      have hcP : ψ₀ c ∉ P₀ := by
        intro h; apply hcy; rw [hyeq, Ideal.mem_comap]; exact h
      have hc0 : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0 := by
        intro h0; apply hcP
        have : ψ₀ c = 0 := Subtype.ext h0
        rw [this]; exact Submodule.zero_mem _
      have hcinv : (((c : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∈ O := by
        rw [hOiff₀]
        refine ⟨1, ψ₀ c, hcP, ?_⟩
        show (((c : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ * ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((1 : ↥((Algebra.adjoin ↥(chartAlgFin A (↥K) j)
          {x : ↥K | ∃ i ∈ J, x * ((a₀ : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)) : ↥K)
        rw [inv_mul_cancel₀ hc0]; rfl
      have hcu : IsUnit (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO c⟩ : ↥O) :=
        IsUnit.of_mul_eq_one ⟨_, hcinv⟩ (Subtype.ext (mul_inv_cancel₀ hc0))
      exact hOV_unit V hOV _ (hCO c) hcu (hVC c) (hc (hVC c))
    have hyV_ne : yV ≠ y := by
      intro heq
      have : b ∈ yV := heq ▸ hby
      rw [hyV] at this
      exact hIV' _ (hCO b) (hbI (hCO b)) (hVC b) (this (hVC b))
    have hny : ¬ yV.IsMaximal := fun hm => hyV_ne (hm.eq_of_le hy.ne_top hyV_le)
    have hjT := AlgebraicCurve.TwoChartIntegralModel.forall_monic_aeval_not_mem_maximalIdeal_of_not_isMaximal_centre
      A (↥K) j V hAV (by
        intro a' ha'
        rw [hϖ, Ideal.mem_span_singleton'] at ha'
        obtain ⟨c, rfl⟩ := ha'
        have : (⟨algebraMap A ↥K (c * ϖ), hAV _⟩ : ↥V) = ⟨algebraMap A ↥K c, hAV c⟩ * ⟨algebraMap A ↥K ϖ, hAV ϖ⟩ :=
          Subtype.ext (by show algebraMap A ↥K (c * ϖ) = algebraMap A ↥K c * algebraMap A ↥K ϖ; exact map_mul _ _ _)
        rw [this]; exact Ideal.mul_mem_left _ _ (hϖV (hAV ϖ))) hVC yV hyV hny

    have hjV : (j : ↥K) ∈ V := hVC (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j)
    have := hxV V hconst hϖV hjV (hjT hjV) hOV (hOV x hxO)
    exact this (hIV x hxO hXI (hOV x hxO))

  have hEle : 𝔮E ≤ 𝔮 := by
    intro f hf
    apply htri 𝔮 h𝔮p hϖ𝔮 hne_E hne_I f
    intro hu
    exact hEp.ne_top (Ideal.eq_top_of_isUnit_mem _ hf hu)
  have hElt : 𝔮E < 𝔮 := lt_of_le_of_ne hEle (Ne.symm hne_E)
  have hϖE : (⟨algebraMap A ↥K ϖ, hϖO⟩ : ↥O) ∈ 𝔮E := by
    rw [hEchar _ hϖO (hBW _ (B.algebraMap_mem ϖ)), hϖW]
    exact Ideal.subset_span rfl
  have hbotlt : (⊥ : Ideal ↥O) < 𝔮E := by
    rw [bot_lt_iff_ne_bot]
    intro h
    have : (⟨algebraMap A ↥K ϖ, hϖO⟩ : ↥O) = 0 := by simpa [h] using hϖE
    exact hϖK0 (congrArg Subtype.val this)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbotlt
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hElt
  rw [Ideal.height_bot, zero_add] at h1
  have : (2 : ℕ∞) ≤ 𝔮.height := by
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ 𝔮E.height + 1 := add_le_add h1 le_rfl
      _ ≤ 𝔮.height := h2
  have := this.trans hht
  norm_num at this

end S_ModularCurve_FullLevel_AuxLevelOne_isUnit_of_notMem_maximalIdeal_exceptional_igusa_of_end_blowupChart_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_isUnit_of_notMem_maximalIdeal_exceptional_igusa_of_end_blowupChart_of_dvd (solution)
