-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.isNoetherianRing_and_mem_iff_and_exists_sub_of_end_blowupChart_of_drinfeldChartWitness_linked_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/98901df0-533b-597c-a0cb-82be9fd6c7e6

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
import Theorems.Thm_Subring_exists_isLocalRing_ringEquiv_adicCompletion_of_forall_mem_iff_exists_mul_eq_of_isMaximal
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense_of_dvd
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_moduleFinite_adjoin_jChartFin_chartAlgFin
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_isNoetherianRing_and_mem_iff_and_exists_sub_of_end_blowupChart_of_drinfeldChartWitness_linked_of_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace EndPinBasicsAux

open IsLocalRing

theorem exists_sub_algebraMap_mem
    {A K : Type*} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
    (hres : IsAlgClosed (ResidueField A))
    (C : Subalgebra A K) (hC : C.FG) (T : Set K) (hT : T.Finite)
    (Ba : Subalgebra A K) (hBa : Ba = (Algebra.adjoin ↥C T).restrictScalars A)
    (P : Ideal ↥Ba) (hP : P.IsMaximal) (hmP : ∀ r ∈ maximalIdeal A, algebraMap A ↥Ba r ∈ P)
    (b : ↥Ba) : ∃ c : A, b - algebraMap A ↥Ba c ∈ P := by
  classical
  obtain ⟨s₀, rfl⟩ := hC
  subst hBa
  have hfg : ((Algebra.adjoin ↥(Algebra.adjoin A (↑s₀ : Set K)) T).restrictScalars A).FG := by
    refine ⟨s₀ ∪ hT.toFinset, ?_⟩
    rw [Finset.coe_union, Set.Finite.coe_toFinset, Algebra.adjoin_union_eq_adjoin_adjoin]
  haveI hFT : Algebra.FiniteType A ↥((Algebra.adjoin ↥(Algebra.adjoin A (↑s₀ : Set K)) T).restrictScalars A) :=
    (Subalgebra.fg_iff_finiteType _).1 hfg
  haveI : P.IsMaximal := hP
  letI : Field (↥((Algebra.adjoin ↥(Algebra.adjoin A (↑s₀ : Set K)) T).restrictScalars A) ⧸ P) := Ideal.Quotient.field P
  let φ : ResidueField A →+* (↥((Algebra.adjoin ↥(Algebra.adjoin A (↑s₀ : Set K)) T).restrictScalars A) ⧸ P) :=
    Ideal.Quotient.lift (maximalIdeal A) ((Ideal.Quotient.mk P).comp (algebraMap A _)) (fun r hr => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hmP r hr)
  letI : Algebra (ResidueField A) (↥((Algebra.adjoin ↥(Algebra.adjoin A (↑s₀ : Set K)) T).restrictScalars A) ⧸ P) := φ.toAlgebra
  haveI : IsScalarTower A (ResidueField A) (↥((Algebra.adjoin ↥(Algebra.adjoin A (↑s₀ : Set K)) T).restrictScalars A) ⧸ P) :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Algebra.FiniteType (ResidueField A) (↥((Algebra.adjoin ↥(Algebra.adjoin A (↑s₀ : Set K)) T).restrictScalars A) ⧸ P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (ResidueField A) _
  haveI hfin := finite_of_finite_type_of_isJacobsonRing (ResidueField A)
    (↥((Algebra.adjoin ↥(Algebra.adjoin A (↑s₀ : Set K)) T).restrictScalars A) ⧸ P)
  obtain ⟨x, hx⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField A)
    (K := ↥((Algebra.adjoin ↥(Algebra.adjoin A (↑s₀ : Set K)) T).restrictScalars A) ⧸ P)).2 (Ideal.Quotient.mk P b)
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact hx.symm

theorem not_isUnit_of_mul_eq {K : Type*} [Field K] {Ba : Subring K} (P : Ideal ↥Ba) (hP : P.IsPrime)
    (O : Subring K) (hO : ∀ f : K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K))
    (x : ↥O) (p h : ↥Ba) (hp : p ∈ P) (hh : h ∉ P) (hx : (x : K) * (h : K) = (p : K)) : ¬ IsUnit x := by
  rintro ⟨u, rfl⟩
  obtain ⟨g', h', hh', he⟩ := (hO _).1 ((u⁻¹ : (↥O)ˣ) : ↥O).2
  have hinv : ((u : ↥O) : K) * (((u⁻¹ : (↥O)ˣ) : ↥O) : K) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  have hK : (p : K) * (g' : K) = (h : K) * (h' : K) := by
    rw [← hx, ← he]
    have : ((u : ↥O) : K) * (h : K) * ((((u⁻¹ : (↥O)ˣ) : ↥O) : K) * (h' : K)) =
        (((u : ↥O) : K) * (((u⁻¹ : (↥O)ˣ) : ↥O) : K)) * ((h : K) * (h' : K)) := by ring
    rw [this, hinv, one_mul]
  have hBa : p * g' = h * h' := Subtype.ext (by simpa using hK)
  have hmem : h * h' ∈ P := by rw [← hBa]; exact Ideal.mul_mem_right _ _ hp
  rcases hP.mem_or_mem hmem with h1 | h1
  · exact hh h1
  · exact hh' h1

end EndPinBasicsAux

open EndPinBasicsAux in

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

    (hjK : ModularCurve.jqNModC L q ∈ K)
    (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ chartAlgFin A (↥K) j)

    (m : ℕ) (hm1 : 1 ≤ m) (hmt : ∃ w : A, IsUnit w ∧ ϖ ^ m = ϖt * w)

    (a : ↥(chartAlgFin A (↥K) j)) (haJ : a ∈ J) (ha0 : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0)
    (Ba : Subalgebra A ↥K)
    (hBa : Ba = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)
    (P : Ideal ↥Ba) (hP : P.IsMaximal)

    (O : Subring ↥K)
    (hOdef : ∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K))
    (hOy : ∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
      ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O))
    (hOB : ¬ (∀ f : ↥K, f ∈ B → f ∈ O)) :

    IsNoetherianRing ↥Ba ∧

    (∀ c : ↥(chartAlgFin A (↥K) j), ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba) ∧

    (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba), (⟨_, hb⟩ : ↥Ba) ∈ P ↔ b ∈ y) ∧

    (∀ (f : ↥K) (hf : f ∈ O), ∃ (a' : A) (ha' : algebraMap A ↥K a' ∈ O), ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, ha'⟩)) ∧

    (∃ hta : algebraMap A ↥K ϖt * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∈ Ba, (⟨_, hta⟩ : ↥Ba) ∈ P) ∧

    (∀ i : ↥(chartAlgFin A (↥K) j), i ∈ J →
      ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∈ Ba) := by
  classical

  obtain ⟨htrA, hfinK, hsepK⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
      (q ^ 2 * M') H₁ L K hK A j hj
  haveI := hfinK
  haveI := hsepK
  have htrL : Transcendental L j := fun h => htrA ((IsFractionRing.isAlgebraic_iff A L ↥K).2 h)
  haveI hMF : Module.Finite ↥(Algebra.adjoin A ({jChartFin A (↥K) j} : Set ↥(chartAlgFin A (↥K) j))) ↥(chartAlgFin A (↥K) j) :=
    AlgebraicCurve.TwoChartIntegralModel.moduleFinite_adjoin_jChartFin_chartAlgFin A L (↥K) j htrL
  have hFTC : Algebra.FiniteType A ↥(chartAlgFin A (↥K) j) :=
    (Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton (jChartFin A (↥K) j))).trans
      (Module.Finite.finiteType ↥(chartAlgFin A (↥K) j))
  have hCfg : (chartAlgFin A (↥K) j).FG := (Subalgebra.fg_iff_finiteType _).2 hFTC
  haveI hCnoe : IsNoetherianRing ↥(chartAlgFin A (↥K) j) := isNoetherianRing_of_fg hCfg

  have hP1 : (1 : ↥Ba) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hCBa : ∀ c : ↥(chartAlgFin A (↥K) j), ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba := by
    intro c
    rw [hBa, Subalgebra.mem_restrictScalars]
    exact Subalgebra.algebraMap_mem _ c
  have hJBa : ∀ i : ↥(chartAlgFin A (↥K) j), i ∈ J → ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∈ Ba := by
    intro i hi
    rw [hBa, Subalgebra.mem_restrictScalars]
    exact Algebra.subset_adjoin ⟨i, hi, by rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]⟩
  obtain ⟨hBO, iOloc, hOP, -, hfrac, -⟩ :=
    Subring.exists_isLocalRing_ringEquiv_adicCompletion_of_forall_mem_iff_exists_mul_eq_of_isMaximal (↥K) Ba.toSubring P hP O hOdef
  haveI := iOloc
  have hCle : chartAlgFin A (↥K) j ≤ Ba := fun x hx => hCBa ⟨x, hx⟩

  have hyP : ∀ (b : ↥(chartAlgFin A (↥K) j)), b ∈ y → ∀ (hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba), (⟨_, hb⟩ : ↥Ba) ∈ P := by
    intro b hyb hb
    have h1 := hOy b hyb (hBO ⟨_, hb⟩)
    exact (hOP ⟨_, hb⟩).1 ((IsLocalRing.mem_maximalIdeal _).2 h1)
  have hPy : ∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba), (⟨_, hb⟩ : ↥Ba) ∈ P ↔ b ∈ y := by
    have key : y = P.comap (Subalgebra.inclusion hCle).toRingHom := by
      refine hy.eq_of_le ?_ ?_
      · intro htop
        apply hP1
        have h1 : (1 : ↥(chartAlgFin A (↥K) j)) ∈ P.comap (Subalgebra.inclusion hCle).toRingHom := by
          rw [htop]; exact Submodule.mem_top
        rw [Ideal.mem_comap, map_one] at h1
        exact h1
      · intro b hb
        rw [Ideal.mem_comap]
        have : (Subalgebra.inclusion hCle).toRingHom b = ⟨_, hCBa b⟩ := Subtype.ext rfl
        rw [this]
        exact hyP b hb (hCBa b)
    intro b hb
    constructor
    · intro h
      rw [key, Ideal.mem_comap]
      have : (Subalgebra.inclusion hCle).toRingHom b = ⟨_, hb⟩ := Subtype.ext rfl
      rw [this]
      exact h
    · intro h
      exact hyP b h hb

  obtain ⟨s, hs⟩ := (isNoetherian_def.1 hCnoe) J
  have hTfin : ((fun i : ↥(chartAlgFin A (↥K) j) => ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹) '' (↑s : Set ↥(chartAlgFin A (↥K) j))).Finite :=
    (Finset.finite_toSet s).image _
  have hadj : Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} =
      Algebra.adjoin ↥(chartAlgFin A (↥K) j) ((fun i : ↥(chartAlgFin A (↥K) j) => ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹) '' (↑s : Set ↥(chartAlgFin A (↥K) j))) := by
    apply le_antisymm
    · refine Algebra.adjoin_le ?_
      rintro x ⟨i, hi, hx⟩
      have hx' : x = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ := by
        rw [← hx, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
      rw [hx']
      rw [← hs] at hi
      refine Submodule.span_induction
        (p := fun (i : ↥(chartAlgFin A (↥K) j)) _ => ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∈
          Algebra.adjoin ↥(chartAlgFin A (↥K) j) ((fun i : ↥(chartAlgFin A (↥K) j) => ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹) '' (↑s : Set ↥(chartAlgFin A (↥K) j))))
        ?_ ?_ ?_ ?_ hi
      · intro i his
        exact Algebra.subset_adjoin ⟨i, his, rfl⟩
      · simp only [ZeroMemClass.coe_zero, zero_mul]
        exact zero_mem _
      · intro i i' _ _ h h'
        rw [Subalgebra.coe_add, add_mul]
        exact add_mem h h'
      · intro c i _ h
        rw [smul_eq_mul, Subalgebra.coe_mul, mul_assoc]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) h
    · refine Algebra.adjoin_mono ?_
      rintro x ⟨i, his, rfl⟩
      refine ⟨i, ?_, by rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]⟩
      rw [← hs]
      exact Submodule.subset_span his
  have hnoe' : IsNoetherianRing ↥(Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}) := by
    rw [hadj]
    exact isNoetherianRing_of_fg ⟨hTfin.toFinset, by rw [Set.Finite.coe_toFinset]⟩
  have hBanoe : IsNoetherianRing ↥Ba := by
    rw [hBa]
    exact hnoe'

  have hϖC : ((algebraMap A ↥(chartAlgFin A (↥K) j) ϖ : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba := hCBa _
  have hϖP : (⟨_, hϖC⟩ : ↥Ba) ∈ P := hyP _ hϖy hϖC
  have hmP : ∀ r ∈ maximalIdeal A, algebraMap A ↥Ba r ∈ P := by
    intro r hr
    rw [hϖ] at hr
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [map_mul]
    refine Ideal.mul_mem_left _ _ ?_
    have : algebraMap A ↥Ba ϖ = ⟨_, hϖC⟩ := Subtype.ext rfl
    rw [this]
    exact hϖP
  have hBa' : Ba = (Algebra.adjoin ↥(chartAlgFin A (↥K) j) ((fun i : ↥(chartAlgFin A (↥K) j) => ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹) '' (↑s : Set ↥(chartAlgFin A (↥K) j)))).restrictScalars A := by
    rw [hBa, hadj]
  have hresBa : ∀ g : ↥Ba, ∃ c : A, g - algebraMap A ↥Ba c ∈ P :=
    EndPinBasicsAux.exists_sub_algebraMap_mem ‹IsAlgClosed (ResidueField A)› (chartAlgFin A (↥K) j) hCfg _ hTfin Ba hBa' P hP hmP
  have hiv : ∀ (f : ↥K) (hf : f ∈ O), ∃ (a' : A) (ha' : algebraMap A ↥K a' ∈ O), ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, ha'⟩) := by
    intro f hf
    obtain ⟨g, h, hhP, hfh⟩ := hfrac f hf
    obtain ⟨cg, hcg⟩ := hresBa g
    obtain ⟨ch, hch⟩ := hresBa h
    have hchu : IsUnit ch := by
      by_contra hnu
      apply hhP
      have hmem : algebraMap A ↥Ba ch ∈ P := hmP ch ((IsLocalRing.mem_maximalIdeal _).2 hnu)
      have : h = (h - algebraMap A ↥Ba ch) + algebraMap A ↥Ba ch := by ring
      rw [this]
      exact add_mem hch hmem
    obtain ⟨uh, huh⟩ := hchu
    refine ⟨cg * ((uh⁻¹ : Aˣ) : A), hBO (algebraMap A ↥Ba (cg * ((uh⁻¹ : Aˣ) : A))), ?_⟩
    have hprod : (((⟨f, hf⟩ : ↥O) - ⟨_, hBO (algebraMap A ↥Ba (cg * ((uh⁻¹ : Aˣ) : A)))⟩ : ↥O) : ↥K) * ((h : ↥Ba) : ↥K) =
        (((g - algebraMap A ↥Ba (cg * ((uh⁻¹ : Aˣ) : A)) * h : ↥Ba)) : ↥K) := by
      have e1 := congrArg (fun z : ↥O => (z : ↥K)) hfh
      simp only [MulMemClass.coe_mul] at e1
      push_cast
      linear_combination e1
    refine EndPinBasicsAux.not_isUnit_of_mul_eq P hP.isPrime O hOdef _ _ h ?_ hhP hprod
    have hc : algebraMap A ↥Ba cg - algebraMap A ↥Ba (cg * ((uh⁻¹ : Aˣ) : A)) * algebraMap A ↥Ba ch = 0 := by
      rw [← map_mul, ← map_sub, mul_assoc, ← huh, Units.inv_mul, mul_one, sub_self, map_zero]
    have : g - algebraMap A ↥Ba (cg * ((uh⁻¹ : Aˣ) : A)) * h =
        (g - algebraMap A ↥Ba cg) - algebraMap A ↥Ba (cg * ((uh⁻¹ : Aˣ) : A)) * (h - algebraMap A ↥Ba ch) +
          (algebraMap A ↥Ba cg - algebraMap A ↥Ba (cg * ((uh⁻¹ : Aˣ) : A)) * algebraMap A ↥Ba ch) := by ring
    rw [this, hc, add_zero]
    exact sub_mem hcg (Ideal.mul_mem_left _ _ hch)

  have hK2 := ModularCurve.FullLevel.AuxLevelOne.comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁.1
  have hK1 := ModularCurve.FullLevel.AuxLevelOne.blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB
  have hK3 := ModularCurve.FullLevel.AuxLevelOne.map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ hK1.1 hK2.1 hK2.2.1 hK2.2.2.2.1 ⟨hK2.2.2.2.2.2.2.1, hK2.2.2.2.2.2.2.2.1⟩
  have htJ : algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ∈ J := hK3.2.2.2
  have hq0 : (q : A) ≠ 0 := by
    intro h0
    have : (q : L) = 0 := by rw [← map_natCast (algebraMap A L), h0, map_zero]
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  have hϖtA : ϖt ≠ 0 := by
    obtain ⟨uu, huu, hpow⟩ := hϖt
    intro h0
    rw [h0, zero_pow (Nat.sub_ne_zero_of_lt (by nlinarith [(Fact.out : q.Prime).two_le])), eq_comm, mul_eq_zero] at hpow
    rcases hpow with h | h
    · exact hq0 h
    · exact huu.ne_zero h
  have hϖt0 : algebraMap A ↥K ϖt ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A L ↥K]
    exact (map_ne_zero_iff _ (algebraMap L ↥K).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr hϖtA)
  have htaK : algebraMap A ↥K ϖt * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((algebraMap A ↥(chartAlgFin A (↥K) j) ϖt : ↥(chartAlgFin A (↥K) j)) : ↥K) := by
    rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]; rfl
  have htaBa : algebraMap A ↥K ϖt * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∈ Ba := by
    rw [hBa, Subalgebra.mem_restrictScalars]
    exact Algebra.subset_adjoin ⟨algebraMap A ↥(chartAlgFin A (↥K) j) ϖt, htJ, htaK⟩
  have htaP : (⟨_, htaBa⟩ : ↥Ba) ∈ P := by
    by_contra hn
    apply hOB
    have haO : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) * (algebraMap A ↥K ϖt)⁻¹ ∈ O := by
      refine (hOdef _).2 ⟨1, ⟨_, htaBa⟩, hn, ?_⟩
      rw [OneMemClass.coe_one]
      show ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) * (algebraMap A ↥K ϖt)⁻¹ * (algebraMap A ↥K ϖt * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹) = 1
      field_simp
    let OC : Subalgebra ↥(chartAlgFin A (↥K) j) ↥K :=
      { carrier := O
        mul_mem' := fun hx hy => O.mul_mem hx hy
        one_mem' := O.one_mem
        add_mem' := fun hx hy => O.add_mem hx hy
        zero_mem' := O.zero_mem
        algebraMap_mem' := fun c => hBO ⟨_, hCBa c⟩ }
    have hgen : {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} ⊆ (OC : Set ↥K) := by
      rintro x ⟨i, hi, hx⟩
      have hx' : x = (((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹) * (((a : ↥(chartAlgFin A (↥K) j)) : ↥K) * (algebraMap A ↥K ϖt)⁻¹) := by
        rw [← hx]; field_simp
      rw [hx']
      exact O.mul_mem (hBO ⟨_, hJBa i hi⟩) haO
    intro f hf
    rw [hB, Subalgebra.mem_restrictScalars] at hf
    exact (Algebra.adjoin_le hgen : _ ≤ OC) hf

  exact ⟨hBanoe, hCBa, hPy, hiv, ⟨htaBa, htaP⟩, hJBa⟩

end S_ModularCurve_FullLevel_AuxLevelOne_isNoetherianRing_and_mem_iff_and_exists_sub_of_end_blowupChart_of_drinfeldChartWitness_linked_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_isNoetherianRing_and_mem_iff_and_exists_sub_of_end_blowupChart_of_drinfeldChartWitness_linked_of_dvd (solution)
