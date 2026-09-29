-- Prove2me | solution 1 for ModularCurve.XOneP.exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/126eac3f-8c8c-58dc-8b97-dbfff03d5144

import Mathlib
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_Module_Finite_quotient_of_isUnit_leadingCoeff_of_mem
import Theorems.Thm_ModularCurve_exists_int_poly_natDegree_aeval_jFull_eq_mul_aeval_modularUnitSeries
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionField
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_jGeomGen"
p2m_attr_erase "simp" "ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false

open scoped Polynomial

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

namespace C1FinLevelX1

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem ringHom_aeval_int {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T) (x : S) (P : ℤ[X]) :
    φ (Polynomial.aeval x P) = Polynomial.aeval (φ x) P := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

theorem finrank_quotient_le_mul_natDegree
    (R : Type*) [CommRing R] [Nontrivial R] (A : Type*) [CommRing A] [Algebra R A] [Algebra R[X] A]
    [IsScalarTower R R[X] A] (m : ℕ) (f : (Fin m → R[X]) →ₗ[R[X]] A) (hf : Function.Surjective f)
    (N : R[X]) (hN : IsUnit N.leadingCoeff) (I : Ideal A) (hNI : algebraMap R[X] A N ∈ I) :
    Module.finrank R (A ⧸ I) ≤ m * N.natDegree := by
  classical
  obtain ⟨u, hu⟩ := hN

  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : R[X], N₁ = Polynomial.C (↑u⁻¹ : R) * N := ⟨_, rfl⟩
  have hmon : N₁.Monic := by
    rw [hN₁]
    exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu, Units.inv_mul])
  have hdeg : N₁.natDegree = N.natDegree := by
    rw [hN₁]
    exact Polynomial.natDegree_C_mul_of_mul_ne_zero (by rw [← hu, Units.inv_mul]; exact one_ne_zero)
  have hN₁I : algebraMap R[X] A N₁ ∈ I := by
    rw [hN₁, map_mul]
    exact I.mul_mem_left _ hNI

  obtain ⟨a, ha⟩ : ∃ a : A, a = algebraMap R[X] A Polynomial.X := ⟨_, rfl⟩
  have hX : (Polynomial.aeval a : R[X] →ₐ[R] A) = IsScalarTower.toAlgHom R R[X] A :=
    Polynomial.algHom_ext (by rw [Polynomial.aeval_X, IsScalarTower.toAlgHom_apply, ha])
  have hX' : ∀ P : R[X], Polynomial.aeval a P = algebraMap R[X] A P := fun P => by
    rw [hX, IsScalarTower.toAlgHom_apply]

  have hroot : N₁.eval₂ (↑(Algebra.ofId R (A ⧸ I)) : R →+* A ⧸ I) (Ideal.Quotient.mk I a) = 0 := by
    have h1 : (↑(Algebra.ofId R (A ⧸ I)) : R →+* A ⧸ I) = (Ideal.Quotient.mk I).comp (algebraMap R A) := rfl
    rw [h1, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hX', Ideal.Quotient.eq_zero_iff_mem]
    exact hN₁I
  let ψ : AdjoinRoot N₁ →ₐ[R] A ⧸ I := AdjoinRoot.liftAlgHom N₁ (Algebra.ofId R (A ⧸ I)) (Ideal.Quotient.mk I a) hroot
  have hψ : ∀ P : R[X], ψ (AdjoinRoot.mk N₁ P) = Ideal.Quotient.mk I (algebraMap R[X] A P) := by
    intro P
    change AdjoinRoot.liftAlgHom N₁ (Algebra.ofId R (A ⧸ I)) (Ideal.Quotient.mk I a) hroot (AdjoinRoot.mk N₁ P) = _
    rw [AdjoinRoot.liftAlgHom_mk]
    have h1 : (↑(Algebra.ofId R (A ⧸ I)) : R →+* A ⧸ I) = (Ideal.Quotient.mk I).comp (algebraMap R A) := rfl
    rw [h1, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hX']

  let gen : Fin m → A := fun i => f (fun j => if i = j then 1 else 0)
  let Φ : (Fin m → AdjoinRoot N₁) →ₗ[R] A ⧸ I :=
    { toFun := fun w => ∑ i, ψ (w i) * Ideal.Quotient.mk I (gen i)
      map_add' := fun w w' => by
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r w => by
        simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply] }
  have hΦ : Function.Surjective Φ := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨w, rfl⟩ := hf x
    refine ⟨fun i => AdjoinRoot.mk N₁ (w i), ?_⟩
    change ∑ i, ψ (AdjoinRoot.mk N₁ (w i)) * Ideal.Quotient.mk I (gen i) = Ideal.Quotient.mk I (f w)
    rw [LinearMap.pi_apply_eq_sum_univ f w, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψ, Algebra.smul_def, map_mul]

  let pb := AdjoinRoot.powerBasis' hmon
  haveI : Module.Free R (AdjoinRoot N₁) := Module.Free.of_basis pb.basis
  haveI : Module.Finite R (AdjoinRoot N₁) := Module.Finite.of_basis pb.basis
  have hrk : Module.finrank R (Fin m → AdjoinRoot N₁) = m * N.natDegree := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, pb.finrank,
      ← hdeg]
    rfl
  calc Module.finrank R (A ⧸ I) = Module.finrank R ↥(LinearMap.range Φ) := by
        rw [LinearMap.range_eq_top.mpr hΦ, finrank_top]
    _ ≤ Module.finrank R (Fin m → AdjoinRoot N₁) := LinearMap.finrank_range_le Φ
    _ = m * N.natDegree := hrk

end C1FinLevelX1

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open C1FinLevelX1 in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (v : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hv : ((v : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p) ∨
      ((v : ↥K) : LaurentSeries L) = (p : LaurentSeries L) ^ 12 * (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))⁻¹)
    :
    ∃ Kb : ℕ, ∀ g : ℤ[X], g.Monic → (g.map (Int.castRingHom (ZMod p))).coeff 0 ≠ 0 →
      Module.Finite A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
      Module.finrank A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ≤ Kb * g.natDegree := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  let jA : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) := ModularCurve.TwoChart.jChartFin A (↥K) j
  letI algXA : Algebra A[X] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) := (Polynomial.aeval jA).toRingHom.toAlgebra
  haveI istXA : IsScalarTower A A[X] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) :=
    IsScalarTower.of_algebraMap_eq' (Polynomial.aeval jA).comp_algebraMap.symm
  have halgXA : ∀ P : A[X], algebraMap A[X] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) P = Polynomial.aeval jA P := fun _ => rfl
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
    subst hK
    exact ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 (M * p)) hT L _ rfl j hj
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsSeparable.of_integral _ _
  haveI hfin : Module.Finite A[X] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) :=
    (AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep).1
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' A[X] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)

  set u₀ : LaurentSeries ℚ := ModularCurve.modularUnitSeries p with hu₀def
  have hmem : u₀ ∈ ModularCurve.modularFunctionFieldFull p :=
    ModularCurve.modularFunctionField_le_full p (ModularCurve.modularUnitSeries_mem_modularFunctionField p)
  have hΓ : CongruenceSubgroup.Gamma1 (M * p) ≤ CongruenceSubgroup.Gamma0 p := by
    intro γ hγ
    have h0 := CongruenceSubgroup.Gamma1_in_Gamma0 (M * p) hγ
    rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 ⊢
    exact (Int.natCast_dvd_natCast.mpr (Dvd.intro_left M rfl) : (p : ℤ) ∣ (M * p : ℕ)).trans (by exact_mod_cast h0)
  have hle : ModularCurve.modularFunctionFieldFull p ≤ ModularCurve.x1FunctionField (M * p) := by
    rw [← ModularCurve.modularFunctionFieldFullC_rat]
    exact (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ p).trans (ModularCurve.qExpFunctionFieldC_mono ℚ hΓ)
  have hKmem : ∀ x : ↥(ModularCurve.modularFunctionFieldFull p), ModularCurve.coeffEmb L (x : LaurentSeries ℚ) ∈ K := by
    intro x
    rw [hK]
    exact ModularCurve.coeffEmb_mem_laurentBaseChange L (hle x.2)
  let θ : ↥(ModularCurve.modularFunctionFieldFull p) →+* ↥K :=
    RingHom.codRestrict ((ModularCurve.coeffEmb L).comp (ModularCurve.modularFunctionFieldFull p).toSubring.subtype) K hKmem
  have hθ : ∀ x, ((θ x : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (x : LaurentSeries ℚ) := fun _ => rfl
  have hθj : θ (ModularCurve.IgusaScheme.jFull p) = j := by
    apply Subtype.ext
    rw [hθ, ModularCurve.IgusaScheme.coe_jFull, hj]
  let θℤ : ↥(ModularCurve.modularFunctionFieldFull p) →ₐ[ℤ] ↥K := θ.toIntAlgHom
  have hmapadj : ∀ x ∈ Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p)),
      θ x ∈ Algebra.adjoin A ({j} : Set ↥K) := by
    intro x hx
    have h1 : θℤ x ∈ (Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p))).map θℤ :=
      Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton] at h1
    have h2 : Algebra.adjoin ℤ ({θℤ (ModularCurve.IgusaScheme.jFull p)} : Set ↥K) ≤
        (Algebra.adjoin A ({j} : Set ↥K)).restrictScalars ℤ := by
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      show θ (ModularCurve.IgusaScheme.jFull p) ∈ Algebra.adjoin A ({j} : Set ↥K)
      rw [hθj]
      exact Algebra.subset_adjoin rfl
    exact h2 h1
  let φ : ↥(Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p))) →+*
      ↥(Algebra.adjoin A ({j} : Set ↥K)) :=
    RingHom.codRestrict (θ.comp (Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set _)).toSubring.subtype) _
      (fun x => hmapadj x x.2)
  have hcomp : (algebraMap ↥(Algebra.adjoin A ({j} : Set ↥K)) ↥K).comp φ =
      θ.comp (algebraMap ↥(Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p))) ↥(ModularCurve.modularFunctionFieldFull p)) := by
    ext x
    rfl
  have hI : ∀ {a : ↥(ModularCurve.modularFunctionFieldFull p)},
      a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (ModularCurve.IgusaScheme.jFull p) →
      θ a ∈ ModularCurve.TwoChart.chartAlgFin A (↥K) j := by
    intro a ha
    rw [ModularCurve.TwoChart.mem_chartAlg_iff]
    rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff] at ha
    exact ha.map_of_comp_eq φ θ hcomp
  have hu₀0 : (⟨u₀, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull p)) ≠ 0 := by
    intro h
    apply ModularCurve.modularUnitSeries_ne_zero p
    have := congrArg (fun x : ↥(ModularCurve.modularFunctionFieldFull p) => (x : LaurentSeries ℚ)) h
    simpa using this

  refine ⟨m * (p - 1), fun g hg hg0 => ?_⟩
  by_cases hD : g.natDegree = 0
  ·
    have hg1 : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hg hD
    subst hg1
    have htop : Ideal.span {Polynomial.aeval v (1 : ℤ[X])} = (⊤ : Ideal ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) := by
      rw [map_one, Ideal.span_singleton_one]
    haveI : Subsingleton (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v (1 : ℤ[X])}) :=
      Ideal.Quotient.subsingleton_iff.mpr htop
    exact ⟨inferInstance, by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _⟩
  have hD1 : 1 ≤ g.natDegree := Nat.one_le_iff_ne_zero.mpr hD
  have hndvd : ¬ (p : ℤ) ∣ g.coeff 0 := by
    intro h
    apply hg0
    rw [Polynomial.coeff_map, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h
  have h0 : g.coeff 0 ≠ 0 := fun h => hndvd (h ▸ dvd_zero _)

  obtain ⟨vq, hvq, hθv⟩ : ∃ vq : ↥(ModularCurve.modularFunctionFieldFull p),
      (vq = ⟨u₀, hmem⟩ ∨ vq = (p : ↥(ModularCurve.modularFunctionFieldFull p)) ^ 12 * (⟨u₀, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull p))⁻¹) ∧ θ vq = (v : ↥K) := by
    rcases hv with h | h
    · refine ⟨_, Or.inl rfl, Subtype.ext ?_⟩
      rw [hθ, h]
    · refine ⟨_, Or.inr rfl, Subtype.ext ?_⟩
      rw [hθ, h]
      simp [u₀, map_natCast]
  obtain ⟨N, ε, k, c, hdegN, hlcN, hcA, hNc⟩ :=
    ModularCurve.exists_int_poly_natDegree_aeval_jFull_eq_mul_aeval_modularUnitSeries p hmem vq hvq g hg hD1 h0

  let c' : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) := ⟨θ c, hI hcA⟩
  have hNA : Polynomial.aeval jA N = c' * Polynomial.aeval v g := by
    apply Subtype.ext
    have e1 : ((Polynomial.aeval jA N : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = Polynomial.aeval (jA : ↥K) N :=
      C1FinLevelX1.ringHom_aeval_int (ModularCurve.TwoChart.chartAlgFin A (↥K) j).val.toRingHom jA N
    have e2 : ((Polynomial.aeval v g : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = Polynomial.aeval (v : ↥K) g :=
      C1FinLevelX1.ringHom_aeval_int (ModularCurve.TwoChart.chartAlgFin A (↥K) j).val.toRingHom v g
    have hj' : (jA : ↥K) = j := rfl
    rw [MulMemClass.coe_mul, e1, e2, hj']
    have h := congrArg θ hNc
    rw [map_mul, C1FinLevelX1.ringHom_aeval_int, C1FinLevelX1.ringHom_aeval_int, hθj, hθv] at h
    exact h

  have hunit0 : IsUnit (algebraMap ℤ A (g.coeff 0)) := by
    rw [eq_intCast]
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop : IsCoprime (p : ℤ) (g.coeff 0) := (Irreducible.coprime_iff_not_dvd hpr.irreducible).mpr hndvd
    obtain ⟨a, b, hab⟩ := hcop
    by_contra hnu
    have hm : ((g.coeff 0 : ℤ) : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      have hab' := congrArg (Int.cast : ℤ → A) hab
      push_cast at hab'
      rw [← hab']
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hAp) (Ideal.mul_mem_left _ _ hm)
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal A).ne_top h1
  have hlcU : IsUnit (algebraMap ℤ A N.leadingCoeff) := by
    rw [hlcN, map_mul, map_pow]
    exact ((Units.isUnit ε).map _).mul (hunit0.pow _)

  obtain ⟨NR, hNR⟩ : ∃ NR : A[X], NR = N.map (algebraMap ℤ A) := ⟨_, rfl⟩
  have hlc' : IsUnit NR.leadingCoeff := by
    rwa [hNR, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (algebraMap ℤ A) hlcU.ne_zero]
  have hdegNR : NR.natDegree = g.natDegree * (p - 1) := by
    rw [hNR, Polynomial.natDegree_map_of_leadingCoeff_ne_zero (algebraMap ℤ A) hlcU.ne_zero, hdegN]
  have hmapN : algebraMap A[X] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) NR = Polynomial.aeval jA N := by
    rw [halgXA, hNR, Polynomial.aeval_map_algebraMap]
  have hmemI : algebraMap A[X] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) NR ∈ Ideal.span {Polynomial.aeval v g} := by
    rw [hmapN, hNA]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  refine ⟨Module.Finite.quotient_of_isUnit_leadingCoeff_of_mem A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) NR hlc' _ hmemI, ?_⟩
  calc Module.finrank A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g})
        ≤ m * NR.natDegree := C1FinLevelX1.finrank_quotient_le_mul_natDegree A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) m f hf NR hlc' _ hmemI
    _ = m * (p - 1) * g.natDegree := by rw [hdegNR]; ring

end S_ModularCurve_XOneP_exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin_twoChartModel_x1_mul (solution)
