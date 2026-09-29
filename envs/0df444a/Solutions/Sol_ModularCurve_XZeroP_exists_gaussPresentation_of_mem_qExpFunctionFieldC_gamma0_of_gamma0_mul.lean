-- Prove2me | solution 1 for ModularCurve.XZeroP.exists_gaussPresentation_of_mem_qExpFunctionFieldC_gamma0_of_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d0b48a40-98e0-580d-b551-8aabbe1d5a8f

import Mathlib
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_XZeroP_valuationSubring_eq_or_eq_comap_and_uniformizer_and_gaussReduction_eq_gamma0_mul
import Theorems.Thm_ModularCurve_XOneGammaZeroP_exists_algEquiv_pair_map_j_eq_qExpand_and_coe_comp_eq_x1x0_gamma0
import Theorems.Thm_ModularCurve_chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XZeroP_exists_gaussPresentation_of_mem_qExpFunctionFieldC_gamma0_of_gamma0_mul
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower"
p2m_attr_erase "instance" "CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub"
p2m_attr_erase "simp" "WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLOOR0E100

open IsLocalRing

theorem exists_intermediateField_mem_iff
    {κ E : Type*} [Field κ] [Field E] [Algebra κ E]
    {R : Type*} [CommRing R] [IsLocalRing R]
    (red : R →+* E) (hker : RingHom.ker red = maximalIdeal R)
    (hconst : ∀ c : κ, ∃ r : R, red r = algebraMap κ E c) :
    ∃ R₀ : IntermediateField κ E, ∀ z : E, z ∈ R₀ ↔ ∃ r : R, red r = z := by
  classical
  let S : Subfield E :=
    { red.range with
      inv_mem' := by
        rintro _ ⟨r, rfl⟩
        by_cases hr : red r = 0
        · exact ⟨0, by rw [hr, inv_zero, map_zero]⟩
        have hu : IsUnit r := by
          by_contra h
          exact hr (by rw [← RingHom.mem_ker, hker]; exact (mem_maximalIdeal _).mpr h)
        obtain ⟨u, rfl⟩ := hu
        exact ⟨((u⁻¹ : Rˣ) : R), eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])⟩ }
  refine ⟨S.toIntermediateField (fun c => ?_), fun z => ?_⟩
  · obtain ⟨r, hr⟩ := hconst c
    exact ⟨r, hr⟩
  · show z ∈ S ↔ _
    exact ⟨fun ⟨r, hr⟩ => ⟨r, hr⟩, fun ⟨r, hr⟩ => ⟨r, hr⟩⟩

theorem red_algebraMap
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (W₀ : ValuationSubring ↥K)
    (red : ↥W₀ →+* LaurentSeries (IsLocalRing.ResidueField A))
    (hred : ∀ (f : ↥W₀) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        red f = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)))
    (a : A) (ha : algebraMap A ↥K a ∈ W₀) :
    red ⟨algebraMap A ↥K a, ha⟩ = algebraMap (IsLocalRing.ResidueField A)
      (LaurentSeries (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a) := by
  have h1 : (1 : PowerSeries A).map (IsLocalRing.residue A) ≠ 0 := by rw [map_one]; exact one_ne_zero
  have hcoe : (((algebraMap A ↥K a : ↥K)) : LaurentSeries L) = algebraMap L (LaurentSeries L) (algebraMap A L a) := by
    rw [IsScalarTower.algebraMap_apply A L ↥K a]
    exact (IsScalarTower.algebraMap_apply L ↥K (LaurentSeries L) _).symm
  have := hred ⟨algebraMap A ↥K a, ha⟩ (PowerSeries.C a) 1 h1 (by
    change (((algebraMap A ↥K a : ↥K)) : LaurentSeries L) * _ = _
    rw [hcoe, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    simp only [map_one, mul_one, PowerSeries.map_C])
  rw [this, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [map_one, div_one, PowerSeries.map_C]

theorem exists_apply_eq_iff
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (red : ↥W₀ →+* LaurentSeries (IsLocalRing.ResidueField A))
    (hred : ∀ (f : ↥W₀) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        red f = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)))
    (z : LaurentSeries (IsLocalRing.ResidueField A)) :
    (∃ w : ↥W₀, red w = z) ↔ ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ w).mp w.2
    exact ⟨w, x, y, hy, hxy, (hred w x y hy hxy).symm⟩
  · rintro ⟨f, x, y, hy, hxy, hz⟩
    have hf : f ∈ W₀ := (hW₀ f).mpr ⟨x, y, hy, hxy⟩
    exact ⟨⟨f, hf⟩, (hred ⟨f, hf⟩ x y hy hxy).trans hz⟩

theorem gamma1_inf_gamma0_le_gamma0_mul (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) :
    CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ≤ CongruenceSubgroup.Gamma0 (M * p) := by
  intro γ hγ
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hγ
  obtain ⟨-, -, h1c⟩ := (CongruenceSubgroup.Gamma1_mem M γ).mp h1
  rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 h1c ⊢
  have hcop : IsCoprime (M : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hpM))
  push_cast
  exact hcop.mul_dvd h1c h0

end FLOOR0E100

open FLOOR0E100 in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    [NeZero p]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∀ z : LaurentSeries (IsLocalRing.ResidueField A),
      z ∈ ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma0 M) →
      ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z := by
  intro z hz
  classical

  obtain ⟨W₀', hW₀', hW₀A', -, -, hnu'⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
      (CongruenceSubgroup.Gamma0 (M * p)) L K hK A j hj
  have hWW : W₀' = W₀ := by
    ext f
    rw [hW₀' f, hW₀ f]
  subst hWW

  obtain ⟨red, hred, hker⟩ :=
    ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
      L K A W₀' hW₀' hnu'

  have hconst : ∀ c : IsLocalRing.ResidueField A, ∃ r : ↥W₀', red r =
      algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    exact ⟨⟨algebraMap A ↥K a, hW₀A' a⟩, red_algebraMap L K A W₀' red hred a (hW₀A' a)⟩
  obtain ⟨R₀, hR₀⟩ := exists_intermediateField_mem_iff red hker hconst
  have hR₀' : ∀ z : LaurentSeries (IsLocalRing.ResidueField A), z ∈ R₀ ↔
      ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z :=
    fun z => (hR₀ z).trans (exists_apply_eq_iff L K A W₀' hW₀' red hred z)

  set K₁ : IntermediateField L (LaurentSeries L) :=
    ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p) with hK₁
  have hle : K ≤ K₁ := by
    rw [hK, hK₁]
    exact IntermediateField.adjoin.mono L _ _ (Set.image_mono
      (fun x hx => ModularCurve.qExpFunctionFieldC_mono ℚ (gamma1_inf_gamma0_le_gamma0_mul p M hpM) hx))
  let ι₂ : ↥K →+* ↥K₁ := (IntermediateField.inclusion hle).toRingHom
  have hι₂ : ∀ y : ↥K, (((ι₂ y : ↥K₁)) : LaurentSeries L) = ((y : ↥K) : LaurentSeries L) := fun _ => rfl
  have hj₁ : (((ι₂ j : ↥K₁)) : LaurentSeries L) = ModularCurve.coeffEmb L ModularCurve.jq := by
    rw [hι₂]; exact hj
  obtain ⟨σ, σ₂, hσ, hcompat⟩ :=
    ModularCurve.XOneGammaZeroP.exists_algEquiv_pair_map_j_eq_qExpand_and_coe_comp_eq_x1x0_gamma0
      p M hpM L K₁ hK₁ K hK ι₂ hι₂ (ι₂ j) hj₁
  have hσ₂ : ((σ₂ j : ↥K) : LaurentSeries L) =
      ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) := by
    rw [← hcompat j]; exact hσ

  obtain ⟨-, hcl⟩ :=
    ModularCurve.chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand
      p L K A hAp j hj σ₂ hσ₂
  obtain ⟨hσW, hσj'⟩ := hcl W₀' hW₀'
  obtain ⟨-, -, hiii, -⟩ :=
    ModularCurve.XZeroP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_gaussReduction_eq_gamma0_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj ϖ hϖ W₀' hW₀' σ₂ hσ₂ hσW hσj'
  have hR₀eq : R₀ = ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma0 M) :=
    hiii R₀ hR₀'
  rw [← hR₀eq] at hz
  exact (hR₀' z).mp hz

end S_ModularCurve_XZeroP_exists_gaussPresentation_of_mem_qExpFunctionFieldC_gamma0_of_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_XZeroP_exists_gaussPresentation_of_mem_qExpFunctionFieldC_gamma0_of_gamma0_mul (solution)
