-- Prove2me | solution 1 for ModularCurve.relfinrank_laurentBaseChange_gamma0_mul_x1x0FunctionFieldC_eq_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/9247fdc1-6041-5648-adee-974d8a57f8ba

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Theorems.Thm_CongruenceSubgroup_gamma1_inf_gamma0_mul_eq_gammaH_ker
import Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relfinrank_laurentBaseChange_gamma0_mul_x1x0FunctionFieldC_eq_index
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open scoped MatrixGroups

namespace DegFloor

open CongruenceSubgroup

theorem gamma0_mul_le_right (M t : ℕ) : Gamma0 (M * t) ≤ Gamma0 t := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
  exact (dvd_mul_left (t : ℤ) M).trans (by exact_mod_cast hγ)

theorem inf_le_gamma0_mul (M p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M) :
    Gamma1 M ⊓ Gamma0 p ≤ Gamma0 (M * p) := by
  intro γ hγ
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hγ
  rw [Gamma1_mem] at h1
  rw [Gamma0_mem] at h0 ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 ⊢
  have hM' : ((M : ℕ) : ℤ) ∣ _ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1.2.2
  have hcop : IsCoprime (M : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM).symm
  push_cast
  exact hcop.mul_dvd hM' h0

theorem gamma1_inf_gamma0_eq (M p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M) :
    Gamma1 M ⊓ Gamma0 p = Gamma1 M ⊓ Gamma0 (M * p) := by
  apply le_antisymm
  · exact le_inf inf_le_left (inf_le_gamma0_mul M p hp hpM)
  · exact inf_le_inf_left _ (gamma0_mul_le_right M p)

theorem ker_sup_zpowers_neg_one_eq_comap {A B : Type*} [CommGroup A] [CommGroup B] [HasDistribNeg A] [HasDistribNeg B]
    (f : A →* B) (hf : f (-1) = -1) :
    f.ker ⊔ Subgroup.zpowers (-1 : A) = (Subgroup.zpowers (-1 : B)).comap f := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      rw [Subgroup.mem_comap, (MonoidHom.mem_ker).mp hx]
      exact one_mem _
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, hf]
      exact Subgroup.mem_zpowers _
  · intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, hk⟩ := hx
    have hmem : x * (-1 : A) ^ (-k) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, hf, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
    have : x = x * (-1 : A) ^ (-k) * (-1 : A) ^ k := by
      rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    rw [this]
    exact Subgroup.mul_mem_sup hmem (Subgroup.zpow_mem_zpowers _ _)

theorem unitsMap_neg_one {n m : ℕ} (h : n ∣ m) : ZMod.unitsMap h (-1) = -1 := by
  ext
  simp [ZMod.unitsMap_def]

end DegFloor

open DegFloor in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L]
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) :
    IntermediateField.relfinrank K₂ K₁ = (Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne p)⟩

  have hK₁' : K₁ = ModularCurve.qExpFunctionFieldC L
      (CohCarrier.GammaH (M * p) (ZMod.unitsMap (dvd_mul_right M p)).ker) := by
    rw [hK₁]
    unfold ModularCurve.x1x0FunctionFieldC
    rw [ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq, gamma1_inf_gamma0_eq M p Fact.out hpM,
      CongruenceSubgroup.gamma1_inf_gamma0_mul_eq_gammaH_ker M p]
  have hK₂' : K₂ = ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 (M * p)) := by
    rw [hK₂, ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq]
  subst hK₁' hK₂'
  rw [ModularCurve.relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero L (M * p)
    (ZMod.unitsMap (dvd_mul_right M p)).ker]

  rw [ker_sup_zpowers_neg_one_eq_comap _ (unitsMap_neg_one _),
    Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective (dvd_mul_right M p))]

end S_ModularCurve_relfinrank_laurentBaseChange_gamma0_mul_x1x0FunctionFieldC_eq_index
end P2MW
export P2MW.S_ModularCurve_relfinrank_laurentBaseChange_gamma0_mul_x1x0FunctionFieldC_eq_index (solution)
