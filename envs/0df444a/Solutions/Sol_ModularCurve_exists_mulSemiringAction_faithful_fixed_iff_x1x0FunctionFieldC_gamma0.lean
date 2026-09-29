-- Prove2me | solution 1 for ModularCurve.exists_mulSemiringAction_faithful_fixed_iff_x1x0FunctionFieldC_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/45cd6618-02fb-5cba-9c93-d2d2cf931ee2

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_apply_eq_one_iff_of_charZero
import Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Theorems.Thm_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0
import Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mulSemiringAction_faithful_fixed_iff_x1x0FunctionFieldC_gamma0
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open scoped MatrixGroups

namespace T3Assembly

open CongruenceSubgroup

theorem gamma1_mul_le (M p : ℕ) : Gamma1 (M * p) ≤ Gamma1 M ⊓ Gamma0 p := by
  refine le_inf (ModularCurve.Gamma1_le_of_dvd (dvd_mul_right M p)) ?_
  intro A hA
  rw [Gamma1_mem] at hA
  rw [Gamma0_mem]
  have h := congrArg (ZMod.castHom (dvd_mul_left p M) (ZMod p)) hA.2.2
  rwa [map_intCast, map_zero] at h

theorem inf_le_gamma0_mul (M p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M) :
    Gamma1 M ⊓ Gamma0 p ≤ Gamma0 (M * p) := by
  intro A hA
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hA
  rw [Gamma1_mem] at h1
  rw [Gamma0_mem] at h0 ⊢
  have hM : ((M : ℕ) : ℤ) ∣ (A 1 0 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp h1.2.2
  have hp' : ((p : ℕ) : ℤ) ∣ (A 1 0 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
  have hcop : IsCoprime (M : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM))
  have : ((M * p : ℕ) : ℤ) ∣ (A 1 0 : ℤ) := by
    push_cast
    exact hcop.mul_dvd hM hp'
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ (M * p)).mpr this

theorem core
    (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G)
      (_ : MulSemiringAction G ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH N H))),
      FaithfulSMul G ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH N H)) ∧
      (∀ (g : G) (x : ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH N H))),
        (x : LaurentSeries L) ∈ ModularCurve.qExpFunctionFieldC L (Gamma0 N) → g • x = x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH N H)),
        (∀ g : G, g • x = x) → (x : LaurentSeries L) ∈ ModularCurve.qExpFunctionFieldC L (Gamma0 N)) := by
  classical
  set E : IntermediateField L (LaurentSeries L) := ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH N H) with hE
  set E₀ : IntermediateField L (LaurentSeries L) := ModularCurve.qExpFunctionFieldC L (Gamma0 N) with hE₀
  obtain ⟨ρ, hfix, hker⟩ :=
    ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_apply_eq_one_iff_of_charZero L N H
  have hdeg : E₀.relfinrank E = (H ⊔ Subgroup.zpowers (-1 : (ZMod N)ˣ)).index :=
    ModularCurve.relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero L N H

  set H' : Subgroup (ZMod N)ˣ := H ⊔ Subgroup.zpowers (-1 : (ZMod N)ˣ) with hH'
  let G := ρ.range

  have hker' : ρ.ker = (CohCarrier.GammaH N H').subgroupOf (Gamma0 N) := by
    ext γ
    rw [MonoidHom.mem_ker, hker γ, Subgroup.mem_subgroupOf, CohCarrier.mem_GammaH_iff]
    constructor
    · intro h; exact ⟨γ.2, h⟩
    · rintro ⟨_, h⟩; exact h
  have hidx0 : (Gamma0 N).index ≠ 0 := by
    exact Subgroup.FiniteIndex.index_ne_zero
  have hrel : (CohCarrier.GammaH N H').relIndex (Gamma0 N) = H'.index := by
    have h1 := Subgroup.relIndex_mul_index (CohCarrier.GammaH_le_Gamma0 (M := N) H')
    rw [CohCarrier.index_gammaH_eq_index_gamma0_mul_index N H'] at h1

    have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx0) (h1.trans (mul_comm _ _))
    exact this
  have hcardG : Nat.card G = H'.index := by
    rw [← hrel, Subgroup.relIndex, ← hker', Subgroup.index_eq_card]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv).symm
  have hH'fin : H'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  haveI : Finite G := Nat.finite_of_card_ne_zero (hcardG ▸ hH'fin)
  letI : Fintype G := Fintype.ofFinite G

  have hfaith : FaithfulSMul G ↥E := by
    refine ⟨fun {g₁ g₂} h => ?_⟩
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    exact h x
  refine ⟨G, inferInstance, inferInstance, inferInstance, hfaith, ?_, ?_⟩
  ·
    rintro ⟨g, γ, rfl⟩ x hx
    exact hfix γ x hx
  ·
    intro x hx

    let Fix : Subfield (LaurentSeries L) := (FixedPoints.subfield G ↥E).map E.toSubfield.subtype
    have hFixle : Fix ≤ E.toSubfield := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have hE₀le : E₀.toSubfield ≤ Fix := by
      intro z hz
      have hzE : z ∈ E := ModularCurve.qExpFunctionFieldC_mono L (CohCarrier.GammaH_le_Gamma0 (M := N) H) hz
      refine Subfield.mem_map.mpr ⟨⟨z, hzE⟩, ?_, rfl⟩
      rintro ⟨_, γ, rfl⟩
      exact hfix γ ⟨z, hzE⟩ hz
    have hArtin : Fix.relfinrank E.toSubfield = Nat.card G := by
      haveI := hfaith
      have htop : (⊤ : Subfield ↥E).map E.toSubfield.subtype = E.toSubfield := by
        ext z
        constructor
        · rintro ⟨y, _, rfl⟩; exact y.2
        · intro hz; exact ⟨⟨z, hz⟩, trivial, rfl⟩
      have h1 : Fix.relfinrank E.toSubfield =
          (FixedPoints.subfield G ↥E).relfinrank (⊤ : Subfield ↥E) := by
        rw [← htop]
        exact Subfield.relfinrank_map_map (FixedPoints.subfield G ↥E) ⊤ E.toSubfield.subtype
      rw [h1, Subfield.relfinrank_top_right, FixedPoints.finrank_eq_card G ↥E, Nat.card_eq_fintype_card]
    have hdeg' : E₀.toSubfield.relfinrank E.toSubfield = H'.index := hdeg
    have hmul := Subfield.relfinrank_mul_relfinrank hE₀le hFixle
    rw [hArtin, hcardG, hdeg'] at hmul

    have hone : E₀.toSubfield.relfinrank Fix = 1 := by
      have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hH'fin) (hmul.trans (one_mul _).symm)
      exact this
    have hle : Fix ≤ E₀.toSubfield := Subfield.relfinrank_eq_one_iff.mp hone
    have hxFix : (x : LaurentSeries L) ∈ Fix := by
      refine Subfield.mem_map.mpr ⟨x, ?_, rfl⟩

      exact fun g => hx g
    exact hle hxFix

end T3Assembly

open T3Assembly in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L]
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (hle : K₂ ≤ K₁) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥K₁),
      FaithfulSMul G ↥K₁ ∧
      (∀ (g : G) (x : ↥K₁), (x : LaurentSeries L) ∈ K₂ → g • x = x) ∧
      (∀ x : ↥K₁, (∀ g : G, g • x = x) → (x : LaurentSeries L) ∈ K₂) := by
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨H, hH⟩ := CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0 (M * p)
    (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p)
    (gamma1_mul_le M p) (inf_le_gamma0_mul M p Fact.out hpM)
  have hK₁' : K₁ = ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH (M * p) H) := by
    rw [hK₁]
    unfold ModularCurve.x1x0FunctionFieldC
    rw [ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq, hH]
  have hK₂' : K₂ = ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 (M * p)) := by
    rw [hK₂, ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq]
  subst hK₁'
  subst hK₂'
  exact core L (M * p) H

end S_ModularCurve_exists_mulSemiringAction_faithful_fixed_iff_x1x0FunctionFieldC_gamma0
end P2MW
export P2MW.S_ModularCurve_exists_mulSemiringAction_faithful_fixed_iff_x1x0FunctionFieldC_gamma0 (solution)
