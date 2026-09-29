-- Prove2me | solution 1 for ModularCurve.relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0c99b1af-5211-58aa-846f-bfa96375f2c6

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_index_le_relfinrank_qExpFunctionFieldC_gamma0_gammaH_of_charZero
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_card_quotient_gamma0_eq_index
import Theorems.Thm_ModularCurve_card_quotient_gamma0_le_dedekindPsi
import Theorems.Thm_ModularCurve_le_dedekindPsi
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open scoped MatrixGroups

namespace T3DegAssembly

open CongruenceSubgroup

variable {M : ℕ}

theorem gamma1_le_gammaH [NeZero M] (H : Subgroup (ZMod M)ˣ) : Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [Gamma1_mem] at hA
  have hA0 : A ∈ Gamma0 M := Gamma0_mem.mpr hA.2.2
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact hA.2.1
  rw [this]
  exact one_mem _

theorem T_mem_gammaH [NeZero M] (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  apply gamma1_le_gammaH
  rw [Gamma1_mem]
  simp [ModularGroup.coe_T]

theorem gammaH_le_gammaH_sup [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) := by
  intro A hA
  obtain ⟨hA0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hA
  exact CohCarrier.mem_GammaH_iff.mpr ⟨hA0, Subgroup.mem_sup_left hH⟩

theorem neg_mem_gamma0 {A : SL(2, ℤ)} (hA : A ∈ Gamma0 M) : -A ∈ Gamma0 M := by
  rw [Gamma0_mem] at hA ⊢
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, hA, neg_zero]

theorem gamma0Units_neg [NeZero M] {A : SL(2, ℤ)} (hA : A ∈ Gamma0 M) :
    CohCarrier.gamma0Units M ⟨-A, neg_mem_gamma0 hA⟩ = -CohCarrier.gamma0Units M ⟨A, hA⟩ := by
  ext
  rw [CohCarrier.val_gamma0Units, Units.val_neg, CohCarrier.val_gamma0Units]
  show (((-A : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = -(((A : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]

theorem mem_or_neg_mem [NeZero M] (H : Subgroup (ZMod M)ˣ) {A : SL(2, ℤ)}
    (hA : A ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ))) :
    A ∈ CohCarrier.GammaH M H ∨ -A ∈ CohCarrier.GammaH M H := by
  obtain ⟨hA0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hA

  rw [Subgroup.mem_sup] at hH
  obtain ⟨h, hh, u, hu, hhu⟩ := hH
  rw [Subgroup.mem_zpowers_iff] at hu
  obtain ⟨k, rfl⟩ := hu

  have h2 : (-1 : (ZMod M)ˣ) ^ (2 : ℤ) = 1 := by
    rw [zpow_two]; simp
  rcases Int.even_or_odd k with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · left
    refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
    have : (-1 : (ZMod M)ˣ) ^ (l + l) = 1 := by rw [← two_mul, zpow_mul, h2, one_zpow]
    rw [this, mul_one] at hhu
    rwa [← hhu]
  · right
    refine CohCarrier.mem_GammaH_iff.mpr ⟨neg_mem_gamma0 hA0, ?_⟩
    have : (-1 : (ZMod M)ˣ) ^ (2 * l + 1) = -1 := by
      rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
    rw [this] at hhu
    rw [gamma0Units_neg hA0, ← hhu, mul_neg_one, neg_neg]
    exact hh

theorem relfinrank_adjoin_jq_eq_finrank (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ))
    (y : ModularCurve.qExpFunctionFieldC K Γ) (hy : (y : LaurentSeries K) = ModularCurve.jqModC K) :
    (IntermediateField.adjoin K {ModularCurve.jqModC K}).relfinrank (ModularCurve.qExpFunctionFieldC K Γ) =
      Module.finrank (IntermediateField.adjoin K ({y} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ) := by
  have h1 : IntermediateField.adjoin K {ModularCurve.jqModC K} =
      IntermediateField.lift (IntermediateField.adjoin K ({y} : Set (ModularCurve.qExpFunctionFieldC K Γ))) := by
    rw [IntermediateField.lift_adjoin_simple, hy]
  have h3 : IntermediateField.lift (⊤ : IntermediateField K (ModularCurve.qExpFunctionFieldC K Γ)) =
      ModularCurve.qExpFunctionFieldC K Γ := IntermediateField.lift_top K _
  calc (IntermediateField.adjoin K {ModularCurve.jqModC K}).relfinrank (ModularCurve.qExpFunctionFieldC K Γ)
      = (IntermediateField.lift (IntermediateField.adjoin K ({y} : Set (ModularCurve.qExpFunctionFieldC K Γ)))).relfinrank
          (ModularCurve.qExpFunctionFieldC K Γ) := by rw [h1]
    _ = (IntermediateField.lift (IntermediateField.adjoin K ({y} : Set (ModularCurve.qExpFunctionFieldC K Γ)))).relfinrank
          (IntermediateField.lift (⊤ : IntermediateField K (ModularCurve.qExpFunctionFieldC K Γ))) :=
        congrArg _ h3.symm
    _ = (IntermediateField.adjoin K ({y} : Set (ModularCurve.qExpFunctionFieldC K Γ))).relfinrank ⊤ :=
        IntermediateField.relfinrank_map_map _ _ (ModularCurve.qExpFunctionFieldC K Γ).val
    _ = _ := IntermediateField.relfinrank_top_right _

theorem index_gamma0_le_dedekindPsi (N : ℕ) [NeZero N] : (Gamma0 N).index ≤ ModularCurve.dedekindPsi N := by
  rw [← ModularCurve.card_quotient_gamma0_eq_index N]
  exact ModularCurve.card_quotient_gamma0_le_dedekindPsi N

end T3DegAssembly

open T3DegAssembly in
theorem solution
    (K : Type*) [Field K] [CharZero K] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)).relfinrank
        (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) =
      (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := by
  classical
  set F₀ := ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) with hF₀
  set FH := ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) with hFH
  set H' := H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ) with hH'
  apply le_antisymm _ (ModularCurve.index_le_relfinrank_qExpFunctionFieldC_gamma0_gammaH_of_charZero K M H)

  set J : IntermediateField K (LaurentSeries K) := IntermediateField.adjoin K {ModularCurve.jqModC K} with hJ
  have hjF₀ : ModularCurve.jqModC K ∈ F₀ :=
    ModularCurve.intFormRatiosC_subset K _ (ModularCurve.jqModC_mem_intFormRatiosC K _)
  have hjFH : ModularCurve.jqModC K ∈ FH :=
    ModularCurve.intFormRatiosC_subset K _ (ModularCurve.jqModC_mem_intFormRatiosC K _)
  have hJ₀ : J ≤ F₀ := IntermediateField.adjoin_simple_le_iff.mpr hjF₀
  have h₀H : F₀ ≤ FH := ModularCurve.qExpFunctionFieldC_mono K (CohCarrier.GammaH_le_Gamma0 (M := M) H)

  haveI : (CohCarrier.GammaH M H).FiniteIndex := by
    refine ⟨?_⟩
    rw [CohCarrier.index_gammaH_eq_index_gamma0_mul_index M H]
    exact Nat.mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.index_ne_zero_of_finite

  obtain ⟨hfinH, hubH⟩ := ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
    (CohCarrier.GammaH M H) (T_mem_gammaH H) (CohCarrier.GammaH M H') (gammaH_le_gammaH_sup H)
    (fun γ hγ => mem_or_neg_mem H hγ) ⟨ModularCurve.jqModC K, hjFH⟩ rfl

  obtain ⟨hfin0, -⟩ := ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
    (CongruenceSubgroup.Gamma0 M) (by rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.coe_T]) (CongruenceSubgroup.Gamma0 M) le_rfl
    (fun γ hγ => Or.inl hγ) ⟨ModularCurve.jqModC K, hjF₀⟩ rfl
  haveI := hfin0
  have hlb0 : ModularCurve.dedekindPsi M ≤
      Module.finrank (IntermediateField.adjoin K ({(⟨ModularCurve.jqModC K, hjF₀⟩ : F₀)} : Set F₀)) F₀ :=
    ModularCurve.dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0 K M (by exact_mod_cast (NeZero.ne M))
      ⟨ModularCurve.jqModC K, hjF₀⟩ rfl

  have hrelH : J.relfinrank FH = Module.finrank (IntermediateField.adjoin K ({(⟨ModularCurve.jqModC K, hjFH⟩ : FH)} : Set FH)) FH :=
    relfinrank_adjoin_jq_eq_finrank K _ _ rfl
  have hrel0 : J.relfinrank F₀ = Module.finrank (IntermediateField.adjoin K ({(⟨ModularCurve.jqModC K, hjF₀⟩ : F₀)} : Set F₀)) F₀ :=
    relfinrank_adjoin_jq_eq_finrank K _ _ rfl
  have htower := IntermediateField.relfinrank_mul_relfinrank hJ₀ h₀H

  have hidx : (CohCarrier.GammaH M H').index = (CongruenceSubgroup.Gamma0 M).index * H'.index :=
    CohCarrier.index_gammaH_eq_index_gamma0_mul_index M H'
  have hpsi : 0 < ModularCurve.dedekindPsi M :=
    lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne M)) (ModularCurve.le_dedekindPsi M (NeZero.ne M))

  have key : ModularCurve.dedekindPsi M * F₀.relfinrank FH ≤ ModularCurve.dedekindPsi M * H'.index := by
    calc ModularCurve.dedekindPsi M * F₀.relfinrank FH
        ≤ J.relfinrank F₀ * F₀.relfinrank FH := Nat.mul_le_mul_right _ (hrel0 ▸ hlb0)
      _ = J.relfinrank FH := htower
      _ ≤ (CohCarrier.GammaH M H').index := hrelH ▸ hubH
      _ = (CongruenceSubgroup.Gamma0 M).index * H'.index := hidx
      _ ≤ ModularCurve.dedekindPsi M * H'.index := Nat.mul_le_mul_right _ (index_gamma0_le_dedekindPsi M)
  exact Nat.le_of_mul_le_mul_left key hpsi

end S_ModularCurve_relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
end P2MW
export P2MW.S_ModularCurve_relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero (solution)
