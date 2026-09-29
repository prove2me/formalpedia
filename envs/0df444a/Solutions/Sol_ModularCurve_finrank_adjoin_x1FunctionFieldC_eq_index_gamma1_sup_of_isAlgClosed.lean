-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_x1FunctionFieldC_eq_index_gamma1_sup_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/acf0737e-ea4b-59e4-8eb5-e00978b3dca6

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed
import Theorems.Thm_ModularCurve_finrank_adjoin_simple_le_finrank_adjoin_simple_of_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
import Theorems.Thm_ValuationSubring_isOfFinOrder_units_residueField_of_liesOverPrime
import Theorems.Thm_padicPlace_liesOverPrime
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_x1FunctionFieldC_eq_index_gamma1_sup_of_isAlgClosed
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X"
p2m_attr_erase "simp" "CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

open ModularCurve CongruenceSubgroup
open scoped MatrixGroups IntermediateField

namespace DegKE96

theorem gammaH_bot (M : ℕ) [NeZero M] :
    CohCarrier.GammaH M (⊥ : Subgroup (ZMod M)ˣ) = CongruenceSubgroup.Gamma1 M := by
  ext A
  rw [CohCarrier.mem_GammaH_iff, Gamma1_mem]
  constructor
  · rintro ⟨hA, h⟩
    rw [Subgroup.mem_bot] at h
    have hd : ((A 1 1 : ℤ) : ZMod M) = 1 := by
      have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) h
      simpa [CohCarrier.val_gamma0Units, Gamma0Map] using this
    have hc : ((A 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hA
    have hda := CohCarrier.Gamma0_d_mul_a M ⟨A, hA⟩
    simp only [hd, one_mul] at hda
    exact ⟨hda, hd, hc⟩
  · rintro ⟨ha, hd, hc⟩
    have hA : A ∈ Gamma0 M := Gamma0_mem.mpr hc
    refine ⟨hA, ?_⟩
    rw [Subgroup.mem_bot]
    ext
    simp [CohCarrier.val_gamma0Units, Gamma0Map, hd]

theorem mem_gammaH_zpowers_neg_one_iff (M : ℕ) [NeZero M] (A : SL(2, ℤ)) :
    A ∈ CohCarrier.GammaH M (Subgroup.zpowers (-1 : (ZMod M)ˣ)) ↔ A ∈ Gamma1 M ∨ -A ∈ Gamma1 M := by
  rw [CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨hA, h⟩
    have hc : ((A 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hA
    have hda := CohCarrier.Gamma0_d_mul_a M ⟨A, hA⟩
    rw [Subgroup.mem_zpowers_iff] at h
    obtain ⟨k, hk⟩ := h
    have hval : ((A 1 1 : ℤ) : ZMod M) = (((-1 : (ZMod M)ˣ) ^ k : (ZMod M)ˣ) : ZMod M) := by
      have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hk
      simpa [CohCarrier.val_gamma0Units, Gamma0Map] using this.symm
    rcases Int.even_or_odd k with hk2 | hk2
    · rw [hk2.neg_one_zpow, Units.val_one] at hval
      left
      rw [Gamma1_mem]
      simp only [hval, one_mul] at hda
      exact ⟨hda, hval, hc⟩
    · rw [hk2.neg_one_zpow, Units.val_neg, Units.val_one] at hval
      right
      rw [Gamma1_mem]
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, hval, hc, neg_zero]
      rw [hval] at hda
      refine ⟨?_, by ring, trivial⟩
      have : ((A 0 0 : ℤ) : ZMod M) = -1 := by
        have h1 : (-1 : ZMod M) * ((A 0 0 : ℤ) : ZMod M) = 1 := hda
        calc ((A 0 0 : ℤ) : ZMod M) = -((-1 : ZMod M) * ((A 0 0 : ℤ) : ZMod M)) := by ring
          _ = -1 := by rw [h1]
      rw [this]; ring
  · rintro (hA | hA)
    · rw [Gamma1_mem] at hA
      obtain ⟨ha, hd, hc⟩ := hA
      refine ⟨Gamma0_mem.mpr hc, ?_⟩
      have : CohCarrier.gamma0Units M ⟨A, Gamma0_mem.mpr hc⟩ = 1 := by
        ext; simp [CohCarrier.val_gamma0Units, Gamma0Map, hd]
      rw [this]; exact Subgroup.one_mem _
    · rw [Gamma1_mem] at hA
      obtain ⟨ha, hd, hc⟩ := hA
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero] at hc hd
      refine ⟨Gamma0_mem.mpr hc, ?_⟩
      have : CohCarrier.gamma0Units M ⟨A, Gamma0_mem.mpr hc⟩ = -1 := by
        ext; simp [CohCarrier.val_gamma0Units, Gamma0Map]
        calc ((A 1 1 : ℤ) : ZMod M) = -(-((A 1 1 : ℤ) : ZMod M)) := by ring
          _ = -1 := by rw [hd]
      rw [this]; exact Subgroup.mem_zpowers _

theorem mem_gamma1_sup_iff (M : ℕ) [NeZero M] (A : SL(2, ℤ)) :
    A ∈ Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ A ∈ Gamma1 M ∨ -A ∈ Gamma1 M := by
  constructor
  · intro h
    rw [← mem_gammaH_zpowers_neg_one_iff]
    refine (sup_le ?_ ?_ : Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ≤ _) h
    · intro B hB
      exact (mem_gammaH_zpowers_neg_one_iff M B).mpr (Or.inl hB)
    · rw [Subgroup.zpowers_le, mem_gammaH_zpowers_neg_one_iff, neg_neg]
      exact Or.inr (Subgroup.one_mem _)
  · rintro (hA | hA)
    · exact Subgroup.mem_sup_left hA
    · have : A = (-A) * (-1 : SL(2, ℤ)) := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem_sup hA (Subgroup.mem_zpowers _)

theorem gammaH_zpowers_neg_one_eq (M : ℕ) [NeZero M] :
    CohCarrier.GammaH M (Subgroup.zpowers (-1 : (ZMod M)ˣ)) = Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) := by
  ext A; rw [mem_gammaH_zpowers_neg_one_iff, mem_gamma1_sup_iff]

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  rw [Gamma1_mem]; simp [ModularGroup.T]

theorem Gamma_le_Gamma1 (M : ℕ) : CongruenceSubgroup.Gamma M ≤ Gamma1 M := by
  intro A hA
  rw [CongruenceSubgroup.Gamma_mem] at hA
  rw [Gamma1_mem]
  exact ⟨hA.1, hA.2.2.2, hA.2.2.1⟩

end DegKE96

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (t : ↥(ModularCurve.x1FunctionFieldC κ M)) (ht : (t : LaurentSeries κ) = ModularCurve.jqModC κ) :
    Module.finrank ↥(IntermediateField.adjoin κ ({t} : Set ↥(ModularCurve.x1FunctionFieldC κ M)))
        ↥(ModularCurve.x1FunctionFieldC κ M) =
      (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  classical
  have hpp := (Fact.out : p.Prime)
  apply le_antisymm
  ·
    haveI : (Gamma1 M).FiniteIndex := by
      haveI : (CongruenceSubgroup.Gamma M).FiniteIndex := inferInstance
      exact Subgroup.finiteIndex_of_le (DegKE96.Gamma_le_Gamma1 M)
    have hneg : ∀ γ ∈ Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)), γ ∈ Gamma1 M ∨ -γ ∈ Gamma1 M :=
      fun γ hγ => (DegKE96.mem_gamma1_sup_iff M γ).mp hγ
    exact (ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed κ (Gamma1 M)
      (DegKE96.T_mem_Gamma1 M) (Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) le_sup_left hneg t ht).2
  ·
    set A := padicPlace p with hAdef
    have hA : A.LiesOverPrime p := padicPlace_liesOverPrime p
    set k₀ := IsLocalRing.ResidueField ↥A with hk₀

    have hp0 : ((p : ℕ) : k₀) = 0 := by
      have h1 : IsLocalRing.residue ↥A (p : ↥A) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
        push_cast
        exact hA
      rw [map_natCast] at h1
      exact h1
    haveI : CharP k₀ p := (CharP.charP_iff_prime_eq_zero hpp).mpr hp0
    letI : Algebra (ZMod p) k₀ := ZMod.algebra k₀ p
    letI : Algebra (ZMod p) κ := ZMod.algebra κ p
    haveI : Algebra.IsAlgebraic (ZMod p) k₀ := by
      refine ⟨fun x => ?_⟩
      by_cases hx : x = 0
      · rw [hx]; exact isAlgebraic_zero
      · obtain ⟨n, hn, hxn⟩ := (ValuationSubring.isOfFinOrder_units_residueField_of_liesOverPrime p A hA
          (Units.mk0 x hx)).exists_pow_eq_one
        have hxn' : x ^ n = 1 := by
          have := congrArg (fun u : k₀ˣ => (u : k₀)) hxn
          simpa using this
        exact ⟨Polynomial.X ^ n - Polynomial.C 1, (Polynomial.monic_X_pow_sub_C (1 : ZMod p) hn.ne').ne_zero,
          by simp [hxn']⟩
    let σ : k₀ →+* κ := (IsAlgClosed.lift (R := ZMod p) (M := κ) : k₀ →ₐ[ZMod p] κ).toRingHom

    obtain ⟨ι₀, hι₀⟩ := ModularCurve.exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap σ (Gamma1 M)
    let ι : ↥(ModularCurve.x1FunctionFieldC k₀ M) →+* ↥(ModularCurve.x1FunctionFieldC κ M) := ι₀
    have hι : ∀ x : ↥(ModularCurve.x1FunctionFieldC k₀ M),
        ((ι x : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = coeffMap σ (x : LaurentSeries k₀) := hι₀

    let t₀ : ↥(ModularCurve.x1FunctionFieldC k₀ M) :=
      ⟨jqModC k₀, intFormRatiosC_subset k₀ (Gamma1 M) (ModularCurve.jqModC_mem_intFormRatiosC k₀ (Gamma1 M))⟩
    have ht₀ : ((t₀ : ↥(ModularCurve.x1FunctionFieldC k₀ M)) : LaurentSeries k₀) = jqModC k₀ := rfl
    have ht₀tr : Transcendental k₀ t₀ := by
      rw [← transcendental_algebraMap_iff (algebraMap ↥(ModularCurve.x1FunctionFieldC k₀ M) (LaurentSeries k₀)).injective]
      exact ModularCurve.transcendental_jqModC k₀
    have hιt : ι t₀ = t := by
      apply Subtype.ext
      rw [hι, ht₀, ht]
      show HahnSeries.map (jqModC k₀) σ = jqModC κ
      exact map_jqModC σ

    obtain ⟨t₁, ht₁, -, hfd, -⟩ :=
      ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
        p M hM hpM κ
    obtain rfl : t₁ = t := Subtype.ext (ht₁.trans ht.symm)
    subst hιt
    haveI := hfd

    have hig := ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField M ⊥ hpM A hA
    rw [DegKE96.gammaH_bot] at hig
    have hig' := hig t₀ ht₀
    rw [bot_sup_eq, DegKE96.gammaH_zpowers_neg_one_eq] at hig'

    have hcc := ModularCurve.finrank_adjoin_simple_le_finrank_adjoin_simple_of_coe_eq_coeffMap σ
      (ModularCurve.x1FunctionFieldC k₀ M) (ModularCurve.x1FunctionFieldC κ M) ι hι t₀ ht₀tr
    change _ ≤ Module.finrank ↥k₀⟮t₀⟯ ↥(ModularCurve.x1FunctionFieldC k₀ M) at hig'
    exact le_trans hig' hcc

end S_ModularCurve_finrank_adjoin_x1FunctionFieldC_eq_index_gamma1_sup_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_x1FunctionFieldC_eq_index_gamma1_sup_of_isAlgClosed (solution)
