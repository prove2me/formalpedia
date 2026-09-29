-- Prove2me | solution 1 for ModularCurve.tateModule_eq_zero_of_forall_toPic0Pair_sp_eq_zero_of_ne_normFreePartAt_pinnedV3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/081f4ec4-1518-5e07-b403-8cacb080cbb7

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Definitions.Def_ModularCurve_QExpSemistableSpecializationPinnedV3
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Theorems.Thm_ModularCurve_JOne_exists_le_inertiaSubgroupIn_finiteIndex_forall_apply_eq_self_of_pow_eq_one_forall_smul_eq_self_of_torsion
import Theorems.Thm_ModularCurve_pair_normFreeEnd_eq_pair_normFreeEnd
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_isCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_x1FunctionFieldBar
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData
import Theorems.Thm_ModularCurve_normFreeEnd_normFreeEnd_eq_card_nsmul
import Theorems.Thm_ModularCurve_heckeDiamondInputsAll
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_tateModule_eq_zero_of_forall_toPic0Pair_sp_eq_zero_of_ne_normFreePartAt_pinnedV3
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace ModularCurve
p2m_export "ModularCurve" "x1FunctionFieldC x1FunctionField x1FunctionFieldBar JOne laurentBaseChange normFreeRepsAt mem_normFreeRepsAt normFreePartAt mem_normFreePartAt normFreeEnd_mem_normFreePartAt normFreeEnd QExpSemistableSpecializationPinnedV3 JOne.exists_le_inertiaSubgroupIn_finiteIndex_forall_apply_eq_self_of_pow_eq_one_forall_smul_eq_self_of_torsion pair_normFreeEnd_eq_pair_normFreeEnd isCurveOver_x1FunctionFieldBar JOneES.exists_transcendental_finiteDimensional_laurentBaseChange normFreeEnd_normFreeEnd_eq_card_nsmul heckeDiamondInputsAll"
namespace InjReduce
p2m_open "ModularCurve"

theorem tate_eq_zero_of_forall_natCast_smul_apply_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] {J : Type} [AddCommGroup J]
    (x : TateModule ℓ J) {m : ℕ} (hm : m ≠ 0) (h : ∀ n, (m : ℤ) • (x : ℕ → J) n = 0) : x = 0 := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨k, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm ℓ hℓ.ne_one
  refine Subtype.ext (funext fun n => ?_)
  show (x : ℕ → J) n = 0

  have h1 : (m' : ℤ) • (x : ℕ → J) n = 0 := by
    have hc := TateModule.compat_pow x n k
    have hn := h (n + k)
    rw [hmeq, Nat.cast_mul, mul_comm, ← smul_smul, hc] at hn
    exact hn

  have h2 : ((ℓ ^ n : ℕ) : ℤ) • (x : ℕ → J) n = 0 := TateModule.torsion x n
  have hcop : Nat.Coprime m' (ℓ ^ n) :=
    (Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hm')).symm
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hcop : IsCoprime (m' : ℤ) ((ℓ ^ n : ℕ) : ℤ))
  calc (x : ℕ → J) n = (1 : ℤ) • (x : ℕ → J) n := (one_smul ℤ _).symm
    _ = (u * (m' : ℤ) + v * ((ℓ ^ n : ℕ) : ℤ)) • (x : ℕ → J) n := by rw [huv]
    _ = u • ((m' : ℤ) • (x : ℕ → J) n) + v • (((ℓ ^ n : ℕ) : ℤ) • (x : ℕ → J) n) := by
        rw [add_smul, smul_smul, smul_smul]
    _ = 0 := by rw [h1, h2, smul_zero, smul_zero, add_zero]

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.coe_T]

theorem exists_transcendental_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    ∃ x : ↥(ModularCurve.x1FunctionFieldBar M), Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(ModularCurve.x1FunctionFieldBar M)))
        ↥(ModularCurve.x1FunctionFieldBar M) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ)
    (CongruenceSubgroup.Gamma1 M) (T_mem_Gamma1 M)

theorem card_normFreeRepsAt_ne_zero (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) :
    (ModularCurve.normFreeRepsAt M p).card ≠ 0 := by
  have hp : p.Prime := Fact.out
  have hM : 1 < M := lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM)
  exact Finset.card_ne_zero.mpr ⟨1, ModularCurve.mem_normFreeRepsAt.mpr ⟨hM, Nat.coprime_one_left M, Nat.ModEq.refl 1⟩⟩

end ModularCurve.InjReduce

open ModularCurve.InjReduce in
theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (𝒟 : ∀ I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        I ≤ P.inertiaSubgroupIn ℚ →
        (∀ σ ∈ I, ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ) →
        (I.subgroupOf (P.inertiaSubgroupIn ℚ)).FiniteIndex →
        ModularCurve.QExpSemistableSpecializationPinnedV3 (ModularCurve.x1FunctionField M) P I p
          (IsLocalRing.ResidueField P) (IsLocalRing.residue P)
          (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField P) M)
          (ModularCurve.x1FunctionField (M / p))
          (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField P) (M / p))) :

    (∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ P.inertiaSubgroupIn ℚ)
          (hIμ : ∀ σ ∈ I, ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ)
          (hIf : (I.subgroupOf (P.inertiaSubgroupIn ℚ)).FiniteIndex)
          (I' : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI' : I' ≤ P.inertiaSubgroupIn ℚ)
          (hI'μ : ∀ σ ∈ I', ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ)
          (hI'f : (I'.subgroupOf (P.inertiaSubgroupIn ℚ)).FiniteIndex),
        I' ≤ I →
        ∀ (y : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
            (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)))
          (hy : y ∈ (𝒟 I hI hIμ hIf).dom), ∃ h' : y ∈ (𝒟 I' hI' hI'μ hI'f).dom,
          AlgebraicCurve.GluedPic0.toPic0Pair _ ((𝒟 I' hI' hI'μ hI'f).sp ⟨y, h'⟩) =
            AlgebraicCurve.GluedPic0.toPic0Pair _ ((𝒟 I hI hIμ hIf).sp ⟨y, hy⟩)) →

    (∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ P.inertiaSubgroupIn ℚ)
          (hIμ : ∀ σ ∈ I, ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ)
          (hIf : (I.subgroupOf (P.inertiaSubgroupIn ℚ)).FiniteIndex),
        ∀ y ∈ ModularCurve.normFreePartAt M p, (∀ σ ∈ I, σ • y = y) → y ∈ (𝒟 I hI hIμ hIf).dom) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
      ∀ x : TateModule ℓ (ModularCurve.JOne M),
        (∀ n : ℕ, (x : ℕ → ModularCurve.JOne M) n ∈ ModularCurve.normFreePartAt M p) →
        (∀ (n : ℕ) (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
            (hI : I ≤ P.inertiaSubgroupIn ℚ)
            (hIμ : ∀ σ ∈ I, ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ)
            (hIf : (I.subgroupOf (P.inertiaSubgroupIn ℚ)).FiniteIndex)
            (h : (x : ℕ → ModularCurve.JOne M) n ∈ (𝒟 I hI hIμ hIf).dom),
            AlgebraicCurve.GluedPic0.toPic0Pair _ ((𝒟 I hI hIμ hIf).sp ⟨_, h⟩) = 0) →
        x = 0 := by
  intro hnest hdom ℓ hℓF hℓp x hxA h
  haveI := ModularCurve.isCurveOver_x1FunctionFieldBar M
  have hIn := ModularCurve.heckeDiamondInputsAll M
  have hfg := exists_transcendental_x1FunctionFieldBar M
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  refine tate_eq_zero_of_forall_natCast_smul_apply_eq_zero x (card_normFreeRepsAt_ne_zero M p hpM) (fun n => ?_)

  obtain ⟨I, hI, hIμ, hIf, hfix⟩ :=
    ModularCurve.JOne.exists_le_inertiaSubgroupIn_finiteIndex_forall_apply_eq_self_of_pow_eq_one_forall_smul_eq_self_of_torsion M p hp.pos P (ℓ ^ n) (pow_pos hℓ.pos n)
  haveI : NeZero (ℓ ^ n) := ⟨(pow_pos hℓ.pos n).ne'⟩
  have hndvd : ¬ p ∣ ℓ ^ n := fun hd => hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow hd)).symm

  obtain ⟨e⟩ := AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData (AlgebraicClosure ℚ)
    ↥(ModularCurve.x1FunctionFieldBar M) hfg (ℓ ^ n)
  have hxtor : ((ℓ ^ n : ℕ) : ℤ) • (x : ℕ → ModularCurve.JOne M) n = 0 := TateModule.torsion x n
  have hxdom : (x : ℕ → ModularCurve.JOne M) n ∈ (𝒟 I hI hIμ hIf).dom :=
    hdom I hI hIμ hIf _ (hxA n) (fun τ hτ => hfix τ hτ _ hxtor)

  have horth : ∀ (c : ModularCurve.JOne M) (hc : ((ℓ ^ n : ℕ) : ℤ) • c = 0), c ∈ ModularCurve.normFreePartAt M p →
      e.pair ⟨(x : ℕ → ModularCurve.JOne M) n, AlgebraicCurve.Pic0.mem_torsion.mpr hxtor⟩
        ⟨c, AlgebraicCurve.Pic0.mem_torsion.mpr hc⟩ = 1 := by
    intro c hc hcA
    have hcdom : c ∈ (𝒟 I hI hIμ hIf).dom := hdom I hI hIμ hIf c hcA (fun τ hτ => hfix τ hτ c hc)
    obtain ⟨d, hd1, hd2⟩ := e.exists_datum ⟨(x : ℕ → ModularCurve.JOne M) n, AlgebraicCurve.Pic0.mem_torsion.mpr hxtor⟩
      ⟨c, AlgebraicCurve.Pic0.mem_torsion.mpr hc⟩
    rw [← hd1, ← hd2, e.compatible d]
    have e1 : AlgebraicCurve.Pic0.mk d.degZeroLeft = (x : ℕ → ModularCurve.JOne M) n := congrArg Subtype.val hd1
    have e2 : AlgebraicCurve.Pic0.mk d.degZeroRight = c := congrArg Subtype.val hd2
    have m1 : AlgebraicCurve.Pic0.mk d.degZeroLeft ∈ (𝒟 I hI hIμ hIf).dom := by rw [e1]; exact hxdom
    have m2 : AlgebraicCurve.Pic0.mk d.degZeroRight ∈ (𝒟 I hI hIμ hIf).dom := by rw [e2]; exact hcdom
    refine (𝒟 I hI hIμ hIf).pairing_eq_one_of_toPic0Pair_sp_eq_zero (ℓ ^ n) (pow_pos hℓ.pos n) hndvd d
      d.degZeroLeft d.degZeroRight rfl rfl m1 m2 ?_
    have e3 : (⟨AlgebraicCurve.Pic0.mk d.degZeroLeft, m1⟩ : ↥((𝒟 I hI hIμ hIf).dom)) =
        ⟨(x : ℕ → ModularCurve.JOne M) n, hxdom⟩ := Subtype.ext e1
    rw [e3]
    exact h n I hI hIμ hIf hxdom

  have hNxtor : ((ℓ ^ n : ℕ) : ℤ) •
      ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M p) ((x : ℕ → ModularCurve.JOne M) n) = 0 := by
    rw [← map_zsmul, hxtor, map_zero]
  have hall : ∀ y : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) (ℓ ^ n),
      e.pair ⟨ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M p) ((x : ℕ → ModularCurve.JOne M) n),
        AlgebraicCurve.Pic0.mem_torsion.mpr hNxtor⟩ y = 1 := by
    rintro ⟨b, hb'⟩
    have hb : ((ℓ ^ n : ℕ) : ℤ) • b = 0 := AlgebraicCurve.Pic0.mem_torsion.mp hb'
    have hNb : ((ℓ ^ n : ℕ) : ℤ) • ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M p) b = 0 := by
      rw [← map_zsmul, hb, map_zero]
    have hA := ModularCurve.pair_normFreeEnd_eq_pair_normFreeEnd M p hpM e _ b hxtor hb hNxtor hNb
    rw [hA]
    exact horth _ hNb (ModularCurve.normFreeEnd_mem_normFreePartAt M p b)

  have hN0 : ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M p) ((x : ℕ → ModularCurve.JOne M) n) = 0 := by
    have hinj := AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_isCurveOver hfg e
    have hz : (⟨ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M p) ((x : ℕ → ModularCurve.JOne M) n),
        AlgebraicCurve.Pic0.mem_torsion.mpr hNxtor⟩ :
        ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) (ℓ ^ n))) = 0 := by
      apply hinj
      rw [map_zero]
      change Additive.ofMul (e.toChar _) = Additive.ofMul 1
      refine congrArg Additive.ofMul (DFunLike.ext _ _ fun y => ?_)
      rw [AlgebraicCurve.DivisorialWeilPairingData.toChar_apply, AddChar.one_apply]
      exact hall y
    exact congrArg Subtype.val hz

  obtain ⟨z, hz⟩ := ModularCurve.mem_normFreePartAt.mp (hxA n)
  have h2 := ModularCurve.normFreeEnd_normFreeEnd_eq_card_nsmul M p hpM hIn z
  rw [hz] at h2
  rw [natCast_zsmul, ← h2, hN0]

end S_ModularCurve_tateModule_eq_zero_of_forall_toPic0Pair_sp_eq_zero_of_ne_normFreePartAt_pinnedV3
end P2MW
export P2MW.S_ModularCurve_tateModule_eq_zero_of_forall_toPic0Pair_sp_eq_zero_of_ne_normFreePartAt_pinnedV3 (solution)
