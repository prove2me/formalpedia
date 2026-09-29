-- Prove2me | solution 1 for ModularCurve.genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a1c53f75-6970-5d2a-a923-38fc4a019f46

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

import Theorems.Thm_ModularCurve_frobPushDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul
import Theorems.Thm_ModularCurve_diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul
import Theorems.Thm_ModularCurve_heckeDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open scoped TensorProduct
open ModularCurve AlgebraicCurve KaehlerDifferential

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra k K]
    (Φ : K ⊗[k] Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k] →ₗ[K]
        Ω[↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄K])
    (hinj : Function.Injective Φ)
    (hΦ : (∀ (c : K) (f g : ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))
          (f' g' : ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
          (f' : LaurentSeries K) = coeffMap (algebraMap k K) (f : LaurentSeries k) →
          (g' : LaurentSeries K) = coeffMap (algebraMap k K) (g : LaurentSeries k) →
          Φ (c ⊗ₜ[k] (f • D k ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) g)) =
            c • (f' • D K ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) g')))
    (hCk : ∃ C : Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k] →ₗ[k] Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k],
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; IsFrobPushDiff k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p C)
    (hCK : ∃ C : Ω[↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄K] →ₗ[K] Ω[↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄K],
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; IsFrobPushDiff K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p C)
    (hρk : ∃ ρ : CongruenceSubgroup.Gamma0 (M / p) →*
        (↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ≃ₐ[k] ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
      IsDiamondPullbackModL k (M / p) (infSubgroup p M H hpM) ρ)
    (hρK : ∃ ρ : CongruenceSubgroup.Gamma0 (M / p) →*
        (↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ≃ₐ[K] ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
      IsDiamondPullbackModL K (M / p) (infSubgroup p M H hpM) ρ)
    (g : CohCarrier.Gen M S) :
    (genDiffModL K p M H hpM S g) ∘ₗ Φ = Φ ∘ₗ (genDiffModL k p M H hpM S g).baseChange K := by
  have hN : NeZero (M / p) := neZero_div p M hpM
  have hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → (ℓ : K) ≠ 0 := by
    haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
    intro ℓ hℓ hne h
    rw [CharP.cast_eq_zero_iff K p ℓ] at h
    exact hne ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  cases g with
  | T ℓ hℓ hℓS hℓM =>
      rw [genDiffModL_T, genDiffModL_T]
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      have hne : ℓ ≠ p := fun h => hℓM (h ▸ hpM)
      exact ModularCurve.heckeDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul_of_prime p M hpM hpM2 H S k K Φ hinj hΦ
        hN ℓ hℓ (hprime ℓ hℓ hne)
  | U q hq hqM =>
      by_cases hqp : q = p
      · have eK : genDiffModL K p M H hpM S (.U q hq hqM) =
            (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
              frobPushDiffModL K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p) := by
          clear hprime
          subst hqp
          exact genDiffModL_U_self K q M H hpM S hq hqM
        have ek : genDiffModL k p M H hpM S (.U q hq hqM) =
            (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
              frobPushDiffModL k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p) := by
          clear hprime
          subst hqp
          exact genDiffModL_U_self k q M H hpM S hq hqM
        rw [eK, ek]
        exact ModularCurve.frobPushDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul p M hpM hpM2 H S k K Φ hinj hΦ
          hCk hCK ⟨(Fact.out : p.Prime).ne_zero⟩
      · rw [genDiffModL_U_of_ne K p M H hpM S q hq hqM hqp, genDiffModL_U_of_ne k p M H hpM S q hq hqM hqp]
        haveI : NeZero q := ⟨hq.ne_zero⟩
        exact ModularCurve.heckeDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul_of_prime p M hpM hpM2 H S k K Φ hinj hΦ
          hN q hq (hprime q hq hqp)
  | dia d =>
      rw [genDiffModL_dia, genDiffModL_dia]
      exact ModularCurve.diamondDiffModLH_comp_eq_comp_baseChange_of_forall_apply_tmul p M hpM hpM2 H S k K Φ hinj hΦ
        hρk hρK hN _

#print axioms solution

end S_ModularCurve_genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul
end P2MW
export P2MW.S_ModularCurve_genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul (solution)
