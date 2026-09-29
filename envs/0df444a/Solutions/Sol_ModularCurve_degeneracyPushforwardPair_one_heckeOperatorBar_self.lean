-- Prove2me | solution 1 for ModularCurve.degeneracyPushforwardPair_one_heckeOperatorBar_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d5a239e6-222b-52f9-8e57-340544d92efc

import Mathlib
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_degeneracyPushforwardInputs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_degeneracyPushforwardPair_one_heckeOperatorBar_self
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X"
p2m_attr_erase "simp" "ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option Elab.async false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "degeneracyPushforwardPair degeneracyPushforwardPair_eq heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar modularFunctionFieldBar JZero modularFunctionFieldFull laurentBaseChange heckeOperatorBar heckeOperatorBar_apply heckeOperatorAlong_eq finiteAlong_heckeBetaBar_of_prime finrankAlong_heckeBetaBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional heckeInputsAll degeneracyPushforwardInputs"
p2m_open "ModularCurve"

namespace WK2Aux

section Projection

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F']

private theorem correspondence_self_eq_finrankAlong_smul (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) (D : Divisor K F) :
    Divisor.correspondence φ φ hφ hφ D = (finrankAlong K φ : ℤ) • D := by
  induction D using Finsupp.induction with
  | zero => rw [map_zero, smul_zero]
  | single_add v n D _ _ ih =>
    rw [map_add, smul_add, ih, Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum]
    congr 1
    calc ∑ W ∈ Place.fiberAlong φ hφ v,
          Divisor.pushforwardAlong φ hφ (Finsupp.single W (n * (W.ramificationIndexAlong φ : ℤ)))
        = ∑ W ∈ Place.fiberAlong φ hφ v,
            Finsupp.single v (n * ((W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong φ hφ : ℤ))) := by
          refine Finset.sum_congr rfl fun W hW => ?_
          rw [Divisor.pushforwardAlong_single, Place.mem_fiberAlong.mp hW, mul_assoc]
      _ = Finsupp.single v (n * (finrankAlong K φ : ℤ)) := by
          rw [← Finsupp.single_finsetSum, ← Finset.mul_sum,
            Place.sum_ramificationIndexAlong_mul_inertiaDegAlong φ hφ hfin hsep v]
      _ = (finrankAlong K φ : ℤ) • Finsupp.single v n := by
          rw [Finsupp.smul_single, smul_eq_mul, mul_comm]

end Projection

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem pushforwardAlong_congr {φ ψ : F →ₐ[K] F'} (h : φ = ψ) (hφ : φ.toRingHom.IsIntegral)
    (hψ : ψ.toRingHom.IsIntegral) (D : Divisor K F') :
    Divisor.pushforwardAlong φ hφ D = Divisor.pushforwardAlong ψ hψ D := by
  subst h; rfl

end Congr

section DivGrain

variable (N₀ p : ℕ) [NeZero N₀] [hp : Fact p.Prime]

local notation "LL" => AlgebraicClosure ℚ
local notation "FF" n => laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull n)

include hp in

private theorem pushforwardAlong_heckeBetaBar_heckeDivBar_self
    (hb : (heckeBetaBar LL N₀ p).toRingHom.IsIntegral) (ha : (heckeAlphaBar LL N₀ p).toRingHom.IsIntegral)
    (hβu : (heckeBetaBar LL (N₀ * p) p).toRingHom.IsIntegral)
    (hαu : (heckeAlphaBar LL (N₀ * p) p).toRingHom.IsIntegral)
    [HasPrincipalDivisors LL (FF (N₀ * p * p))] (D : Divisor LL (FF (N₀ * p))) :
    Divisor.pushforwardAlong (heckeBetaBar LL N₀ p) hb
        (Divisor.correspondence (heckeBetaBar LL (N₀ * p) p) (heckeAlphaBar LL (N₀ * p) p) hβu hαu D) =
      (p : ℤ) • Divisor.pushforwardAlong (heckeAlphaBar LL N₀ p) ha D := by
  have e1 : (heckeAlphaBar LL (N₀ * p) p).comp (heckeBetaBar LL N₀ p) =
      (heckeBetaBar LL (N₀ * p) p).comp (heckeAlphaBar LL N₀ p) := by
    apply AlgHom.ext; intro x; apply Subtype.ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_heckeAlphaBar, coe_heckeBetaBar, coe_heckeBetaBar,
      coe_heckeAlphaBar]
  rw [Divisor.correspondence_apply,
    Divisor.pushforwardAlong_pushforwardAlong _ _ hb hαu (RingHom.IsIntegral.trans _ _ hb hαu),
    pushforwardAlong_congr e1 _ (RingHom.IsIntegral.trans _ _ ha hβu),
    ← Divisor.pushforwardAlong_pushforwardAlong _ _ ha hβu (RingHom.IsIntegral.trans _ _ ha hβu),
    ← Divisor.correspondence_apply,
    correspondence_self_eq_finrankAlong_smul _ hβu (finiteAlong_heckeBetaBar_of_prime LL (N₀ * p) p)
      (separableAlong_of_charZero _ hβu),
    finrankAlong_heckeBetaBar LL (N₀ * p) p, if_pos (dvd_mul_left p N₀), map_zsmul]

end DivGrain

section Descent

variable {K F₁ F₂ E₁ : Type*} [Field K] [Field F₁] [Field F₂] [Field E₁]
  [Algebra K F₁] [Algebra K F₂] [Algebra K E₁] [HasPrincipalDivisors K E₁]

private theorem _root_.AlgebraicCurve.Pic0.mk_zsmul (n : ℤ) (D : Divisor.degZero (K := K) (F := F₁)) :
    Pic0.mk (n • D) = n • Pic0.mk D :=
  map_zsmul (QuotientAddGroup.mk' _) n D

p2m_alias "P2MW.S_ModularCurve_degeneracyPushforwardPair_one_heckeOperatorBar_self.AlgebraicCurve.Pic0.mk_zsmul" "AlgebraicCurve.Pic0.mk_zsmul"
private theorem pushforwardAlongHom_correspondence_eq_zsmul
    (φβ : F₂ →ₐ[K] F₁) (hφβ : φβ.toRingHom.IsIntegral) (hfinβ : FiniteAlong K φβ) (hNβ : NormFormulaAlong K φβ hfinβ)
    (φα : F₂ →ₐ[K] F₁) (hφα : φα.toRingHom.IsIntegral) (hfinα : FiniteAlong K φα) (hNα : NormFormulaAlong K φα hfinα)
    (βu αu : F₁ →ₐ[K] E₁) (hβu : βu.toRingHom.IsIntegral) (hαu : αu.toRingHom.IsIntegral)
    (hFIu : FundamentalIdentityAlong K βu hβu) (hfinu : FiniteAlong K αu) (hNu : NormFormulaAlong K αu hfinu)
    (n : ℤ)
    (hdiv : ∀ D : Divisor K F₁, Divisor.pushforwardAlong φβ hφβ (Divisor.correspondence βu αu hβu hαu D) =
      n • Divisor.pushforwardAlong φα hφα D)
    (c : Pic0 K F₁) :
    Pic0.pushforwardAlongHom φβ hφβ hfinβ hNβ (Pic0.correspondence βu αu hβu hαu hFIu hfinu hNu c) =
      n • Pic0.pushforwardAlongHom φα hφα hfinα hNα c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [Pic0.correspondence_mk, Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk, ← Pic0.mk_zsmul]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [Pic0.coe_pushforwardAlongDegZero, Pic0.coe_degZeroCorrespondence, AddSubgroupClass.coe_zsmul,
    Pic0.coe_pushforwardAlongDegZero]
  exact hdiv (D : Divisor K F₁)

end Descent

end WK2Aux

local instance instNeZeroPrimesWK2 (ℓ : Nat.Primes) : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩

local instance instHasPrincipalDivisorsBarWK2 (M : ℕ) [NeZero M] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M) :=
  hasPrincipalDivisors_modularFunctionFieldBar_unconditional M

private theorem degeneracyPushforwardPair_one_heckeOperatorBar_self
    (N₀ p : ℕ) [NeZero N₀] [NeZero p] (hp : p.Prime) (y : JZero (N₀ * p)) :
    degeneracyPushforwardPair N₀ p 1 (heckeOperatorBar (N₀ * p) ⟨p, hp⟩ y) =
      (p : ℤ) • degeneracyPushforwardPair N₀ p 0 y := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hαu, hβu, _, hfinu, hFIu, hNu⟩ := heckeInputsAll (N₀ * p) ⟨p, hp⟩
  obtain ⟨hαδ, hβδ, hfinαδ, hfinβδ, hNαδ, hNβδ⟩ := degeneracyPushforwardInputs N₀ p hp
  rw [heckeOperatorBar_apply, heckeOperatorAlong_eq hαu hβu hFIu hfinu hNu,
    degeneracyPushforwardPair_eq hαδ hβδ hfinαδ hNαδ hfinβδ hNβδ]
  exact WK2Aux.pushforwardAlongHom_correspondence_eq_zsmul _ hβδ hfinβδ hNβδ _ hαδ hfinαδ hNαδ _ _ hβu hαu hFIu
    hfinu hNu (p : ℤ) (fun D => WK2Aux.pushforwardAlong_heckeBetaBar_heckeDivBar_self N₀ p hβδ hαδ hβu hαu D) y

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_degeneracyPushforwardPair_one_heckeOperatorBar_self.ModularCurve in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [NeZero p] (hp : p.Prime) (y : JZero (N₀ * p)) :
    degeneracyPushforwardPair N₀ p 1 (heckeOperatorBar (N₀ * p) ⟨p, hp⟩ y) =
      (p : ℤ) • degeneracyPushforwardPair N₀ p 0 y :=
  ModularCurve.degeneracyPushforwardPair_one_heckeOperatorBar_self N₀ p hp y

end S_ModularCurve_degeneracyPushforwardPair_one_heckeOperatorBar_self
end P2MW
export P2MW.S_ModularCurve_degeneracyPushforwardPair_one_heckeOperatorBar_self (solution)
