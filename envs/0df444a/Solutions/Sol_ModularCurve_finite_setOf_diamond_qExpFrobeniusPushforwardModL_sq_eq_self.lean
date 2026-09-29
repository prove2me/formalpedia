-- Prove2me | solution 1 for ModularCurve.finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ad87aa04-d3ab-58f5-bd6d-653df836915c

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators
import Theorems.Thm_ModularCurve_finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL
import Theorems.Thm_ModularCurve_exists_iterate_diamond_eq_self_pic0_fbar
import Theorems.Thm_ModularCurve_qExpFrobeniusPushforwardModL_ofAlgAut_diamondActionModL_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]

    (halg : ∀ a : κ, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (F : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p z)
    (pb : (ZMod (M / p))ˣ)
    (δ : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL κ (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z) :
    {z : Pic0 κ (Fbar p M H hpM κ) | δ (F (F z)) = z}.Finite := by
  classical
  have hp : p.Prime := Fact.out
  have hpN : ¬ p ∣ M / p := by
    intro h; apply hpM2; obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [pow_two, mul_assoc, ← hk, mul_comm, Nat.div_mul_cancel hpM]⟩

  obtain ⟨m, hm, hδm⟩ := ModularCurve.exists_iterate_diamond_eq_self_pic0_fbar p M H hpM hpM2 κ pb δ hδ
  have hcomm : Function.Commute (⇑δ) (⇑F ∘ ⇑F) := by
    have h1 : ∀ z, δ (F z) = F (δ z) := by
      intro z
      rw [hF, hF, hδ, hδ]
      exact (ModularCurve.qExpFrobeniusPushforwardModL_ofAlgAut_diamondActionModL_smul κ p (M / p) hpN
        (infSubgroup p M H hpM) pb z).symm
    intro z
    show δ (F (F z)) = F (F (δ z))
    rw [h1, h1]

  have hsub : {z : Pic0 κ (Fbar p M H hpM κ) | δ (F (F z)) = z} ⊆ Function.fixedPoints (⇑F)^[2 * m] := by
    intro z hz
    have hg : (⇑δ ∘ (⇑F ∘ ⇑F))^[m] z = z := by
      have : Function.IsFixedPt (⇑δ ∘ (⇑F ∘ ⇑F)) z := hz
      exact this.iterate m
    rw [hcomm.comp_iterate] at hg
    have h2 : (⇑F ∘ ⇑F)^[m] = (⇑F)^[2 * m] := by
      rw [Function.iterate_mul]
      rfl
    show (⇑F)^[2 * m] z = z
    rw [← h2]
    have := hδm ((⇑F ∘ ⇑F)^[m] z)
    rw [Function.comp_apply] at hg
    rw [← this]
    exact hg.symm ▸ rfl
  exact (ModularCurve.finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL p M H hpM hpM2 κ halg F hF (2 * m)
    (Nat.mul_pos two_pos hm)).subset hsub

end S_ModularCurve_finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self
end P2MW
export P2MW.S_ModularCurve_finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self (solution)
