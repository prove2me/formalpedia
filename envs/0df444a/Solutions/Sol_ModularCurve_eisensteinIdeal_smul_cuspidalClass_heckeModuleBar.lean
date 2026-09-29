-- Prove2me | solution 1 for ModularCurve.eisensteinIdeal_smul_cuspidalClass_heckeModuleBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/ab8a03c0-b0c1-5d04-b2ea-846f4dc2cb78

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_ModularCurve_heckeInputsAlong_of_prime
import Theorems.Thm_ModularCurve_heckeDivBar_cuspidalDivisor_of_prime
import Theorems.Thm_ModularCurve_heckeDivBar_cuspidalDivisor_self_of_prime
import Theorems.Thm_ModularCurve_heckePic0Bar_cuspidalClass
import Theorems.Thm_ModularCurve_heckePic0Bar_cuspidalClass_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisensteinIdeal_smul_cuspidalClass_heckeModuleBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
open ModularCurve AlgebraicCurve

private theorem heckeOperatorBar_cuspidalClass_eisensteinSystem (p : ℕ) [Fact p.Prime]
    (ℓ : Nat.Primes) :
    heckeOperatorBar p ℓ (cuspidalClass p) = eisensteinSystem p ℓ • cuspidalClass p := by
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  by_cases hdvd : (ℓ : ℕ) ∣ p
  · have hep : ℓ = ⟨p, Fact.out⟩ :=
      Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 Fact.out).mp hdvd)
    subst hep
    rw [eisensteinSystem_of_dvd hdvd, one_smul]
    obtain ⟨hα, hβ, hP, hfin, hFI, hN⟩ :=
      heckeInputsAlong_of_prime (AlgebraicClosure ℚ) p p
    haveI := hP
    have hcast : heckeOperatorBar p ⟨p, Fact.out⟩ (cuspidalClass p)
        = heckeOperatorAlong (AlgebraicClosure ℚ) p p (cuspidalClass p) := rfl
    rw [hcast, heckeOperatorAlong_eq hα hβ hFI hfin hN]
    exact heckePic0Bar_cuspidalClass_self p hα hβ hFI hfin hN
      (heckeDivBar_cuspidalDivisor_self_of_prime p hα hβ)
  · have hlp : p ≠ (ℓ : ℕ) :=
      fun h => hdvd ((Nat.prime_dvd_prime_iff_eq ℓ.2 Fact.out).mpr h.symm)
    rw [eisensteinSystem_of_not_dvd hdvd]
    obtain ⟨hα, hβ, hP, hfin, hFI, hN⟩ :=
      heckeInputsAlong_of_prime (AlgebraicClosure ℚ) p (ℓ : ℕ)
    haveI := hP
    have hcast : heckeOperatorBar p ℓ (cuspidalClass p)
        = heckeOperatorAlong (AlgebraicClosure ℚ) p (ℓ : ℕ) (cuspidalClass p) := rfl
    rw [hcast, heckeOperatorAlong_eq hα hβ hFI hfin hN]
    exact heckePic0Bar_cuspidalClass p (ℓ : ℕ) hα hβ hFI hfin hN
      (heckeDivBar_cuspidalDivisor_of_prime p (ℓ : ℕ) hlp hα hβ)

private theorem heckeEvalBar_cuspidalClass_aeval (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p) (t : HeckeAlg) :
    heckeEvalBar hcomm t (cuspidalClass p)
      = MvPolynomial.aeval (eisensteinSystem p) t • cuspidalClass p := by
  induction t using MvPolynomial.induction_on with
  | C a =>
      rw [heckeEvalBar_C, Module.End.intCast_apply, MvPolynomial.aeval_C, eq_intCast,
        Int.cast_id]
  | add s r hs hr =>
      rw [map_add, LinearMap.add_apply, hs, hr, map_add, add_zsmul]
  | mul_X s ℓ ih =>
      have hX : heckeEvalBar hcomm (MvPolynomial.X ℓ) = heckeOperatorBar p ℓ :=
        heckeEvalBar_heckeGen hcomm ℓ
      rw [map_mul, Module.End.mul_apply, hX,
        heckeOperatorBar_cuspidalClass_eisensteinSystem p ℓ, map_zsmul, ih, smul_smul,
        map_mul, MvPolynomial.aeval_X, mul_comm]

theorem solution (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p) :
    letI := heckeModuleBar p
    ∀ t ∈ eisensteinIdeal p, t • cuspidalClass p = 0 := by
  refine fun t ht => ?_
  have ht0 : MvPolynomial.aeval (eisensteinSystem p) t = (0 : ℤ) :=
    (mem_eigenIdeal_iff (eisensteinSystem p) t).mp ht
  refine (heckeModuleBar_smul_def hcomm t (cuspidalClass p)).trans ?_
  rw [heckeEvalBar_cuspidalClass_aeval p hcomm t, ht0, zero_zsmul]

end S_ModularCurve_eisensteinIdeal_smul_cuspidalClass_heckeModuleBar
end P2MW
export P2MW.S_ModularCurve_eisensteinIdeal_smul_cuspidalClass_heckeModuleBar (solution)
