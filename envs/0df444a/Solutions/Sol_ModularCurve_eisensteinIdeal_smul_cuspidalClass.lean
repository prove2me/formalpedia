-- Prove2me | solution 1 for ModularCurve.eisensteinIdeal_smul_cuspidalClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c607b235-da31-5d45-a889-d8dd043ce4d6

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_Eisenstein
import Theorems.Thm_ModularCurve_heckeOperatorBar_cuspidalClass
import Theorems.Thm_ModularCurve_heckeOperatorBar_cuspidalClass_self
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisensteinIdeal_smul_cuspidalClass
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open ModularCurve

namespace S09A1

open ModularCurve

section A1a

variable (p : ℕ) [hp : Fact p.Prime]

theorem heckeOperatorBar_cuspidalClass_eq (ℓ : Nat.Primes) :
    heckeOperatorBar p ℓ (cuspidalClass p) = eisensteinSystem p ℓ • cuspidalClass p := by
  by_cases h : (ℓ : ℕ) = p
  · have hℓ : ℓ = ⟨p, hp.out⟩ := Subtype.ext h
    subst hℓ
    rw [eisensteinSystem_of_dvd (show ((⟨p, hp.out⟩ : Nat.Primes) : ℕ) ∣ p from dvd_refl p), one_smul]
    exact heckeOperatorBar_cuspidalClass_self p
  · have hnd : ¬ (ℓ : ℕ) ∣ p := fun hd => h ((Nat.prime_dvd_prime_iff_eq ℓ.2 hp.out).mp hd)
    rw [eisensteinSystem_of_not_dvd hnd]
    exact_mod_cast heckeOperatorBar_cuspidalClass p ℓ h

theorem heckeEvalBar_cuspidalClass (h : HeckeOperatorsCommuteBar p) (t : HeckeAlg) :
    heckeEvalBar h t (cuspidalClass p) = MvPolynomial.aeval (eisensteinSystem p) t • cuspidalClass p := by
  induction t using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => rw [map_add, LinearMap.add_apply, hf, hg, map_add, add_zsmul]
  | mul_X f ℓ hf =>
      rw [map_mul, Module.End.mul_apply, show MvPolynomial.X ℓ = heckeGen ℓ from rfl, heckeEvalBar_heckeGen,
        heckeOperatorBar_cuspidalClass_eq, map_zsmul, hf, map_mul, aeval_heckeGen, smul_smul, mul_comm]

theorem eisensteinIdeal_smul_cuspidalClass :
    ∀ i ∈ eisensteinIdeal p, (letI := heckeModuleBar p; i • cuspidalClass p) = 0 := by
  intro i hi
  have h := heckeOperatorsCommuteBar p
  rw [heckeModuleBar_smul_def h, heckeEvalBar_cuspidalClass p h,
    (mem_eigenIdeal_iff _ _).mp hi, zero_zsmul]

end A1a

end S09A1

theorem solution (p : ℕ) [Fact p.Prime] : ∀ i ∈ eisensteinIdeal p, (letI := heckeModuleBar p; i • cuspidalClass p) = 0 :=
  S09A1.eisensteinIdeal_smul_cuspidalClass p

end S_ModularCurve_eisensteinIdeal_smul_cuspidalClass
end P2MW
export P2MW.S_ModularCurve_eisensteinIdeal_smul_cuspidalClass (solution)
