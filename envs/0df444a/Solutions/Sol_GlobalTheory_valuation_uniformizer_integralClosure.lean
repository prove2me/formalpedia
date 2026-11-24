-- Prove2me | solution 1 for GlobalTheory.valuation_uniformizer_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:42:19.981436+00:00
-- url     : https://prove2.me/submissions/c136bf36-f9c8-4315-94ed-f63bf5294f0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationUniformizerIntegralClosureEqExpNegRamif

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra R L] [IsScalarTower R K L] [IsDedekindDomain (integralClosure R L)]
    [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L))
    (π : R) (hπ : Irreducible π) :
    P.valuation L (algebraMap K L (algebraMap R K π)) = WithZero.exp (-(P.asIdeal.ramificationIdx R : ℤ)) := by
  let v : HeightOneSpectrum R := IsDiscreteValuationRing.maximalIdeal R
  have hinj : Function.Injective (algebraMap R (integralClosure R L)) := by
    have h : Function.Injective (algebraMap R L) := by
      rw [IsScalarTower.algebraMap_eq R K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
    rw [IsScalarTower.algebraMap_eq R (integralClosure R L) L] at h
    rw [RingHom.coe_comp] at h
    exact Function.Injective.of_comp h
  have : FaithfulSMul R (integralClosure R L) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Module.IsTorsionFree R (integralClosure R L) := inferInstance
  have hlo : P.asIdeal.LiesOver v.asIdeal := by
    constructor
    have hP := P.isPrime
    have hne : P.asIdeal.under R ≠ ⊥ := Ideal.under_ne_bot R P.ne_bot
    exact ((IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne))).symm
  have h1 := HeightOneSpectrum.valuation_liesOver L v P (algebraMap R K π)
  rw [← h1, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton v hπ.ne_zero hπ.maximalIdeal_eq, ← WithZero.exp_nsmul]
  congr 1
  simp
end GlobalTheory
