-- Prove2me | solution 1 for HorizontalPadicL.SeededHorizontalPadicLFunctionV4.primePower_propagation_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:58:21.114599+00:00
-- url     : https://prove2.me/submissions/06cb1ee8-01c9-485a-9fdd-79b601ee48e3

import Definitions.Def_KN_InverseSeedConventionV2
import Theorems.Thm_HorizontalPadicL_HorizontalMeasure_boundedExponent_finiteCorrection_v2
import Theorems.Thm_HorizontalPadicL_SeededHorizontalPrimeSystemV3_orderExponent_le_exponent_v2
import Theorems.Thm_HorizontalPadicL_supportedPrimePowerCharacters_logLowerBound_v2
import Theorems.Thm_HorizontalPadicL_primitiveCharacters_boundedConductor_finite_v2
import Theorems.Thm_HorizontalPadicL_CharacterCountingTransfer_logLowerBound_v2
import Theorems.Thm_HorizontalPadicL_finiteCorrection_realization_countingTransfer_inverseSeed_v2

set_option autoImplicit false
noncomputable section
open HorizontalPadicL

-- Prove2Me requires this declaration at the root namespace.
theorem solution
    {N k B p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (ν : SeededHorizontalPadicLFunctionV4 (B := B) p ιp f η)
    (hpodd : p ≠ 2) (m : ℕ) (hm : 0 < m)
    (hexponent : ν.primes.orderExponent = m)
    (hinterp : ν.InterpolatesSeededCriticalValuesV4)
    (htriv : ν.measure.eval
      (trivialHorizontalCharacterV2 p ν.primes.exponent) ≠ 0) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound
        (seededPrimePowerNonvanishingCount ι f η p m B) α := by
  obtain ⟨A, hcorr⟩ := HorizontalMeasure.boundedExponent_finiteCorrection_v2
    ν.measure ν.coefficient_integral m hm
    (fun n => hexponent ▸ ν.primes.orderExponent_le_exponent_v2 n) htriv
  obtain ⟨R, hR, hvalues⟩ := hinterp
  obtain ⟨F⟩ := finiteCorrection_realization_countingTransfer_inverseSeed_v2
    ν.primes.toConstructionData R hR ν.measure hpodd m hm hvalues A hcorr
  obtain ⟨α, hα, _hαlt, hcount⟩ := supportedPrimePowerCharacters_logLowerBound_v2
    p m hm ν.primes.primeAt ν.primes.primeAt_prime ν.primes.primeAt_injective
    (fun n => hexponent ▸ (ν.primes.primeAt_orderly n).2.1)
    ν.primes.naturalDensity ν.primes.naturalDensity_pos
    ν.primes.has_naturalDensity A
  refine ⟨α, hα, F.logLowerBound_v2 ?_ ?_ α hα hcount⟩
  · intro X
    exact (primitiveCharacters_boundedConductor_finite_v2 X).subset
      (fun χ hχ => ⟨hχ.1.1, hχ.2⟩)
  · intro X
    exact (primitiveCharacters_boundedConductor_finite_v2 X).subset
      (fun χ hχ => ⟨hχ.1.1, hχ.2⟩)
