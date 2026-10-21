-- Prove2me | solution 1 for MazurTransfer.original_rational_closure_prime_valuation_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T00:37:06.407062+00:00
-- url     : https://prove2.me/submissions/d63a6652-99d8-4aaa-a2b2-4f7d42985bce

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original height-one prime valuations in the ring of integers of the same embedded rational field agree with the exact original rational p-adic normalization.
Named downstream consumer: the original actual pi Selmer rational radicand prime-divisibility and thirteen-support theorem.
-/
import Definitions.Def_MazurTransfer_OriginalRationalClosurePrimeValuationData20261019
noncomputable section
open NumberField IsDedekindDomain MazurTransfer.RationalClosurePrimeValuation
attribute [local instance] MazurTransfer.RationalClosurePrimeValuation.instNumberFieldSubtypeAlgebraicClosureRatMemIntermediateFieldRationalField
attribute [local instance] MazurTransfer.RationalClosurePrimeValuation.instIsPrincipalIdealRingRingOfIntegersSubtypeAlgebraicClosureRatMemIntermediateFieldRationalField
namespace MazurTransfer.OriginalRationalClosurePrimeValuationNormalizationBoundary20261019
end MazurTransfer.OriginalRationalClosurePrimeValuationNormalizationBoundary20261019
namespace MazurTransfer.OriginalRationalClosurePrimeValuationNormalizationProof20261019
theorem intValuation_intCast (q : ℕ) [hq : Fact q.Prime] (z : ℤ) (hz : z ≠ 0) :
    (rationalPrime q).intValuation (z : 𝓞 RationalField) =
      WithZero.exp (-(padicValInt q z : ℤ)) := by
  rw [(rationalPrime q).intValuation_eq_exp_neg_multiplicity (Int.cast_ne_zero.mpr hz)]
  have hm : multiplicity (rationalPrime q).asIdeal (Ideal.span {(z : 𝓞 RationalField)}) =
      padicValInt q z := by
    calc
      _ = multiplicity (q : 𝓞 RationalField) (z : 𝓞 RationalField) :=
        multiplicity_eq_of_emultiplicity_eq Ideal.emultiplicity_eq_emultiplicity_span
      _ = multiplicity (q : ℤ) z := by
        simpa using
          (multiplicity_map_eq integerEquiv (a := (q : 𝓞 RationalField))
            (b := (z : 𝓞 RationalField))).symm
      _ = padicValInt q z := (padicValInt.of_ne_one_ne_zero hq.out.ne_one hz).symm
  rw [hm]
theorem valuation_intCast (q : ℕ) [Fact q.Prime] (z : ℤ) (hz : z ≠ 0) :
    (rationalPrime q).valuation RationalField (z : RationalField) =
      WithZero.exp (-(padicValInt q z : ℤ)) := by
  rw [show (z : RationalField) = algebraMap (𝓞 RationalField) RationalField (z : 𝓞 RationalField) by
    rw [map_intCast], HeightOneSpectrum.valuation_of_algebraMap, intValuation_intCast q z hz]
theorem valuation_ratCast (q : ℕ) [Fact q.Prime] (a : ℚ) (ha : a ≠ 0) :
    (rationalPrime q).valuation RationalField (algebraMap ℚ RationalField a) =
      WithZero.exp (-padicValRat q a) := by
  have hfrac : algebraMap ℚ RationalField a = (a.num : RationalField) / (a.den : RationalField) := by
    simpa only [map_div₀, map_intCast, map_natCast] using
      (congrArg (algebraMap ℚ RationalField) (Rat.num_div_den a)).symm
  rw [hfrac, map_div₀, valuation_intCast q a.num (Rat.num_ne_zero.mpr ha)]
  rw [show (a.den : RationalField) = ((a.den : ℤ) : RationalField) by simp,
    valuation_intCast q (a.den : ℤ) (Int.natCast_ne_zero.mpr a.den_nz),
    ← WithZero.exp_sub, padicValRat_def, padicValInt.of_nat]
  congr 1
  ring
theorem valuationOfNeZero_rationalUnits (q : ℕ) [Fact q.Prime] (a : ℚˣ) :
    Multiplicative.toAdd ((rationalPrime q).valuationOfNeZero (rationalUnits a)) =
      -padicValRat q (a : ℚ) := by
  apply WithZero.exp_inj.mp
  change ((rationalPrime q).valuationOfNeZero (rationalUnits a) : WithZero (Multiplicative ℤ)) = _
  rw [HeightOneSpectrum.valuationOfNeZero_eq]
  exact valuation_ratCast q (a : ℚ) (Units.ne_zero a)
end MazurTransfer.OriginalRationalClosurePrimeValuationNormalizationProof20261019
theorem solution : (∀ (q : ℕ) [Fact q.Prime] (z : ℤ) (hz : z ≠ 0), (rationalPrime q).intValuation (z : 𝓞 RationalField) = WithZero.exp (-(padicValInt q z : ℤ))) ∧ (∀ (q : ℕ) [Fact q.Prime] (z : ℤ) (hz : z ≠ 0), (rationalPrime q).valuation RationalField (z : RationalField) = WithZero.exp (-(padicValInt q z : ℤ))) ∧ (∀ (q : ℕ) [Fact q.Prime] (a : ℚ) (ha : a ≠ 0), (rationalPrime q).valuation RationalField (algebraMap ℚ RationalField a) = WithZero.exp (-padicValRat q a)) ∧ (∀ (q : ℕ) [Fact q.Prime] (a : ℚˣ), Multiplicative.toAdd ((rationalPrime q).valuationOfNeZero (rationalUnits a)) = -padicValRat q (a : ℚ)) := by
  exact ⟨MazurTransfer.OriginalRationalClosurePrimeValuationNormalizationProof20261019.intValuation_intCast, MazurTransfer.OriginalRationalClosurePrimeValuationNormalizationProof20261019.valuation_intCast, MazurTransfer.OriginalRationalClosurePrimeValuationNormalizationProof20261019.valuation_ratCast, MazurTransfer.OriginalRationalClosurePrimeValuationNormalizationProof20261019.valuationOfNeZero_rationalUnits⟩
#print axioms solution
