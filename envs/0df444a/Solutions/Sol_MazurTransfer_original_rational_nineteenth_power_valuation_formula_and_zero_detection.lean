-- Prove2me | solution 1 for MazurTransfer.original_rational_nineteenth_power_valuation_formula_and_zero_detection
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T20:18:17.896715+00:00
-- url     : https://prove2.me/submissions/1722ac54-53d7-4766-8ce5-48775a708ecb

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original rational prime valuation coordinates on the genuine nineteenth-power quotient have zero common kernel. All original prime, valuation and quotient hypotheses are retained.
Named downstream consumer: the rational thirteen-support dimension theorem and original pi Selmer radicand injection.
-/
import Definitions.Def_MazurTransfer_OriginalRationalNineteenthPowerValuationCoordinateData20261019
import Theorems.Thm_MazurTransfer_original_rational_nineteenth_power_class_equality_and_exponent
import Theorems.Thm_MazurTransfer_original_nineteenth_roots_from_natural_integer_rational_prime_valuations
noncomputable section
open MazurTransfer RationalNineteenthPowerClasses RationalNineteenthPowerValuations
attribute [local instance] MazurTransfer.RationalNineteenthPowerValuations.instModuleZModOfNatNatAdditivePowerClasses_rationalNineteenthPowerValuations
namespace MazurTransfer.RationalPowerValuationZeroDetectionProofBoundary20261019
end MazurTransfer.RationalPowerValuationZeroDetectionProofBoundary20261019
namespace MazurTransfer.OriginalRationalNineteenthPowerValuationZeroDetectionProof20261019
theorem valuationLinearMap_classOf (p : ℕ) (hp : p.Prime) (a : ℚˣ) :
    valuationLinearMap p hp (Additive.ofMul (classOf a)) = ((padicValRat p (a : ℚ) : ℤ) : ZMod 19) := rfl
theorem class_eq_one_of_all_prime_values (y : PowerClasses)
    (h : ∀ (p : ℕ) (hp : p.Prime), valuationClassHom p hp y = 1) : y = 1 := by
  revert h
  refine Quotient.inductionOn y ?_
  intro a ha
  apply (MazurTransfer.original_rational_nineteenth_power_class_equality_and_exponent.2.1 a).mpr
  apply MazurTransfer.original_nineteenth_roots_from_natural_integer_rational_prime_valuations.2.2.2.2 a
  intro p hp
  have h := congrArg Multiplicative.toAdd (ha p hp)
  change ((padicValRat p (a : ℚ) : ℤ) : ZMod 19) = 0 at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
theorem zero_of_all_prime_values (x : Additive PowerClasses)
    (h : ∀ (p : ℕ) (hp : p.Prime), valuationLinearMap p hp x = 0) : x = 0 := by
  apply Additive.toMul.injective
  apply class_eq_one_of_all_prime_values x.toMul
  intro p hp
  exact congrArg Multiplicative.ofAdd (h p hp)
end MazurTransfer.OriginalRationalNineteenthPowerValuationZeroDetectionProof20261019
theorem solution : (∀ (p : ℕ) (hp : p.Prime) (a : ℚˣ), valuationLinearMap p hp (Additive.ofMul (classOf a)) = ((padicValRat p (a : ℚ) : ℤ) : ZMod 19)) ∧ (∀ (y : PowerClasses)
    (h : ∀ (p : ℕ) (hp : p.Prime), valuationClassHom p hp y = 1), y = 1) ∧ (∀ (x : Additive PowerClasses)
    (h : ∀ (p : ℕ) (hp : p.Prime), valuationLinearMap p hp x = 0), x = 0) := by
  exact ⟨MazurTransfer.OriginalRationalNineteenthPowerValuationZeroDetectionProof20261019.valuationLinearMap_classOf, MazurTransfer.OriginalRationalNineteenthPowerValuationZeroDetectionProof20261019.class_eq_one_of_all_prime_values, MazurTransfer.OriginalRationalNineteenthPowerValuationZeroDetectionProof20261019.zero_of_all_prime_values⟩
#print axioms solution
