-- Prove2me | solution 1 for MazurTransfer.original_rational_nineteenth_power_class_equality_and_exponent
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T20:04:06.470561+00:00
-- url     : https://prove2.me/submissions/715dea28-2f44-4da7-aebf-28cf033c7458

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact equality and zero criteria in the original rational nineteenth-power quotient, with its original exponent certificate. Prime-support and actual Selmer conditions are separate downstream statements.
Named downstream consumer: original rational nineteenth-power valuations and the actual selected pi Selmer radicand map.
-/
import Definitions.Def_MazurTransfer_OriginalRationalNineteenthPowerClassesData20261019
noncomputable section
open MazurTransfer RationalNineteenthPowerClasses
namespace MazurTransfer.RationalNineteenthPowerClassEqualityProofBoundary20261019
end MazurTransfer.RationalNineteenthPowerClassEqualityProofBoundary20261019
namespace MazurTransfer.OriginalRationalNineteenthPowerClassEqualityProof20261019
theorem classOf_eq_iff_power_ratio (a d : ℚˣ) :
    classOf a = classOf d ↔ ∃ b : ℚˣ, b ^ 19 = a / d :=
  QuotientGroup.eq_iff_div_mem
theorem classOf_eq_one_iff (a : ℚˣ) : classOf a = 1 ↔ ∃ b : ℚˣ, b ^ 19 = a :=
  QuotientGroup.eq_one_iff a
theorem pow_nineteen (x : PowerClasses) : x ^ 19 = 1 := by
  refine Quotient.inductionOn x ?_
  intro a
  change (QuotientGroup.mk a : PowerClasses) ^ 19 = 1
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨a, rfl⟩
end MazurTransfer.OriginalRationalNineteenthPowerClassEqualityProof20261019
theorem solution : (∀ (a d : ℚˣ), classOf a = classOf d ↔ ∃ b : ℚˣ, b ^ 19 = a / d) ∧ (∀ (a : ℚˣ), classOf a = 1 ↔ ∃ b : ℚˣ, b ^ 19 = a) ∧ (∀ (x : PowerClasses), x ^ 19 = 1) := by
  exact ⟨MazurTransfer.OriginalRationalNineteenthPowerClassEqualityProof20261019.classOf_eq_iff_power_ratio, MazurTransfer.OriginalRationalNineteenthPowerClassEqualityProof20261019.classOf_eq_one_iff, MazurTransfer.OriginalRationalNineteenthPowerClassEqualityProof20261019.pow_nineteen⟩
#print axioms solution
