-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThree.canonicalKummerFiber_card_field81
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:21.003594+00:00
-- url     : https://prove2.me/submissions/b77d3a4b-2bd4-4676-9476-5779616fbb43

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_ExplicitKummerThree
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_fifthPowerFiber_card_field81
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_canonicalKummer_eq_zero_iff_fifthPower_eq_target

/-! Segre factorization and eigencoordinate identities for the canonical curve in characteristic three. -/

namespace MazurProof.RationalPointsN25QuotientKummerThree

open RationalPointsN25QuotientF2

section StructuralModel

variable {K : Type*} [Field K] [CharP K 3]

end StructuralModel

section FifthPowerFibres

open scoped Pointwise

/-- The structural classifier gives the actual number of roots of the
Kummer polynomial over every 81-element field.

The proof separates the two degenerate constant fibres from the nonzero
coefficient case, where the Kummer equation is transported to `r⁵=c` and
the cyclic-group theorem applies.  No field elements are enumerated. -/
theorem _root_.solution
    {K : Type*} [Field K] [Finite K] [DecidableEq K]
    (hcard : Nat.card K = 81) (e t : K) :
    Nat.card {r : K // canonicalKummerPolynomial25Three e r t = 0} =
      canonicalKummerFiberSizeField81 e t := by
  by_cases hden : canonicalKummerDenominator25Three e t = 0
  · by_cases hnum : canonicalKummerNumerator25Three e t = 0
    · change Nat.card
          {r : K // r ^ 5 * canonicalKummerDenominator25Three e t +
            canonicalKummerNumerator25Three e t = 0} =
            (if canonicalKummerDenominator25Three e t = 0 then
              if canonicalKummerNumerator25Three e t = 0 then 81 else 0
            else
              let target := -canonicalKummerNumerator25Three e t /
                canonicalKummerDenominator25Three e t
              if target = 0 then 1 else if target ^ 16 = 1 then 5 else 0)
      simpa [hden, hnum] using hcard
    · change Nat.card
          {r : K // r ^ 5 * canonicalKummerDenominator25Three e t +
            canonicalKummerNumerator25Three e t = 0} =
            (if canonicalKummerDenominator25Three e t = 0 then
              if canonicalKummerNumerator25Three e t = 0 then 81 else 0
            else
              let target := -canonicalKummerNumerator25Three e t /
                canonicalKummerDenominator25Three e t
              if target = 0 then 1 else if target ^ 16 = 1 then 5 else 0)
      simp [hden, hnum]
  · have hequiv :
        {r : K // canonicalKummerPolynomial25Three e r t = 0} ≃
          {r : K // r ^ 5 = canonicalKummerTarget25Three e t} :=
      (Equiv.refl K).subtypeEquiv fun r =>
        canonicalKummer_eq_zero_iff_fifthPower_eq_target e t hden
    calc
      Nat.card {r : K // canonicalKummerPolynomial25Three e r t = 0} =
          Nat.card {r : K // r ^ 5 = canonicalKummerTarget25Three e t} :=
        Nat.card_congr hequiv
      _ = if canonicalKummerTarget25Three e t = 0 then 1
          else if (canonicalKummerTarget25Three e t) ^ 16 = 1 then 5 else 0 :=
        fifthPowerFiber_card_field81 hcard (canonicalKummerTarget25Three e t)
      _ = canonicalKummerFiberSizeField81 e t := by
        unfold canonicalKummerTarget25Three canonicalKummerFiberSizeField81
        rw [if_neg hden]

end FifthPowerFibres

end MazurProof.RationalPointsN25QuotientKummerThree
