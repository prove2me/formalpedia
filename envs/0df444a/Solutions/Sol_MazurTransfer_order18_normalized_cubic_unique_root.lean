-- Prove2me | solution 1 for MazurTransfer.order18_normalized_cubic_unique_root
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:38:00.346904+00:00
-- url     : https://prove2.me/submissions/364b0690-690e-4bcf-b1e1-323d0fb9d414

import Mathlib
import Definitions.Def_MazurTransfer_OrderEighteenNormalizedCubicData


/- Source module: MazurTorsion.NumberTheory.XOneEighteenDyadicGeneratorRingCertificate. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Ring realization of the dyadic generator certificate

The finite certificate in `XOneEighteenDyadicCubicCertificate` uses triples
with a custom multiplication.  This file identifies those triples with the
power basis of

`(ZMod 16)[T] / (T³ - 3T - 1)`

and transfers its nonsquare result to the ordinary ring-theoretic
`IsSquare` predicate.
-/

open Polynomial Module

namespace MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate

noncomputable section































/-! ## The bounded normalized-relative-cubic certificate -/



private theorem normalizedRelativeCubicValue_eq_zero_iff_coordinates :
    ∀ a b c : R,
      normalizedRelativeCubicValue ![a, b, c] = 0 ↔
        ![a, b, c] =
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator := by
  decide +kernel +revert

/-- The normalized relative cubic has exactly one root among the `16³`
coefficient vectors.  This is the complete bounded enumeration used by the
integral reduction bridge.  The three coordinates are enumerated separately
so that the kernel proof term does not traverse a `4096`-element function
enumeration at once. -/
theorem normalizedRelativeCubicValue_eq_zero_iff :
    ∀ z : Fin 3 → R,
      normalizedRelativeCubicValue z = 0 ↔
        z = XOneEighteenDyadicGeneratorCertificate.normalizedGenerator := by
  intro z
  have hz : ![z 0, z 1, z 2] = z := by
    funext i
    fin_cases i <;> rfl
  rw [← hz]
  exact normalizedRelativeCubicValue_eq_zero_iff_coordinates
    (z 0) (z 1) (z 2)



















/-! ## Exact evaluations of the four generator polynomials -/

























end

end MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate

end

theorem solution :
    ∀ z : Fin 3 → ZMod 16,
      MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate.normalizedRelativeCubicValue z = 0 ↔
        z = MazurTorsion.XOneEighteenDyadicGeneratorCertificate.normalizedGenerator := by
  exact MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate.normalizedRelativeCubicValue_eq_zero_iff

#print axioms solution
