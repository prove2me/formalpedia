-- Prove2me | solution 1 for MazurTransfer.order49_first_bounded_resultant_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T21:56:21.875184+00:00
-- url     : https://prove2.me/submissions/8923ba30-7991-4947-b92d-2db526b9ceea

import Theorems.Thm_MazurTransfer_order49_generic_resultant_factorization
import Theorems.Thm_MazurTransfer_order49_resultant_factor_nonzero
import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49ResultantFactorData
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
open Polynomial
namespace MazurTorsion.PolynomialResultant
end MazurTorsion.PolynomialResultant
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.generic_resultant_eq_resultantFactorData : Polynomial.resultant MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactorData MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0 33 7 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.resultantFactorData := MazurTransfer.order49_generic_resultant_factorization
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.resultantFactorData_eval_ne_zero (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.resultantFactorData.eval d ≠ 0 := MazurTransfer.order49_resultant_factor_nonzero d hd0 hd1 hcubic


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificate. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Generic resultant certificate for order-seven backtracking

This file checks the degree and leading-coefficient side conditions
for the primitive pseudo-remainder sequence and telescopes its seven
recurrences to the factored generic resultant. The recurrence proofs
are separate exact-arithmetic certificate shards.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

open MazurTorsion.PolynomialResultant

namespace Internal.ResultantCertificate

























































































end Internal.ResultantCertificate

open Internal.ResultantCertificate



/-- Specializing the checked generic identity gives the first bounded
resultant without requiring the selection cofactor to preserve its degree. -/
theorem selection_divisionCofactor0_resultant_eq_resultantFactorData_eval
    (d : ℚ) :
    resultant (selectionCofactor d) (divisionCofactor0 d) 33 7 =
      resultantFactorData.eval d := by
  change _ = (evalRingHom d) resultantFactorData
  have hgeneric := congrArg (evalRingHom d)
    generic_resultant_eq_resultantFactorData
  simpa only [selectionCofactor, divisionCofactor0,
    resultant_map_map] using hgeneric

/-- The first bounded resultant is nonzero at every nonsingular Kubert
parameter. -/
theorem selection_divisionCofactor0_resultant_ne_zero
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    resultant (selectionCofactor d) (divisionCofactor0 d) 33 7 ≠ 0 := by
  rw [selection_divisionCofactor0_resultant_eq_resultantFactorData_eval
    d]
  exact resultantFactorData_eval_ne_zero d hd0 hd1 hcubic

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end

theorem solution (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) : Polynomial.resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selection_divisionCofactor0_resultant_ne_zero d hd0 hd1 hcubic
#print axioms solution
