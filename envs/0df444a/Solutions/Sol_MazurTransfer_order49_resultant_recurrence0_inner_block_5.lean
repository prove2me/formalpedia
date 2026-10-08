-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence0_inner_block_5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:29:00.79299+00:00
-- url     : https://prove2.me/submissions/91c4eaeb-8e1d-40df-a584-0fb4737f01e9

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Mathlib.Tactic.Ring


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData0. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial data for the order-seven branch-zero resultant PRS

This file starts the exact primitive pseudo-remainder sequence over
`ℚ[D][X]` for the selection cofactor and the first degree-seven
division cofactor. Each generated remainder is grouped by its outer
`X` coefficient; the first quotient remains exact table data, while
the later linear quotients are forced by the leading two coefficients.
Lean recurrence certificates check the untrusted generating computation.
-/
section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

noncomputable section






theorem coefficientTerm_eq_C_mul_X_pow
    (degree : ℕ) (coefficient : ℚ) :
    coefficientTerm degree coefficient =
      C coefficient * X ^ degree := by
  exact C_mul_X_pow_eq_monomial.symm





































































































































































































































































































































































































































































































































































































































































































































































end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial resultant recurrence certificates for order-seven branch zero

This internal proof shard checks a balanced subset of the independent
coefficient identities used by the initial pseudo-remainder recurrence.
-/

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem recurrence0Inner30 :
    Internal.selectionCofactorCoefficient30 =
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient23 := by
  unfold Internal.selectionCofactorCoefficient30
    Internal.selectionCofactorCoefficient30Chunk1
    Internal.selectionCofactorCoefficient30Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient26
    quotient0Coefficient26Block0
    quotient0Coefficient26Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient25
    quotient0Coefficient25Block0
    quotient0Coefficient25Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient24
    quotient0Coefficient24Block0
    quotient0Coefficient24Chunk1
    quotient0Coefficient24Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient23
    quotient0Coefficient23Block0
    quotient0Coefficient23Chunk1
    quotient0Coefficient23Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat]
  ring
theorem recurrence0Inner31 :
    Internal.selectionCofactorCoefficient31 =
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient24 := by
  unfold Internal.selectionCofactorCoefficient31
    Internal.selectionCofactorCoefficient31Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient26
    quotient0Coefficient26Block0
    quotient0Coefficient26Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient25
    quotient0Coefficient25Block0
    quotient0Coefficient25Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient24
    quotient0Coefficient24Block0
    quotient0Coefficient24Chunk1
    quotient0Coefficient24Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat]
  ring
theorem recurrence0Inner32 :
    Internal.selectionCofactorCoefficient32 =
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient25 := by
  unfold Internal.selectionCofactorCoefficient32
    Internal.selectionCofactorCoefficient32Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient26
    quotient0Coefficient26Block0
    quotient0Coefficient26Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient25
    quotient0Coefficient25Block0
    quotient0Coefficient25Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat]
  ring
theorem recurrence0Inner33 :
    Internal.selectionCofactorCoefficient33 =
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient26 := by
  unfold Internal.selectionCofactorCoefficient33
    Internal.selectionCofactorCoefficient33Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient26
    quotient0Coefficient26Block0
    quotient0Coefficient26Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat]
  ring
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end

open Polynomial MazurTorsion.Kubert.OrderSevenBacktrackingCertificate MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem solution :
(Internal.selectionCofactorCoefficient30 =
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient23) ∧
(Internal.selectionCofactorCoefficient31 =
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient24) ∧
(Internal.selectionCofactorCoefficient32 =
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient25) ∧
(Internal.selectionCofactorCoefficient33 =
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient26) := by
  exact ⟨MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner30, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner31, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner32, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner33⟩

#print axioms solution
