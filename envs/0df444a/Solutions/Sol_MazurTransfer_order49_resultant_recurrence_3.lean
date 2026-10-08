-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence_3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T21:13:20.612233+00:00
-- url     : https://prove2.me/submissions/3a1be4d0-117c-4e48-97dc-2ae44a2b51fb

import Theorems.Thm_MazurTransfer_order49_resultant_recurrence3_scalar_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence3_scalar_1
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence3_scalar_2
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence3_scalar_3
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.LinearCombination
open Polynomial
open MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem solution : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence3 := by
  have a4 : remainder3.coeff 4 = remainder3Coefficient4 := by
    unfold remainder3 outerTerm
    simp
  have a5 : remainder3.coeff 5 = remainder3Coefficient5 := by
    unfold remainder3 outerTerm
    simp
  have b3 : remainder4.coeff 3 = remainder4Coefficient3 := by
    unfold remainder4 outerTerm
    simp
  have b4 : remainder4.coeff 4 = remainder4Coefficient4 := by
    unfold remainder4 outerTerm
    simp
  have m0 := congrArg (Polynomial.C : Coefficient → Bivariate)
    MazurTransfer.order49_resultant_recurrence3_scalar_0
  have m1 := congrArg (Polynomial.C : Coefficient → Bivariate)
    MazurTransfer.order49_resultant_recurrence3_scalar_1
  have m2 := congrArg (Polynomial.C : Coefficient → Bivariate)
    MazurTransfer.order49_resultant_recurrence3_scalar_2
  have m3 := congrArg (Polynomial.C : Coefficient → Bivariate)
    MazurTransfer.order49_resultant_recurrence3_scalar_3
  simp only [map_mul, map_pow, map_sub, map_add] at m0 m1 m2 m3
  unfold recurrence3
  rw [b4, a5]
  unfold quotient3 linearPseudoQuotient
  rw [a4, a5, b3, b4]
  unfold remainder3 remainder4 remainder5 outerTerm
  simp only [map_mul, map_pow, map_sub]
  linear_combination m0 + m1 * X + m2 * X ^ 2 + m3 * X ^ 3
#print axioms solution
