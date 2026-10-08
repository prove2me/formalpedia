-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence_1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:12:32.24598+00:00
-- url     : https://prove2.me/submissions/14599d6c-7269-45c6-a81b-1efafbc79f18

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData1
import Mathlib
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner_0
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner_1
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner_2
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner_3
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner_4
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner_5
open Polynomial
theorem MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_0 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient0 =
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7 ^ 2 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional1) *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient0 := by
  exact MazurTransfer.order49_recurrence1_inner_0
theorem MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_1 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient1 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7 ^ 2 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional1) *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient1 := by
  exact MazurTransfer.order49_recurrence1_inner_1
theorem MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_2 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient2 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7 ^ 2 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional1) *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient2 := by
  exact MazurTransfer.order49_recurrence1_inner_2
theorem MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_3 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient3 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7 ^ 2 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional1) *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient3 := by
  exact MazurTransfer.order49_recurrence1_inner_3
theorem MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_4 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient4 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7 ^ 2 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional1) *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 := by
  exact MazurTransfer.order49_recurrence1_inner_4
theorem MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_5 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient5 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7 ^ 2 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional1) *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 := by
  exact MazurTransfer.order49_recurrence1_inner_5
namespace MazurTransfer.Order49Recurrence1Standalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

noncomputable section

namespace Internal

-- In the coefficient declarations below, `X : ℚ[X]` is the parameter `D`.




























































































































































































































































































































































































































































































































































































































end Internal

















namespace Internal





end Internal









lemma divisionCofactorData0_degree :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0.natDegree ≤ 7 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0
  compute_degree















































namespace Internal






















































end Internal

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end MazurTransfer.Order49Recurrence1Standalone

namespace MazurTransfer.Order49Recurrence1Standalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

open MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private lemma coeff_mul_linearPseudoQuotient_zero
    (dividend divisor : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Bivariate)
    (dividendDegree divisorDegree : ℕ) :
    (divisor * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.linearPseudoQuotient
      dividend divisor dividendDegree divisorDegree).coeff 0 =
      divisor.coeff 0 *
        (divisor.coeff divisorDegree *
            dividend.coeff (dividendDegree - 1) -
          divisor.coeff (divisorDegree - 1) *
            dividend.coeff dividendDegree) := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.linearPseudoQuotient MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm
  rw [mul_add, coeff_add]
  simp [coeff_mul]

private lemma coeff_mul_linearPseudoQuotient_succ
    (dividend divisor : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Bivariate)
    (dividendDegree divisorDegree n : ℕ) :
    (divisor * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.linearPseudoQuotient
      dividend divisor dividendDegree divisorDegree).coeff (n + 1) =
      divisor.coeff n *
          (divisor.coeff divisorDegree *
            dividend.coeff dividendDegree) +
        divisor.coeff (n + 1) *
          (divisor.coeff divisorDegree *
              dividend.coeff (dividendDegree - 1) -
            divisor.coeff (divisorDegree - 1) *
              dividend.coeff dividendDegree) := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.linearPseudoQuotient MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm
  rw [mul_add, coeff_add]
  simp only [pow_one, pow_zero, mul_one]
  rw [← mul_assoc divisor (C _) X, coeff_mul_X, coeff_mul_C]
  rw [coeff_mul_C]

private lemma source_coeff_0 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1.coeff 0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient0 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0]

private lemma source_coeff_1 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1.coeff 1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient1 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0]

private lemma source_coeff_2 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1.coeff 2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient2 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0]

private lemma source_coeff_3 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1.coeff 3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient3 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0]

private lemma source_coeff_4 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1.coeff 4 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient4 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0]

private lemma source_coeff_5 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1.coeff 5 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient5 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0]

private lemma source_coeff_6 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1.coeff 6 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0]

private lemma source_coeff_7 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1.coeff 7 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0]

private lemma remainder2_coeff_0 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2.coeff 0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder2_coeff_1 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2.coeff 1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder2_coeff_2 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2.coeff 2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder2_coeff_3 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2.coeff 3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder2_coeff_4 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2.coeff 4 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder2_coeff_5 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2.coeff 5 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder2_coeff_6 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2.coeff 6 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder2_coeff_7 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2.coeff 7 = 0 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder3_coeff_0 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3.coeff 0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient0 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder3_coeff_1 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3.coeff 1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient1 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder3_coeff_2 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3.coeff 2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient2 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder3_coeff_3 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3.coeff 3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient3 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder3_coeff_4 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3.coeff 4 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder3_coeff_5 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3.coeff 5 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder3_coeff_6 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3.coeff 6 = 0 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder3_coeff_7 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3.coeff 7 = 0 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm]

private lemma remainder1_degree : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1.natDegree ≤ 7 := by
  simpa [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1] using MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0_degree

private lemma remainder2_degree : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2.natDegree ≤ 6 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm
  compute_degree

private lemma remainder3_degree : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3.natDegree ≤ 5 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm
  compute_degree

private lemma quotient1_degree : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1.natDegree ≤ 1 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.linearPseudoQuotient MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm
  compute_degree

theorem recurrence1_checked : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1
  apply Polynomial.ext
  intro n
  by_cases h0 : n = 0
  · subst n
    rw [coeff_C_mul, coeff_add, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1,
      MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coeff_mul_linearPseudoQuotient_zero, coeff_C_mul]
    norm_num
    rw [MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_0, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_6, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_7,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_0, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_5, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_6,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3_coeff_0]
    exact MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_0
  by_cases h1 : n = 1
  · subst n
    rw [coeff_C_mul, coeff_add, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1,
      MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coeff_mul_linearPseudoQuotient_succ MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 7 6 0, coeff_C_mul]
    norm_num
    rw [MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_1, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_6, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_7,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_1, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_5, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_6,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3_coeff_1, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_0]
    exact MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_1
  by_cases h2 : n = 2
  · subst n
    rw [coeff_C_mul, coeff_add, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1,
      MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coeff_mul_linearPseudoQuotient_succ MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 7 6 1, coeff_C_mul]
    norm_num
    rw [MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_2, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_6, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_7,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_2, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_5, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_6,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3_coeff_2, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_1]
    exact MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_2
  by_cases h3 : n = 3
  · subst n
    rw [coeff_C_mul, coeff_add, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1,
      MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coeff_mul_linearPseudoQuotient_succ MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 7 6 2, coeff_C_mul]
    norm_num
    rw [MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_3, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_6, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_7,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_3, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_5, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_6,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3_coeff_3, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_2]
    exact MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_3
  by_cases h4 : n = 4
  · subst n
    rw [coeff_C_mul, coeff_add, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1,
      MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coeff_mul_linearPseudoQuotient_succ MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 7 6 3, coeff_C_mul]
    norm_num
    rw [MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_4, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_6, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_7,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_4, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_5, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_6,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3_coeff_4, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_3]
    exact MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_4
  by_cases h5 : n = 5
  · subst n
    rw [coeff_C_mul, coeff_add, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1,
      MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coeff_mul_linearPseudoQuotient_succ MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 7 6 4, coeff_C_mul]
    norm_num
    rw [MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_5, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_6, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_7,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_5, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_6, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3_coeff_5,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_4]
    exact MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_5
  by_cases h6 : n = 6
  · subst n
    rw [coeff_C_mul, coeff_add, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1,
      MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coeff_mul_linearPseudoQuotient_succ MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 7 6 5, coeff_C_mul]
    norm_num
    rw [MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_6, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_7, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_6,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_5, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3_coeff_6]
    ring
  by_cases h7 : n = 7
  · subst n
    rw [coeff_C_mul, coeff_add, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1,
      MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coeff_mul_linearPseudoQuotient_succ MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 7 6 6, coeff_C_mul]
    norm_num
    rw [MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_7, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.source_coeff_6, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_7,
    MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_5, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coeff_6, MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3_coeff_7]
    ring
  have hn : 7 < n := by omega
  have hsource : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder1_degree.trans_lt hn)
  have hremainder3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3_degree.trans_lt (by omega))
  have hproductDegree :
      (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1).natDegree ≤ 7 := by
    exact natDegree_mul_le.trans (by
      have h2 := MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_degree
      have hq := MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1_degree
      omega)
  have hproduct : (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient1).coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (hproductDegree.trans_lt hn)
  rw [coeff_C_mul, coeff_add, coeff_C_mul, hsource,
    hremainder3, hproduct]
  ring
end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1Standalone

theorem solution : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1 := by
  exact MazurTransfer.Order49Recurrence1Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_checked
#print axioms solution
