-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_c2_range10
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T01:01:27.011863+00:00
-- url     : https://prove2.me/submissions/abddcc8c-10f0-4030-8379-286e169cc99b

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerTables
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData3
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open Polynomial

namespace MazurTransfer.Order49Recurrence3Standalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section























































































































































theorem recurrence4B2_coeff_160 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2.coeff 160 =
      (-35293309092693130193092614851777430488740861861679988156283197 : ℚ) := by
  unfold
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk21
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk20
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk19
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk18
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk17
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk16
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk15
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk14
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk13
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk12
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk11
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk10
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk9
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk8
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk7
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk6
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk5
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk4
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk3
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_161 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2.coeff 161 =
      (901990492351639645394371220901405226935166387424071994660786 : ℚ) := by
  unfold
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk21
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk20
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk19
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk18
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk17
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk16
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk15
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk14
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk13
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk12
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk11
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk10
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk9
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk8
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk7
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk6
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk5
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk4
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk3
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_162 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2.coeff 162 =
      (-1374558268844116244828640071139234830452149625881717600077 : ℚ) := by
  unfold
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk21
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk20
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk19
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk18
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk17
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk16
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk15
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk14
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk13
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk12
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk11
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk10
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk9
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk8
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk7
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk6
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk5
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk4
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk3
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_163 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2.coeff 163 =
      (606230329235390967552843126457705192146625266405369913 : ℚ) := by
  unfold
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk21
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk20
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk19
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk18
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk17
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk16
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk15
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk14
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk13
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk12
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk11
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk10
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk9
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk8
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk7
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk6
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk5
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk4
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk3
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_164 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2.coeff 164 =
      (-72519115701450106230107972658119229527810025982051 : ℚ) := by
  unfold
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk21
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk20
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk19
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk18
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk17
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk16
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk15
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk14
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk13
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk12
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk11
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk10
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk9
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk8
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk7
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk6
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk5
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk4
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk3
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_165 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2.coeff 165 =
      (1936443151073259926394357518664301167601012831 : ℚ) := by
  unfold
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk21
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk20
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk19
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk18
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk17
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk16
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk15
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk14
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk13
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk12
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk11
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk10
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk9
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk8
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk7
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk6
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk5
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk4
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk3
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_166 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2.coeff 166 =
      (-8483347705126631367621564019868229046546 : ℚ) := by
  unfold
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk21
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk20
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk19
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk18
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk17
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk16
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk15
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk14
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk13
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk12
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk11
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk10
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk9
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk8
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk7
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk6
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk5
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk4
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk3
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_167 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2.coeff 167 =
      (3661122349119735226781204871536038 : ℚ) := by
  unfold
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk21
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk20
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk19
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk18
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk17
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk16
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk15
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk14
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk13
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk12
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk11
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk10
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk9
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk8
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk7
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk6
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk5
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk4
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk3
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_168 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2.coeff 168 =
      (-56736521273791373632394593 : ℚ) := by
  unfold
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Block0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk21
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk20
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk19
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk18
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk17
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk16
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk15
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk14
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk13
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk12
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk11
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk10
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk9
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk8
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk7
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk6
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk5
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk4
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk3
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2Chunk0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end MazurTransfer.Order49Recurrence3Standalone

namespace MazurTransfer.Order49Recurrence3Standalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/




section

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate
namespace IntegerDenseCertificate

noncomputable section





































































































































































































































































































































































































































































































































































































































































































private theorem c2_prefix9_length :
    (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2Chunk0 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2Chunk1
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2Chunk2 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2Chunk3
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2Chunk4 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2Chunk5
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2Chunk6 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2Chunk7
       ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2Chunk8 ++ MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2Chunk9).length = 160 := by
  rfl

























private theorem c2_range10 (n : ℕ) (hlo : 160 ≤ n) (hhi : n < 169) :
    ((MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2.getD n 0 : ℤ) : ℚ) = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2.coeff n := by
  unfold MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2
  rw [List.getD_append_right _ _ _ _ (by
    rw [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c2_prefix9_length]
    omega)]
  rw [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c2_prefix9_length]
  interval_cases n <;>
    norm_num [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2Chunk10, MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence4B2_coeff_160, MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence4B2_coeff_161, MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence4B2_coeff_162, MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence4B2_coeff_163, MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence4B2_coeff_164, MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence4B2_coeff_165, MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence4B2_coeff_166, MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence4B2_coeff_167, MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence4B2_coeff_168]















































































end
end IntegerDenseCertificate
end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end MazurTransfer.Order49Recurrence3Standalone

theorem solution (n : ℕ) (hlo : 160 ≤ n) (hhi : n < 169) :
    ((MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c2.getD n 0 : ℤ) : ℚ) = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2.coeff n := by
  apply MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c2_range10 <;> assumption
#print axioms solution
