-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence_6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T21:42:20.36488+00:00
-- url     : https://prove2.me/submissions/d61d5292-e610-4131-86de-cc1723db7605

import Definitions.Def_MazurTransfer_Order49ResultantRecurrence6MinimalData
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_expanded
import Mathlib.Tactic.NormNum
open Polynomial
open MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem solution : recurrence6 := by
  have hr : remainder8 = (-1 : Bivariate) := by
    norm_num [remainder8, remainder8Coefficient0, remainder8Coefficient0Block0, remainder8Coefficient0Chunk0, outerTerm, coefficientTerm]
  simpa only [recurrence6, quotient6, exceptional6, exceptionalUnit6, hr] using MazurTransfer.order49_resultant_recurrence6_expanded

#print axioms solution
