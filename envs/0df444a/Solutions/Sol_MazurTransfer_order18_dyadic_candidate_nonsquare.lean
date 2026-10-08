-- Prove2me | solution 1 for MazurTransfer.order18_dyadic_candidate_nonsquare
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:11:15.957387+00:00
-- url     : https://prove2.me/submissions/a6f299ae-9ee1-4ef4-9883-a48d0f731e20

import Mathlib
import Definitions.Def_MazurTransfer_OrderEighteenDyadicCandidateData
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


namespace MazurTorsion.XOneEighteenDyadicCubicCertificate

/-- None of the fifteen nonidentity candidate products is a square modulo
`2⁴` in the unramified cubic residue ring.  This is a bounded kernel
calculation over `15 · 16³` possible square roots. -/
theorem candidate_nonsquare :
    ∀ i : Fin 15, ¬ IsSquare (candidate i) := by
  decide +kernel

end MazurTorsion.XOneEighteenDyadicCubicCertificate

theorem MazurTransfer.order18_dyadic_candidate_nonsquare :
    ∀ i : Fin 15,
      ¬ MazurTorsion.XOneEighteenDyadicCubicCertificate.IsSquare
        (MazurTorsion.XOneEighteenDyadicCubicCertificate.candidate i) := by
  exact MazurTorsion.XOneEighteenDyadicCubicCertificate.candidate_nonsquare

#print axioms MazurTransfer.order18_dyadic_candidate_nonsquare

theorem solution :
    ∀ i : Fin 15,
      ¬ MazurTorsion.XOneEighteenDyadicCubicCertificate.IsSquare
        (MazurTorsion.XOneEighteenDyadicCubicCertificate.candidate i) := by
  exact MazurTransfer.order18_dyadic_candidate_nonsquare

#print axioms solution
