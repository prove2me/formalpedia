-- Prove2me | solution 1 for GlobalTheory.T.frobeniusSemilinearMatrix_iterate_eq_zero_of_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:01.878922+00:00
-- url     : https://prove2.me/submissions/21546ad4-6dfb-41ab-ac15-f9d76fbd1259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusSemilinearMatrixIterateEqZeroOfNilpoten
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusSemilinearMatrixIterateEqZeroOfNilpotenStatement
import Theorems.Thm_GlobalTheory_frobSemilinear_iterate_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := by
  first | exact @GlobalTheory.frobSemilinear_iterate_eq_zero | exact GlobalTheory.frobSemilinear_iterate_eq_zero | (intros; apply GlobalTheory.frobSemilinear_iterate_eq_zero <;> assumption)
end _root_.GlobalTheory.T
