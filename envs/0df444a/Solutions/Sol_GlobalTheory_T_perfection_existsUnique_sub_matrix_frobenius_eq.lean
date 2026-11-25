-- Prove2me | solution 1 for GlobalTheory.T.perfection_existsUnique_sub_matrix_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:39.352932+00:00
-- url     : https://prove2.me/submissions/4b7ac28b-bb4a-4692-b77f-461edb9c7bd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PerfectionExistsUniqueSubMatrixFrobeniusEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PerfectionExistsUniqueSubMatrixFrobeniusEqStatement
import Theorems.Thm_GlobalTheory_perfection_frobenius_solve


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
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] (Q : Matrix ι ι (Perfection S p)), (∀ n : ℕ, ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k))^[K] z = 0) → ∀ c : ι → Perfection S p, ∃! x : ι → Perfection S p, x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k)) = c := by
  first | exact @GlobalTheory.perfection_frobenius_solve | exact GlobalTheory.perfection_frobenius_solve | (intros; apply GlobalTheory.perfection_frobenius_solve <;> assumption)
end _root_.GlobalTheory.T
