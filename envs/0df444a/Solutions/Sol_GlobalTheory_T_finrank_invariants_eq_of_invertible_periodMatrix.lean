-- Prove2me | solution 1 for GlobalTheory.T.finrank_invariants_eq_of_invertible_periodMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:09:27.141797+00:00
-- url     : https://prove2.me/submissions/f8a6520d-046a-4052-94c7-0d2a1ac0c05c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankInvariantsEqOfInvertiblePeriodMatrix
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankInvariantsEqOfInvertiblePeriodMatrixStatement
import Theorems.Thm_GlobalTheory_InertiaEigenvalues_finrank_invariants_eq_of_period_matrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [Nontrivial B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n B), (∀ b : B, (∀ g, act g b = b) ↔ ∃ c : E, algebraMap E B c = b) → ∀ Q : GL n B, (∀ g, A g * (Q : Matrix n n B).map (act g) = Q) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, (A g).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n := by
  first | exact @GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix | exact GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix | (intros; apply GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix <;> assumption)
end _root_.GlobalTheory.T
