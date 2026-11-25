-- Prove2me | solution 1 for GlobalTheory.T.exists_weightedHomogeneous_homogenisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:19:14.28694+00:00
-- url     : https://prove2.me/submissions/ffc946c7-9836-47b9-ba04-bc95a48c049e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsWeightedHomogenisation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsWeightedHomogenisationStatement
import Theorems.Thm_GlobalTheory_exists_weightedHomogenisation


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
theorem _root_.solution : ∀ {L : Type} [Field L] (Q : Subring L) (r : ℕ) (z : Fin (r + 1) → Q)
    (wt : Fin (r + 1) → ℕ), wt 0 = 1 → (z 0 : L) ≠ 0 → ∀ P : MvPolynomial (Fin r) Q,
    ∃ (N : ℕ) (F : MvPolynomial (Fin (r + 1)) Q), F.IsWeightedHomogeneous wt N ∧
      ((MvPolynomial.eval z F : Q) : L) = (z 0 : L) ^ N *
        MvPolynomial.eval₂ Q.subtype (fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ) P ∧
      ∀ α, ∃ β, F.coeff β = P.coeff α := by
  first | exact @GlobalTheory.exists_weightedHomogenisation | exact GlobalTheory.exists_weightedHomogenisation | (intros; apply GlobalTheory.exists_weightedHomogenisation <;> assumption)
end _root_.GlobalTheory.T
