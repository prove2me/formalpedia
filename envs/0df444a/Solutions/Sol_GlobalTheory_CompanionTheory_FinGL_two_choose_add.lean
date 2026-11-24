-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGL.two_choose_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:31:35.377805+00:00
-- url     : https://prove2.me/submissions/0b7adac4-2647-49bd-a25e-b2418628f37a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGL
namespace GlobalTheory.CompanionTheory.FinGL
theorem _root_.solution (m : ℕ) : 2 * m.choose 2 + m = m * m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    rw [h]
    nlinarith
end GlobalTheory.CompanionTheory.FinGL
