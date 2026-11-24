-- Prove2me | solution 1 for GlobalTheory.RootEx.OpELevi.card_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:06:00.782739+00:00
-- url     : https://prove2.me/submissions/93f22e9f-d1be-42d4-87f5-114422d69371

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpELevi
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.RootEx.OpELevi
theorem _root_.solution (p : ℕ) (_ : 1 ≤ p) (h2 : p ≤ c) :
    (Fintype.card {i : Fin (c + 1) // p < i.val + 1} : ℝ) = c + 1 - p := by
  have : Fintype.card {i : Fin (c + 1) // p < i.val + 1} = c + 1 - p := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin (c + 1) => p < i.val + 1) = Finset.Ici ⟨p, by omega⟩ := by
      ext i; simp [Fin.le_def]
    rw [this, Fin.card_Ici]
  rw [this, Nat.cast_sub (by omega)]; push_cast; ring
end GlobalTheory.RootEx.OpELevi
