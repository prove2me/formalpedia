-- Prove2me | solution 1 for GlobalTheory.RootEx.OpELevi.card_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:06:01.456577+00:00
-- url     : https://prove2.me/submissions/82cf9bf5-7e05-4ffb-bee1-219f77a6f4ac

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
theorem _root_.solution (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ c) :
    (Fintype.card {l : Fin c // l.val + 1 < p} : ℝ) = p - 1 := by
  have : Fintype.card {l : Fin c // l.val + 1 < p} = p - 1 := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun l : Fin c => l.val + 1 < p) = Finset.Iio ⟨p - 1, by omega⟩ := by
      ext i; simp [Fin.lt_def]; omega
    rw [this, Fin.card_Iio]
  rw [this, Nat.cast_sub (by omega)]; push_cast; ring
end GlobalTheory.RootEx.OpELevi
