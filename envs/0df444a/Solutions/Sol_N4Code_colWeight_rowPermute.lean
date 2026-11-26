-- Prove2me | solution 1 for N4Code.colWeight_rowPermute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:36.71291+00:00
-- url     : https://prove2.me/submissions/09b93e54-bd99-4ffe-95bc-da3a5ca0a438

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    colWeight (rowPermute ρ c) = colWeight c := by
  unfold colWeight rowPermute
  apply Finset.card_bij (fun r _ => ρ r)
  · intro r hr
    simpa using hr
  · intro a _ b _ hab
    exact ρ.injective hab
  · intro b hb
    refine ⟨ρ.symm b, ?_, ?_⟩
    · simpa using hb
    · simp
end N4Code
