-- Prove2me | solution 1 for N4Code.dRowMin_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:41.046219+00:00
-- url     : https://prove2.me/submissions/630ba4ed-5ac3-4577-9d9e-a0aebadb8d83

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (S T : Finset (Fin 4)) (hS : S.Nonempty)
    (hT : T.Nonempty) (y : Word n) :
    dRowMin C (S ∪ T) (by rcases hS with ⟨i, hi⟩; exact ⟨i, Finset.mem_union_left T hi⟩) y =
      min (dRowMin C S hS y) (dRowMin C T hT y) := by
  unfold dRowMin
  simp only [Finset.image_union]
  rw [Finset.min'_union]
end N4Code
