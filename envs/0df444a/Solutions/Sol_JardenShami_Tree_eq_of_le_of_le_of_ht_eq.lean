-- Prove2me | solution 1 for JardenShami.Tree.eq_of_le_of_le_of_ht_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:37.524517+00:00
-- url     : https://prove2.me/submissions/62576739-7051-428c-a2d6-5f2bcbf7b8d6

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open JardenShami.Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami.Tree
theorem _root_.solution {x y z : T} (hx : x ≤ z) (hy : y ≤ z) (h : ht x = ht y) :
    x = y := by
  rcases hx.lt_or_eq with hx | rfl
  · rcases hy.lt_or_eq with hy | rfl
    · rcases lt_trichotomy_of_lt hx hy with h' | h' | h'
      · exact absurd h (ht_lt_ht h').ne
      · exact h'
      · exact absurd h (ht_lt_ht h').ne'
    · exact absurd h (ht_lt_ht hx).ne
  · rcases hy.lt_or_eq with hy | rfl
    · exact absurd h (ht_lt_ht hy).ne'
    · rfl
end JardenShami.Tree
