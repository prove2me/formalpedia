-- Prove2me | solution 1 for JardenShami.Iio_succNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:26.075171+00:00
-- url     : https://prove2.me/submissions/ae5fe7eb-2b7a-4426-8408-26ff49180bec

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution {t : T} (ht' : ¬ IsLeaf t) : Set.Iio (succNode ht') = Set.Iic t := by
  have hm : t < succNode ht' := WellFounded.min_mem _ {x | t < x} _
  ext x
  constructor
  · intro hx
    rcases lt_trichotomy_of_lt hx hm with h | rfl | h
    · exact h.le
    · exact le_rfl
    · exact absurd hx (WellFounded.not_lt_min wellFounded_lt {x | t < x} h)
  · intro hx
    exact lt_of_le_of_lt hx hm
end JardenShami
