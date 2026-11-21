-- Prove2me | solution 1 for GwExact.numCols_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:20.695519+00:00
-- url     : https://prove2.me/submissions/5389427f-d656-4c9f-b5af-a0c676faacc7

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank

set_option autoImplicit true
@[expose] public section
public section
open GwExact
variable {α : Type*} [DecidableEq α] (f : ℕ → α)
namespace GwExact
theorem _root_.solution {m m' : ℕ} (h : m ≤ m') : numCols f m ≤ numCols f m' :=
  Finset.card_le_card (Finset.image_subset_image (Finset.range_subset_range.mpr h))
end GwExact
