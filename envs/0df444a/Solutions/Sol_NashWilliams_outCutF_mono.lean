-- Prove2me | solution 1 for NashWilliams.outCutF_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:23:09.061883+00:00
-- url     : https://prove2.me/submissions/7ddb61e3-fe00-4f21-abe5-84ec3d65b963

module
public import Definitions.Def_NashWilliamsLib_Mader
public import Definitions.Def_NashWilliamsLib_Splitting
public import Definitions.Def_NashWilliamsLib_Orientation

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
omit [DecidableEq ι]
namespace NashWilliams
theorem _root_.solution {ends : ι → V × V} {o : ι → Bool} {F G : Finset ι} (h : F ⊆ G)
    (S : Finset V) : outCutF ends o F S ≤ outCutF ends o G S := by
  unfold outCutF
  exact card_le_card (filter_subset_filter _ h)
end NashWilliams
