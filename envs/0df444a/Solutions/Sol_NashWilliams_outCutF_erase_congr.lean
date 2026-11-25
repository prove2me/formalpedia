-- Prove2me | solution 1 for NashWilliams.outCutF_erase_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:27:14.503263+00:00
-- url     : https://prove2.me/submissions/062cf8de-ce97-4211-875a-74494e99d97b

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
theorem _root_.solution {ends : ι → V × V} {o : ι → Bool} {F : Finset ι} {s : V}
    (h : ∀ l ∈ F, (ends l).1 ≠ s ∧ (ends l).2 ≠ s) (S : Finset V) :
    outCutF ends o F (S.erase s) = outCutF ends o F S := by
  unfold outCutF
  congr 1
  refine filter_congr fun l hl => ?_
  obtain ⟨h1, h2⟩ := h l hl
  unfold Leaves
  split <;> simp [mem_erase, h1, h2]
end NashWilliams
