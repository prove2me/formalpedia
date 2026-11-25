-- Prove2me | solution 1 for NashWilliams.one_le_dsF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:23:04.160213+00:00
-- url     : https://prove2.me/submissions/e26c3359-6774-4408-b8ac-eee0205e36fb

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution {s u : V} {ends : ι → V × V} {F : Finset ι} {i : ι} (hi : i ∈ F)
    (hJ : Joins s u (ends i)) {X : Finset V} (hu : u ∈ X) : 1 ≤ dsF s ends F X := by
  unfold dsF
  refine Finset.card_pos.2 ⟨i, mem_filter.2 ⟨hi, ?_⟩⟩
  obtain ⟨h | h, -⟩ := hJ <;> rw [h] <;> simp [hu]
end NashWilliams
