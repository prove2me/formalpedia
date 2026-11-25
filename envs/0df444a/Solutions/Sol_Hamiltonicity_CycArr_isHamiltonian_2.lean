-- Prove2me | solution 2 for Hamiltonicity.CycArr.isHamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:54:27.897394+00:00
-- url     : https://prove2.me/submissions/b4c767b6-3924-4aa8-839f-23d45d88e521

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Theorems.Thm_Hamiltonicity_CycArr_exists_isCycle

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
namespace Hamiltonicity.CycArr
theorem _root_.solution [Fintype V] [DecidableEq V] (h : CycArr G m f)
    (hm : m = Fintype.card V) : G.IsHamiltonian := by
  intro _
  obtain ⟨c, hc, hl⟩ := h.exists_isCycle
  exact ⟨f 0, c, Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.2 ⟨hc, hl.trans hm⟩⟩
end Hamiltonicity.CycArr
