-- Prove2me | solution 1 for Hamiltonicity.exists_cycArr_of_isHamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:24.423613+00:00
-- url     : https://prove2.me/submissions/cd62eba4-9e27-4f3d-a2a3-8473e08c2dee

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Theorems.Thm_Hamiltonicity_cycArr_of_isCycle

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsHamiltonian) (hn : 3 ≤ Fintype.card V) :
    ∃ f, CycArr G (Fintype.card V) f := by
  obtain ⟨a, c, hc⟩ := hG (by omega)
  have := cycArr_of_isCycle hc.isCycle
  rw [hc.length_eq] at this
  exact ⟨_, this⟩
end Hamiltonicity
