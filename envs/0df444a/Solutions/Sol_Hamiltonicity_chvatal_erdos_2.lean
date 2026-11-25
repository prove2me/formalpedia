-- Prove2me | solution 2 for Hamiltonicity.chvatal_erdos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:59:36.883328+00:00
-- url     : https://prove2.me/submissions/74cf746f-835a-45d7-91a1-0c717b0dd92d

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_ClosureAux
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_MengerHamilton_Hamiltonian
public import Theorems.Thm_Hamiltonicity_chvatal_erdos_aux


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V) (k : ℕ)
    (hk : IsKConnected G k) (hα : ∀ s : Set V, G.IsIndepSet s → s.ncard ≤ k) :
    G.IsHamiltonian := by
  exact chvatal_erdos_aux G hn k hk.2 hα
end Hamiltonicity
