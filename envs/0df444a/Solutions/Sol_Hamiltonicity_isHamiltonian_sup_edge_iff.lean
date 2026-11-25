-- Prove2me | solution 1 for Hamiltonicity.isHamiltonian_sup_edge_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:33:39.666962+00:00
-- url     : https://prove2.me/submissions/c94ca845-9ede-42b6-9079-771b738bedbf

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_ClosureAux
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_MengerHamilton_Hamiltonian
public import Theorems.Thm_Hamiltonicity_isHamiltonian_of_sup_edge
public import Theorems.Thm_Menger_Aux_Fam_mono


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v) :
    (G ⊔ edge u v).IsHamiltonian ↔ G.IsHamiltonian := by
  exact ⟨isHamiltonian_of_sup_edge G huv hnadj hdeg, fun h => h.mono le_sup_left⟩
end Hamiltonicity
