-- Prove2me | solution 2 for Hamiltonicity.isHamiltonian_sup_edge_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:58:00.504879+00:00
-- url     : https://prove2.me/submissions/0e8127c1-8480-420b-aad3-8d7025e62455

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
