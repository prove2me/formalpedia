-- Prove2me | solution 2 for Hamiltonicity.dirac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:01:19.619844+00:00
-- url     : https://prove2.me/submissions/0bf317b1-9a20-4da8-bdaa-94e82d66ad2a

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_ClosureAux
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_MengerHamilton_Hamiltonian
public import Theorems.Thm_Hamiltonicity_ore

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdeg : Fintype.card V ≤ 2 * G.minDegree) : G.IsHamiltonian := by
  refine ore G hn fun u v _ _ => hdeg.trans ?_
  have := G.minDegree_le_degree u
  have := G.minDegree_le_degree v
  omega
end Hamiltonicity
