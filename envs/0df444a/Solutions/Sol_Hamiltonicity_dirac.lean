-- Prove2me | solution 1 for Hamiltonicity.dirac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:37:20.309614+00:00
-- url     : https://prove2.me/submissions/da0219cb-d1f0-4049-9889-15188ea4cf5f

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
