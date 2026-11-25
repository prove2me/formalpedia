-- Prove2me | solution 1 for Hamiltonicity.cycArr_of_isCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:29:25.778729+00:00
-- url     : https://prove2.me/submissions/8904e02b-ab35-41d3-99fb-dca39db961a9

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Theorems.Thm_Hamiltonicity_CycArr_of_fun

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution {G : SimpleGraph V} {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    CycArr G c.length (fun i => c.getVert (i % c.length)) := by
  have h3 := hc.three_le_length
  refine CycArr.of_fun h3 ?_ (fun i hi => c.adj_getVert_succ hi) (by simp)
  intro i j hi hj hij
  exact hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) hij
end Hamiltonicity
