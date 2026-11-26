-- Prove2me | solution 1 for MurtySimon.sum_compWt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:29.335826+00:00
-- url     : https://prove2.me/submissions/19c08e68-2edd-4552-a4ce-a6cad5f8724d

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}
namespace MurtySimon
theorem _root_.solution : ∑ C, compWt (G := G) (M := M) C = ∑ p ∈ exits G M, wt M p :=
  sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _
end MurtySimon
