-- Prove2me | solution 1 for MurtySimon.IsEdgeMatching.eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:48.481365+00:00
-- url     : https://prove2.me/submissions/4a5fc7f5-1ac1-4ec0-8a55-4d7fbe3b6433

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
namespace IsEdgeMatching
theorem _root_.solution (hM : IsEdgeMatching G M) {x y z : V} (h1 : s(x, y) ∈ M)
    (h2 : s(x, z) ∈ M) : y = z := by
  by_contra hyz
  have hne : s(x, y) ≠ s(x, z) := fun h => hyz (Sym2.congr_right.1 h)
  exact hM.2 _ h1 _ h2 hne x (Sym2.mem_mk_left x y) (Sym2.mem_mk_left x z)
end IsEdgeMatching
end MurtySimon
