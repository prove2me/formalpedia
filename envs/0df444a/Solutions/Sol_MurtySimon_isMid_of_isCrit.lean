-- Prove2me | solution 1 for MurtySimon.isMid_of_isCrit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:40.729484+00:00
-- url     : https://prove2.me/submissions/a8749a69-4ee3-4660-ad89-595180ec8bae

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_IsCrit_exists_mid

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
theorem _root_.solution {x y w : V} (h : IsCrit G s(x, y)) (hxw : G.Adj x w) (hwy : G.Adj w y) :
    IsMid G x y w := by
  obtain ⟨u, hu⟩ := h.exists_mid
  have := hu.2.2.2.2 w hxw hwy
  subst this
  exact hu
end MurtySimon
