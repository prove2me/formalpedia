-- Prove2me | solution 1 for MurtySimon.sum_cB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:08.325809+00:00
-- url     : https://prove2.me/submissions/0069a55f-3355-4cc3-8fde-9a5c577414ad

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_IsMid_symm


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
theorem _root_.solution (M : Finset (Sym2 V)) : ∑ C, cB G M C = #(Rt G) :=
  (card_eq_sum_card_fiberwise fun _ _ => mem_univ _).symm
end MurtySimon
