-- Prove2me | solution 1 for MurtySimon.sum_cA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:02.240641+00:00
-- url     : https://prove2.me/submissions/0f9a5286-22ea-4c4e-b958-dedf6364710a

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
theorem _root_.solution (M : Finset (Sym2 V)) : ∑ C, cA G M C = #(Lt G M) :=
  (card_eq_sum_card_fiberwise fun _ _ => mem_univ _).symm
end MurtySimon
