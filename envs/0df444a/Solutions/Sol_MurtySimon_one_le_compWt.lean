-- Prove2me | solution 1 for MurtySimon.one_le_compWt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:34.262875+00:00
-- url     : https://prove2.me/submissions/9cc53fae-b6ff-403c-933b-bb57f798634c

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_one_le_wt

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
theorem _root_.solution {C : (aux G M).ConnectedComponent} {p : V × V}
    (hp : p ∈ exits G M) (hpC : compOf G M p = C) : 1 ≤ compWt C :=
  (one_le_wt p).trans (single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨hp, hpC⟩))
end MurtySimon
