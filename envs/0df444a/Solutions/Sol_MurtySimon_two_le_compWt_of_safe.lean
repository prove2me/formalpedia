-- Prove2me | solution 1 for MurtySimon.two_le_compWt_of_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:43.803797+00:00
-- url     : https://prove2.me/submissions/480714dd-be46-43b6-8537-b4295ef6d1d7

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
theorem _root_.solution {C : (aux G M).ConnectedComponent} {p : V × V}
    (hp : p ∈ exits G M) (hpC : compOf G M p = C) (hs : ¬ Covered M p.2) : 2 ≤ compWt C := by
  have : wt M p = 2 := by simp [wt, hs]
  rw [← this]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨hp, hpC⟩)
end MurtySimon
