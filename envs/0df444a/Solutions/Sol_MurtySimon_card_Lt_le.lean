-- Prove2me | solution 1 for MurtySimon.card_Lt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:14:01.294419+00:00
-- url     : https://prove2.me/submissions/ec8d7c3f-e01e-412d-82f8-275be26dcdde

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_main_chain

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
theorem _root_.solution (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G) :
    #(Lt G M) ≤ #(Rt G) + #(Nc G) := by
  obtain ⟨h1, h2, h3⟩ := main_chain hmax hG
  have h4 : ∑ C, ((cA G M C : ℤ) - cB G M C) ≤
      #((univ : Finset (aux G M).ConnectedComponent).filter fun C => cA G M C = cB G M C + 1) := by
    calc ∑ C, ((cA G M C : ℤ) - cB G M C)
        ≤ ∑ C, (if cA G M C = cB G M C + 1 then (1 : ℤ) else 0) := sum_le_sum fun C _ => h2 C
      _ = _ := by rw [sum_boole]
  omega
end MurtySimon
