-- Prove2me | solution 1 for MurtySimon.pieces_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:57.949481+00:00
-- url     : https://prove2.me/submissions/edfc4e6c-b583-40c9-8139-941c2670be56

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality
public import Theorems.Thm_MurtySimon_sum_pieces
public import Theorems.Thm_MurtySimon_eq_case_conditions


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution (hG : IsCritical G) (heq : EqCase G) {M : Finset (Sym2 V)}
    (hmax : IsMaximalEdgeMatching G M) (C : (aux G ∅).ConnectedComponent) :
    cB G ∅ C ≤ #((LC0 C).filter (· ∉ M)) := by
  have h := sum_pieces M C
  have hnn : 0 ≤ ∑ D ∈ (univ : Finset (aux G M).ConnectedComponent).filter
      (fun D => emb G M D = C), ((cA G M D : ℤ) - cB G M D) := by
    apply sum_nonneg
    intro D _
    have := (eq_case_conditions hmax hG (heq M hmax)).1 D
    omega
  omega
end MurtySimon
