-- Prove2me | solution 2 for Hamiltonicity.ore
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:59:43.955344+00:00
-- url     : https://prove2.me/submissions/dd18882c-0691-4a20-8af9-bb1e69ac5ff7

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_ClosureAux
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_MengerHamilton_Hamiltonian
public import Theorems.Thm_Hamiltonicity_isHamiltonian_sup_edge_iff
public import Theorems.Thm_Hamiltonicity_isHamiltonian_of_forall_adj


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdeg : ∀ u v, u ≠ v → ¬ G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by
  suffices key : ∀ N (H : SimpleGraph V) [DecidableRel H.Adj],
      (Finset.univ.filter (fun p : V × V => p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2)).card = N →
      (∀ u v, u ≠ v → ¬ H.Adj u v → Fintype.card V ≤ H.degree u + H.degree v) →
      H.IsHamiltonian from key _ G rfl hdeg
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro H _ hN hH
  by_cases hall : ∀ u v, u ≠ v → H.Adj u v
  · exact isHamiltonian_of_forall_adj hn hall
  push Not at hall
  obtain ⟨u, v, huv, hnadj⟩ := hall
  classical
  have hle : H ≤ H ⊔ edge u v := le_sup_left
  rw [← isHamiltonian_sup_edge_iff H huv hnadj (hH u v huv hnadj)]
  refine ih _ ?_ (H ⊔ edge u v) rfl ?_
  · rw [← hN]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(u, v), ?_, ?_⟩
      · simp [huv, hnadj]
      · simp [huv, edge_adj]
    · intro p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 (hle h)⟩
  · intro a b hab hnab
    have := hH a b hab (fun h => hnab (hle h))
    exact this.trans (add_le_add (degree_le_of_le hle) (degree_le_of_le hle))
end Hamiltonicity
