-- Prove2me | solution 1 for Hamiltonicity.exists_cycArr_of_conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:28.277195+00:00
-- url     : https://prove2.me/submissions/e69c6564-09ed-469b-84b4-5fd89ea7d2b9

module
public import Definitions.Def_MengerHamilton_LongerCycle
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Theorems.Thm_Hamiltonicity_exists_path_avoiding
public import Theorems.Thm_Hamiltonicity_cycArr_of_isCycle
public import Theorems.Thm_Menger_Aux_Sep_symm


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hn : 3 ≤ Fintype.card V) (hk2 : 2 ≤ k)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) :
    ∃ m f, CycArr G m f := by
  classical
  by_contra hno
  push Not at hno
  have hacyc : G.IsAcyclic := fun v c hc => hno _ _ (cycArr_of_isCycle hc)
  have hconnG : G.Connected := by
    have hc0 := hconn ∅ (by simp; omega)
    have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    refine ⟨fun a b => ?_⟩
    obtain ⟨p, -, -⟩ := exists_path_avoiding ∅ hc0 (Set.notMem_empty a) (Set.notMem_empty b)
    exact p.reachable
  have htree : G.IsTree := ⟨hconnG, hacyc⟩
  have hdeg : ∀ v, 2 ≤ G.degree v := by
    intro v
    by_contra hlt
    push Not at hlt
    set N := G.neighborFinset v with hN
    have hNk : (N : Set V).ncard < k := by
      rw [Set.ncard_coe_finset, card_neighborFinset_eq_degree]
      omega
    obtain ⟨w, hw⟩ : ∃ w, w ∉ insert v N := by
      by_contra hcon
      push Not at hcon
      have := Finset.card_le_card (show Finset.univ ⊆ insert v N from fun w _ => hcon w)
      rw [Finset.card_univ] at this
      have := Finset.card_insert_le v N
      rw [card_neighborFinset_eq_degree] at this
      omega
    simp only [Finset.mem_insert, not_or] at hw
    have hvN : v ∉ (N : Set V) := by simp [N]
    obtain ⟨p, -, hpS⟩ := exists_path_avoiding _ (hconn _ hNk) hvN (by simpa using hw.2)
    obtain ⟨w', hvw', q, rfl⟩ := Walk.exists_eq_cons_of_ne (Ne.symm hw.1) p
    exact hpS w' (by simp) (by simpa [N] using hvw')
  have h1 := htree.card_edgeFinset
  have h2 := G.sum_degrees_eq_twice_card_edges
  have h3 : ∑ _v : V, 2 ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => hdeg v
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h3
  omega
end Hamiltonicity
