-- Prove2me | solution 1 for Hamiltonicity.isHamiltonian_of_sup_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:28.133008+00:00
-- url     : https://prove2.me/submissions/eb00fd2e-1542-4043-a1b8-5b1c67ba15b1

module
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Definitions.Def_MengerHamilton_ClosureAux
public import Theorems.Thm_Hamiltonicity_exists_cycArr_of_path
public import Theorems.Thm_Hamiltonicity_CycArr_isHamiltonian
public import Theorems.Thm_Hamiltonicity_CycArr_rotate
public import Theorems.Thm_Hamiltonicity_exists_cycArr_of_isHamiltonian
public import Theorems.Thm_Menger_Aux_Sep_symm


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
theorem _root_.solution [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v)
    (hH : (G ⊔ edge u v).IsHamiltonian) : G.IsHamiltonian := by
  set n := Fintype.card V with hn_def
  have hdu : G.degree u + 2 ≤ n := by
    rw [← card_neighborFinset_eq_degree]
    have h1 : u ∉ insert v (G.neighborFinset u) := by simp [huv]
    have h2 : v ∉ G.neighborFinset u := by simpa using hnadj
    have := Finset.card_le_univ (insert u (insert v (G.neighborFinset u)))
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2] at this
    omega
  have hdv : G.degree v + 2 ≤ n := by
    rw [← card_neighborFinset_eq_degree]
    have h1 : v ∉ insert u (G.neighborFinset v) := by simp [huv.symm]
    have h2 : u ∉ G.neighborFinset v := by simpa [G.adj_comm] using hnadj
    have := Finset.card_le_univ (insert v (insert u (G.neighborFinset v)))
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2] at this
    omega
  have hn : 3 ≤ n := by omega
  obtain ⟨f, hf⟩ := exists_cycArr_of_isHamiltonian hH hn
  by_cases hall : ∀ i, G.Adj (f i) (f (i + 1))
  · exact CycArr.isHamiltonian ⟨hf.three_le, hf.periodic, hf.inj, hall⟩ rfl
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  have huvi : (f i = u ∧ f (i + 1) = v) ∨ (f i = v ∧ f (i + 1) = u) := by
    have := hf.adj i
    rw [sup_adj] at this
    rcases this with h | h
    · exact absurd h hi
    · rw [edge_adj] at h
      exact h.1
  have hrot := hf.rotate (i + 1)
  set x : ℕ → V := fun j => f (i + 1 + j) with hx
  have hx0 : x 0 = f (i + 1) := rfl
  have hxn : x (n - 1) = f i := by
    simp only [x]
    rw [show i + 1 + (n - 1) = i + n by omega, hf.periodic]
  have hadj : ∀ j, j + 1 < n → G.Adj (x j) (x (j + 1)) := by
    intro j hj
    by_contra hne
    have := hrot.adj j
    rw [sup_adj] at this
    rcases this with h | h
    · exact hne h
    rw [edge_adj] at h
    have hcases : (x j = x (n - 1) ∧ x (j + 1) = x 0) ∨ (x j = x 0 ∧ x (j + 1) = x (n - 1)) := by
      rw [hx0, hxn]
      rcases huvi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h.1 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        simp [h1, h2, h3, h4]
    rcases hcases with ⟨h1, -⟩ | ⟨h1, h2⟩
    · have := hrot.inj _ _ (by omega) (by omega) h1
      omega
    · have := hrot.inj _ _ (by omega) (by omega) h1
      subst this
      have := hrot.inj _ _ (by omega) (by omega) h2
      omega
  rcases huvi with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- the path runs from `v` to `u`
    obtain ⟨g, hg⟩ := exists_cycArr_of_path G x hn hrot.inj hadj
      (by rw [hx0, hxn, h1, h2]; omega)
    exact hg.isHamiltonian rfl
  · -- reverse the path
    let y : ℕ → V := fun j => x (n - 1 - j)
    obtain ⟨g, hg⟩ := exists_cycArr_of_path G y hn
      (by
        intro a b ha hb hab
        have := hrot.inj _ _ (by omega) (by omega) hab
        omega)
      (by
        intro j hj
        have := hadj (n - 1 - (j + 1)) (by omega)
        rw [show n - 1 - (j + 1) + 1 = n - 1 - j by omega] at this
        exact this.symm)
      (by
        have hy0 : y 0 = v := by simp only [y, Nat.sub_zero]; rw [hxn, h1]
        have hyn : y (Fintype.card V - 1) = u := by
          simp only [y]
          rw [show n - 1 - (Fintype.card V - 1) = 0 by omega, hx0, h2]
        rw [add_comm] at hdeg
        convert hdeg using 3)
    exact hg.isHamiltonian rfl
end Hamiltonicity
