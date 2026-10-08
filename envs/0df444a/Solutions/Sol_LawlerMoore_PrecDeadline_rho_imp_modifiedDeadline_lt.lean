-- Prove2me | solution 1 for LawlerMoore.PrecDeadline.rho_imp_modifiedDeadline_lt
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:17:11.685644+00:00
-- url     : https://prove2.me/submissions/2a274bcc-3018-4f48-b0d9-431bfaef27e4

import Mathlib
import Definitions.Def_LawlerMoore_PrecDeadline_modifiedDeadline
open LawlerMoore.PrecDeadline

theorem solution (n : ℕ) (d : Fin n → ℝ)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ i j, i ≠ j → ρ i j → modifiedDeadline ρ d ε i < modifiedDeadline ρ d ε j := by
  intro i j hij hr
  obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_inf'
    (Finset.insert_nonempty j (Finset.univ.filter (ρ j))) d
  have hki : k ∈ insert i (Finset.univ.filter (ρ i)) := by
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rcases hk with rfl | hk
    · exact Or.inr hr
    · exact Or.inr (htrans i j k hr hk)
  have hmin := Finset.inf'_le d hki
  have hv : (i : ℕ) < (j : ℕ) := by
    exact Fin.lt_def.mp (lt_of_le_of_ne (hnum i j hr) hij)
  have hvr : (i : ℝ) < (j : ℝ) := by exact_mod_cast hv
  have hmul := mul_lt_mul_of_pos_right hvr hε
  unfold modifiedDeadline
  rw [heq]
  linarith

#print axioms solution
