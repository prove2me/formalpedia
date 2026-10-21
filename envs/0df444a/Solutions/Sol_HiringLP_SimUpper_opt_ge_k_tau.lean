-- Prove2me | solution 1 for HiringLP.SimUpper.opt_ge_k_tau
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:07:34.989862+00:00
-- url     : https://prove2.me/submissions/d33d0621-6c54-46a0-8e3d-f425c122094e

import Mathlib
import Definitions.Def_HiringLP_SimUpper_Model
import Definitions.Def_HiringLP_SimUpper_HardInstance

set_option autoImplicit false
open HiringLP.SimUpper Finset

theorem setProb_ind_HSU {n : ℕ} (S A : Finset (Fin n)) :
    setProb (fun i => (if i ∈ S then (1 : ℝ) else 0)) A = if A = S then 1 else 0 := by
  unfold setProb
  split_ifs with h
  · subst h
    apply prod_eq_one
    intro i _
    by_cases hi : i ∈ A <;> simp [hi]
  · have : ∃ i, ¬ (i ∈ A ↔ i ∈ S) := by
      by_contra hc
      push_neg at hc
      exact h (Finset.ext hc)
    obtain ⟨i, hi⟩ := this
    apply prod_eq_zero (Finset.mem_univ i)
    by_cases h1 : i ∈ A <;> by_cases h2 : i ∈ S <;> simp_all

theorem solution (k j : ℕ) (ε τ : ℝ) (hk : 1 ≤ k) (hkj : k ≤ j) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (k : ℝ) * τ ≤ OPTsim (hardInstance k j ε τ) := by
  set S : Finset (Fin (j ^ 2 + k)) := univ.filter (fun i => ¬ (i.val < j ^ 2)) with hS
  have hcard : S.card = k := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (j ^ 2 + k))))
      (fun i : Fin (j ^ 2 + k) => (i : ℕ) < j ^ 2)
    have h2 : (univ.filter (fun i : Fin (j ^ 2 + k) => (i : ℕ) < j ^ 2)).card = j ^ 2 := by
      rw [Fin.card_filter_val_lt]; omega
    simp only [card_univ, Fintype.card_fin] at h1
    rw [hS]
    omega
  have hrew : reward (hardInstance k j ε τ) S = (k : ℝ) * τ := by
    unfold reward rewardIndep
    have hq : (fun i : Fin (j ^ 2 + k) => (if i ∈ S then (1 : ℝ) else 0) * (hardInstance k j ε τ).p i) =
        fun i => if i ∈ S then (1 : ℝ) else 0 := by
      funext i
      by_cases hi : i ∈ S
      · have : ¬ (i.val < j ^ 2) := by simpa [hS] using hi
        simp [hi, hardInstance, this]
      · simp [hi]
    rw [hq]
    simp_rw [setProb_ind_HSU S]
    rw [Finset.sum_eq_single S]
    · simp only [if_true, one_mul]
      have hv : ∑ i ∈ S, (hardInstance k j ε τ).v i = k * τ := by
        have : ∀ i ∈ S, (hardInstance k j ε τ).v i = τ := by
          intro i hi
          have : ¬ (i.val < j ^ 2) := by simpa [hS] using hi
          simp [hardInstance, this]
        rw [sum_congr rfl this]; simp [hcard]
      rw [hv]
      have : (S.card : ℝ) - (hardInstance k j ε τ).k = 0 := by
        rw [hcard]; simp [hardInstance]
      rw [this]; simp
    · intro A _ hA; simp [hA]
    · intro h; exact absurd (Finset.mem_univ S) h
  rw [← hrew]
  exact le_csSup (Set.finite_range _).bddAbove ⟨S, rfl⟩
