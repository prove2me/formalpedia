-- Prove2me | solution 1 for IntroDelayAMDP.lemma_D_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:48:54.803049+00:00
-- url     : https://prove2.me/submissions/87d9c5d2-b053-4c75-b5c7-fa02cc992e58

import Mathlib

open MeasureTheory

theorem solution {A' : Type} [Fintype A'] [Nonempty A'] (π : A' → ℝ) (hπ : ∀ a, 0 < π a)
    (hπ1 : ∑ a, π a = 1) (g : A' → ℝ) (η : ℝ) (hη : 0 < η) (π' : A' → ℝ)
    (hπ' : ∀ a, π' a = π a * Real.exp (-η * g a) / ∑ b, π b * Real.exp (-η * g b)) (a : A') :
    |Real.log (π' a / π a)| ≤
      η * (Finset.univ.sup' Finset.univ_nonempty g - Finset.univ.inf' Finset.univ_nonempty g) := by
  obtain ⟨M, hM⟩ : ∃ M, M = Finset.univ.sup' Finset.univ_nonempty g := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = Finset.univ.inf' Finset.univ_nonempty g := ⟨_, rfl⟩
  rw [← hM, ← hm]
  have hgM : ∀ b, g b ≤ M := fun b => by rw [hM]; exact Finset.le_sup' g (Finset.mem_univ b)
  have hgm : ∀ b, m ≤ g b := fun b => by rw [hm]; exact Finset.inf'_le g (Finset.mem_univ b)
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∑ b, π b * Real.exp (-η * g b) := ⟨_, rfl⟩
  have hZlo : Real.exp (-η * M) ≤ Z := by
    rw [hZ]
    calc Real.exp (-η * M) = ∑ b, π b * Real.exp (-η * M) := by
          rw [← Finset.sum_mul, hπ1, one_mul]
      _ ≤ ∑ b, π b * Real.exp (-η * g b) := by
          apply Finset.sum_le_sum
          intro b _
          apply mul_le_mul_of_nonneg_left _ (hπ b).le
          apply Real.exp_le_exp.mpr
          nlinarith [hgM b]
  have hZhi : Z ≤ Real.exp (-η * m) := by
    rw [hZ]
    calc ∑ b, π b * Real.exp (-η * g b) ≤ ∑ b, π b * Real.exp (-η * m) := by
          apply Finset.sum_le_sum
          intro b _
          apply mul_le_mul_of_nonneg_left _ (hπ b).le
          apply Real.exp_le_exp.mpr
          nlinarith [hgm b]
      _ = Real.exp (-η * m) := by rw [← Finset.sum_mul, hπ1, one_mul]
  have hZpos : 0 < Z := lt_of_lt_of_le (Real.exp_pos _) hZlo
  have hratio : π' a / π a = Real.exp (-η * g a) / Z := by
    rw [hπ' a, ← hZ, mul_div_assoc, mul_div_cancel_left₀ _ (hπ a).ne']
  rw [hratio, Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  have hl1 : -η * M ≤ Real.log Z := by
    have := Real.log_le_log (Real.exp_pos _) hZlo
    rwa [Real.log_exp] at this
  have hl2 : Real.log Z ≤ -η * m := by
    have := Real.log_le_log hZpos hZhi
    rwa [Real.log_exp] at this
  have e1 := mul_le_mul_of_nonneg_left (hgM a) hη.le
  have e2 := mul_le_mul_of_nonneg_left (hgm a) hη.le
  rw [abs_le]
  constructor <;> nlinarith
