-- Prove2me | solution 1 for MaxPressure.StrictLeontief.off_buffer_R_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:22:49.831017+00:00
-- url     : https://prove2.me/submissions/41598fc3-b087-47cb-b1cd-b3aa969d29b9

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network

open MaxPressure.StrictLeontief in
lemma f4d7d3e6_R_nonpos_of_B_zero {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (j : Fin J) (i : Fin I) (h0 : N.B j i.succ = 0) : R N i j ≤ 0 := by
  obtain ⟨_, hB, _, _, _, _, _, _, hm, hP, _⟩ := hN
  have hmu : 0 ≤ mu N j := by
    unfold mu; exact le_of_lt (one_div_pos.mpr (hm j))
  have hsum : 0 ≤ ∑ i' : Fin (I + 1), N.B j i' * N.P j i' i.succ := by
    apply Finset.sum_nonneg
    intro i' _
    have hb : 0 ≤ N.B j i' := by rcases hB j i' with h | h <;> rw [h] <;> norm_num
    exact mul_nonneg hb (hP j i' i.succ)
  unfold R
  rw [h0]
  exact mul_nonpos_of_nonneg_of_nonpos hmu (by linarith)

open MaxPressure.StrictLeontief in
theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) :
    (∀ j, IsServiceActivity N j → ∀ i₀ : Fin I, N.B j i₀.succ = 1 →
      ∀ i : Fin I, i ≠ i₀ → N.B j i.succ = 0 ∧ R N i j ≤ 0) ∧
    (∀ j, IsInputActivity N j → ∀ i : Fin I, N.B j i.succ = 0 ∧ R N i j ≤ 0) := by
  have hB := hN.2.1
  constructor
  · intro j hj i₀ hi₀ i hne
    have h0 : N.B j i.succ = 0 := by
      rcases hB j i.succ with h | h
      · exact h
      · exfalso
        obtain ⟨u, _, hu⟩ := hSL j hj
        have e1 := hu i.succ h
        have e2 := hu i₀.succ hi₀
        exact hne (Fin.succ_injective _ (e1.trans e2.symm))
    exact ⟨h0, f4d7d3e6_R_nonpos_of_B_zero N hN j i h0⟩
  · intro j hj i
    have h0 : N.B j i.succ = 0 := hj.2 i
    exact ⟨h0, f4d7d3e6_R_nonpos_of_B_zero N hN j i h0⟩
