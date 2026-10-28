-- Prove2me | solution 1 for MusicStreaming.CoreSelection.userCentric_mem_allocSet
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:04:13.441984+00:00
-- url     : https://prove2.me/submissions/9784df0e-f7d5-4428-b686-4fa6e183ea4d

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting

set_option autoImplicit false

open MusicStreaming.CoreSelection

namespace MS3A

lemma userTotal_pos {n : ℕ} (t : MusicStreaming.Axioms.Problem n) (k : ℕ) (hk : k ∈ t.support) :
    (0 : ℝ) < MusicStreaming.Axioms.userTotal t k := by
  have : 0 < MusicStreaming.Axioms.userTotal t k := by
    by_contra h
    have h0 : MusicStreaming.Axioms.userTotal t k = 0 := by omega
    unfold MusicStreaming.Axioms.userTotal at h0
    have : t k = 0 := by
      funext i
      exact (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ i)
    exact (Finsupp.mem_support_iff.mp hk) this
  exact_mod_cast this

lemma col_sum {n : ℕ} (t : MusicStreaming.Axioms.Problem n) (k : ℕ) (hk : k ∈ t.support) :
    ∑ i, (t k i : ℝ) / MusicStreaming.Axioms.userTotal t k = 1 := by
  rw [← Finset.sum_div]
  have : (∑ i, (t k i : ℝ)) = MusicStreaming.Axioms.userTotal t k := by
    simp [MusicStreaming.Axioms.userTotal]
  rw [this]; exact div_self (userTotal_pos t k hk).ne'

lemma sum_userCentric {n : ℕ} (t : MusicStreaming.Axioms.Problem n) :
    ∑ i, userCentric t i = t.support.card := by
  unfold userCentric
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun k hk => col_sum t k hk)]
  simp

lemma reward_userCentric {n : ℕ} (t : MusicStreaming.Axioms.Problem n) :
    MusicStreaming.Axioms.reward userCentric t = userCentric t := by
  funext i
  unfold MusicStreaming.Axioms.reward
  rw [sum_userCentric]
  by_cases h : (t.support.card : ℝ) = 0
  · have h0 : t.support = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast h)
    simp [h, userCentric, h0]
  · field_simp

end MS3A

open MS3A in
theorem solution (n : ℕ) (t : MusicStreaming.Axioms.Problem n) :
    MusicStreaming.Axioms.reward userCentric t ∈ MusicStreaming.Core.allocSet t := by
  rw [reward_userCentric]
  refine ⟨fun j i => (t j i : ℝ) / MusicStreaming.Axioms.userTotal t j, fun j hj => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    have : t j i = 0 := by simpa [MusicStreaming.Axioms.listened] using hi
    simp [this]
  · intro i _; positivity
  · exact col_sum t j hj
  · funext i
    simp [userCentric, Finset.sum_apply]

