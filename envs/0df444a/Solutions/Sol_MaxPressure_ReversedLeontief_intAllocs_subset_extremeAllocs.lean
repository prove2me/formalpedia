-- Prove2me | solution 1 for MaxPressure.ReversedLeontief.intAllocs_subset_extremeAllocs
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:25:54.564663+00:00
-- url     : https://prove2.me/submissions/c6ebd04c-b7ee-4997-bd39-e3d8a06c1520

import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network
set_option autoImplicit false
open MaxPressure.ReversedLeontief

theorem gg_bound {I J K : ℕ} (N : Network I J K) (hN : N.Standing) (x : Fin J → ℝ)
    (hx : x ∈ allocSet N) (j : Fin J) : x j ≤ 1 := by
  obtain ⟨h1, _, _, _, h5, _⟩ := hN
  obtain ⟨k, hk⟩ := h5 j
  have hA : ∀ k j', 0 ≤ N.A k j' := fun k j' => by rcases h1 k j' with h | h <;> rw [h] <;> norm_num
  have hle := hx.2.1 k
  have h : N.A k j * x j ≤ ∑ j', N.A k j' * x j' :=
    Finset.single_le_sum (f := fun j' => N.A k j' * x j')
      (fun j' _ => mul_nonneg (hA k j') (hx.1 j')) (Finset.mem_univ j)
  rw [hk] at h
  linarith

theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing) :
    intAllocs N ⊆ extremeAllocs N := by
  intro a ha
  obtain ⟨haS, hnat⟩ := ha
  refine ⟨haS, ?_⟩
  intro x1 hx1 x2 hx2 hseg
  obtain ⟨s, t, hs, ht, hst, hsum⟩ := hseg
  have key : ∀ j, x1 j = a j ∧ x2 j = a j := by
    intro j
    have hj := congrFun hsum j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
    have b1 := gg_bound N hN x1 hx1 j
    have b2 := gg_bound N hN x2 hx2 j
    have n1 := hx1.1 j
    have n2 := hx2.1 j
    have ba := gg_bound N hN a haS j
    obtain ⟨m, hm⟩ := hnat j
    have hm01 : a j = 0 ∨ a j = 1 := by
      have : (m : ℝ) ≤ 1 := hm ▸ ba
      have hm1 : m ≤ 1 := by exact_mod_cast this
      interval_cases m
      · left; simpa using hm
      · right; simpa using hm
    rcases hm01 with h0 | h1
    · rw [h0] at hj ⊢
      have e1 : s * x1 j = 0 := by nlinarith [mul_nonneg hs.le n1, mul_nonneg ht.le n2]
      have e2 : t * x2 j = 0 := by nlinarith [mul_nonneg hs.le n1, mul_nonneg ht.le n2]
      constructor
      · rcases mul_eq_zero.mp e1 with h | h
        · exact absurd h hs.ne'
        · exact h
      · rcases mul_eq_zero.mp e2 with h | h
        · exact absurd h ht.ne'
        · exact h
    · rw [h1] at hj ⊢
      have p1 : 0 ≤ s * (1 - x1 j) := mul_nonneg hs.le (by linarith)
      have p2 : 0 ≤ t * (1 - x2 j) := mul_nonneg ht.le (by linarith)
      have e1 : s * (1 - x1 j) = 0 := by nlinarith
      have e2 : t * (1 - x2 j) = 0 := by nlinarith
      constructor
      · rcases mul_eq_zero.mp e1 with h | h
        · exact absurd h hs.ne'
        · linarith
      · rcases mul_eq_zero.mp e2 with h | h
        · exact absurd h ht.ne'
        · linarith
  exact funext fun j => (key j).1
