-- Prove2me | solution 1 for MusicStreaming.CoreSelection.one_user_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:05:54.472236+00:00
-- url     : https://prove2.me/submissions/7d70b789-cf31-4079-bf85-c0af0c53c60d

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting

set_option autoImplicit false
open MusicStreaming.CoreSelection

theorem solution (n : ℕ) (I : MusicStreaming.Axioms.Index n) (hI : IsIndexOn I) (hH : HomogeneityOn I)
    (hC : CoreSelectionOn I) (j : ℕ) (x : Fin n → ℕ) (hx : x ≠ 0)
    (hP : InPStar (Finsupp.single j x)) (i : Fin n) :
    I (Finsupp.single j x) i =
      (∑ i', I (Finsupp.single j x) i') * userCentric (Finsupp.single j x) i := by
  set t : MusicStreaming.Axioms.Problem n := Finsupp.single j x with ht
  have hsupp : t.support = {j} := Finsupp.support_single_ne_zero j hx
  have hcol : ∀ j' ∈ t.support, t j' = x := by
    intro j' hj'
    rw [hsupp] at hj'
    have : j' = j := by simpa using hj'
    subst this
    simp [t]
  have hT : 0 < ∑ i', (x i' : ℝ) := by
    obtain ⟨i0, hi0⟩ : ∃ i0, x i0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    exact Finset.sum_pos' (fun _ _ => Nat.cast_nonneg _)
      ⟨i0, Finset.mem_univ _, by exact_mod_cast Nat.pos_of_ne_zero hi0⟩
  have key : ∀ i i' : Fin n, I t i * x i' = I t i' * x i := by
    intro i i'
    by_cases h : x i' = 0
    · have h1 := hH t i' i 0 hP le_rfl (by
        intro j' hj'
        rw [hcol j' hj']
        simp [h])
      have : I t i' = 0 := by simpa using h1
      simp [h, this]
    · have hpos : (x i' : ℝ) ≠ 0 := by exact_mod_cast h
      have h1 := hH t i i' ((x i : ℝ) / x i') hP (by positivity) (by
        intro j' hj'
        rw [hcol j' hj']
        field_simp)
      rw [h1]
      field_simp
  have hU : userCentric t i = (x i : ℝ) / ∑ i', (x i' : ℝ) := by
    unfold userCentric
    rw [hsupp, Finset.sum_singleton]
    simp [MusicStreaming.Axioms.userTotal, t]
  rw [hU, mul_div_assoc', eq_div_iff hT.ne', Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i' _ => key i i'
