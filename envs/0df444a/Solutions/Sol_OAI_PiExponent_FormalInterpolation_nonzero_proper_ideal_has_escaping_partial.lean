-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.nonzero_proper_ideal_has_escaping_partial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:06:21.953696+00:00
-- url     : https://prove2.me/submissions/d984b0d5-275f-426b-8c45-6bec7f83515d

import Mathlib

open MvPolynomial

theorem solution
    {k σ : Type*} [Field k] [CharZero k]
    (I : Ideal (MvPolynomial σ k)) (hIbot : I ≠ ⊥) (hItop : I ≠ ⊤) :
    ∃ F : MvPolynomial σ k, F ∈ I ∧
      ∃ i : σ, MvPolynomial.pderiv i F ∉ I := by
  classical
  by_contra hcon
  push Not at hcon
  -- every nonzero element of I leads to a contradiction, by strong induction on totalDegree
  have key : ∀ n, ∀ F ∈ I, F ≠ 0 → F.totalDegree = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro F hF hF0 hdeg
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, totalDegree_eq_zero_iff_eq_C] at hdeg
        have hc : F.coeff 0 ≠ 0 := by
          intro hc; apply hF0; rw [hdeg, hc, C_0]
        apply hItop
        apply Ideal.eq_top_of_isUnit_mem _ hF
        rw [hdeg]; exact (isUnit_iff_ne_zero.mpr hc).map C
      · -- pick a monomial of maximal degree
        obtain ⟨d, hd, hdmax⟩ := Finset.exists_max_image F.support
          (fun s => s.sum fun _ e => e) (support_nonempty.mpr hF0)
        have hdn : (d.sum fun _ e => e) = n := by
          rw [← hdeg]
          exact le_antisymm (le_totalDegree hd) (Finset.sup_le hdmax)
        have : d ≠ 0 := by
          rintro rfl; simp at hdn; omega
        obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp this
        simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
        set G := pderiv i F
        have hGd : G.coeff (d - Finsupp.single i 1) ≠ 0 := by
          rw [coeff_pderiv]
          have : d - Finsupp.single i 1 + Finsupp.single i 1 = d := by
            ext j; by_cases hj : j = i
            · subst hj; simp; omega
            · simp [Ne.symm hj]
          rw [this]
          refine mul_ne_zero (mem_support_iff.mp hd) ?_
          exact Nat.cast_add_one_ne_zero _
        have hG0 : G ≠ 0 := by intro h; apply hGd; rw [h, coeff_zero]
        have hGlt : G.totalDegree < n := by
          rw [totalDegree]
          refine lt_of_le_of_lt (Finset.sup_le (a := n - 1) ?_) (by omega)
          intro m hm
          rw [mem_support_iff, coeff_pderiv] at hm
          have hm' : m + Finsupp.single i 1 ∈ F.support := by
            rw [mem_support_iff]; intro h; apply hm; rw [h, zero_mul]
          have := hdmax _ hm'
          rw [hdn, Finsupp.sum_add_index' (by simp) (by intros; rfl),
            Finsupp.sum_single_index rfl] at this
          omega
        exact ih _ hGlt G (hcon F hF i) hG0 rfl
  obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hIbot
  exact key _ F hF hF0 rfl
