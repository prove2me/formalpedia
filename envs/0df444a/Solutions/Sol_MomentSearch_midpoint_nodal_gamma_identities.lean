-- Prove2me | solution 1 for MomentSearch.midpoint_nodal_gamma_identities
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:30:09.994789+00:00
-- url     : https://prove2.me/submissions/dd6e48bc-4b5f-4081-9060-21ee278772bc

import Mathlib

private theorem midpointProduct (n : ℕ) (u : ℝ) (hu : 0 ≤ u) (hun : u ≤ n) :
    (∏ j ∈ Finset.Icc 1 n, ((j : ℝ) - 1 / 2 - u)) =
      Real.Gamma (u + 1 / 2) * Real.Gamma ((n : ℝ) - u + 1 / 2) /
        Real.pi * Real.cos (Real.pi * u) := by
  by_cases hc : Real.cos (Real.pi * u) = 0
  · obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hc
    have he : u = (k : ℝ) + 1 / 2 := by
      apply mul_left_cancel₀ Real.pi_ne_zero
      linarith only [hk]
    have hk0 : (0 : ℤ) ≤ k := by
      have : (-1 : ℝ) < k := by linarith
      exact_mod_cast this
    have hkn : k < (n : ℤ) := by
      exact_mod_cast (show (k : ℝ) < n by linarith)
    let j := k.toNat + 1
    have hj : j ∈ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc, j]
      omega
    have hjr : (j : ℝ) = k + 1 := by
      simp [j, Int.toNat_of_nonneg hk0, ← Int.cast_natCast (R := ℝ) k.toNat]
    rw [hc, mul_zero]
    exact Finset.prod_eq_zero hj (by linarith)
  · have recurrence (m : ℕ) :
        (∏ j ∈ Finset.Icc 1 m, ((j : ℝ) - 1 / 2 - u)) =
        Real.Gamma (u + 1 / 2) * Real.Gamma ((m : ℝ) - u + 1 / 2) /
          Real.pi * Real.cos (Real.pi * u) := by
      induction m with
      | zero =>
        have hf := Real.Gamma_mul_Gamma_one_sub (u + 1 / 2)
        rw [show 1 - (u + 1 / 2) = 0 - u + 1 / 2 by ring,
          show Real.pi * (u + 1 / 2) = Real.pi * u + Real.pi / 2 by ring,
          Real.sin_add_pi_div_two] at hf
        simp only [Nat.cast_zero, Finset.Icc_eq_empty_of_lt (by decide : 0 < 1), Finset.prod_empty]
        rw [hf]
        field_simp [Real.pi_ne_zero, hc]
      | succ m ih =>
        have hnz : (m : ℝ) - u + 1 / 2 ≠ 0 := by
          intro hz
          apply hc
          apply Real.cos_eq_zero_iff.mpr
          refine ⟨(m : ℤ), ?_⟩
          push_cast
          rw [show u = (m : ℝ) + 1 / 2 by linarith]
          ring
        rw [Finset.prod_Icc_succ_top (by omega) _, ih, Nat.cast_succ,
          show (m : ℝ) + 1 - u + 1 / 2 = (m - u + 1 / 2) + 1 by ring,
          Real.Gamma_add_one hnz]
        ring
    exact recurrence n

theorem solution (N : ℕ) (hN : 0 < N) :
    let ζ : ℕ → ℝ := fun j => -1 + (2 * (j : ℝ) - 1) / (N : ℝ)
    let T := Lagrange.nodal (Finset.Icc 1 N) ζ
    let b : ℝ := Real.pi * N / 2
    let G : ℝ → ℝ := fun x =>
      (2 / (N : ℝ)) ^ N / Real.pi *
        (Real.Gamma ((N : ℝ) / 2 * (1 + x) + 1 / 2) *
          Real.Gamma ((N : ℝ) / 2 * (1 - x) + 1 / 2))
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |T.eval x| = G x * |Real.cos (b * (x + 1))|) ∧
    (∀ j ∈ Finset.Icc 1 N, |T.derivative.eval (ζ j)| = G (ζ j) * b) := by
  intro ζ T b G
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have signed (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
      T.eval x = (-1 : ℝ)^N * G x * Real.cos (b * (x + 1)) := by
    let u := (N : ℝ) / 2 * (1 + x)
    have hu : 0 ≤ u := by dsimp [u]; nlinarith [mul_nonneg hNr.le (show 0 ≤ 1+x by linarith [hx.1])]
    have hun : u ≤ N := by dsimp [u]; nlinarith [mul_nonneg hNr.le (show 0 ≤ 1-x by linarith [hx.2])]
    have hf (j : ℕ) : x - ζ j = (-1 * (2 / (N : ℝ))) * ((j : ℝ) - 1 / 2 - u) := by
      dsimp [ζ, u]
      field_simp
      ring
    dsimp only [T]
    rw [Lagrange.eval_nodal]
    simp_rw [hf]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, midpointProduct N u hu hun, mul_pow]
    simp only [Nat.add_sub_cancel]
    dsimp [G, b, u]
    ring_nf
  have posG (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : 0 < G x := by
    have hx₁ : 0 ≤ 1+x := by linarith [hx.1]
    have hx₂ : 0 ≤ 1-x := by linarith [hx.2]
    dsimp [G]
    apply mul_pos (by positivity)
    exact mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  constructor
  · intro x hx
    rw [signed x hx, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (posG x hx)]
  · intro j hj
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj
    have hjlo : (1 : ℝ) ≤ j := by exact_mod_cast hj₁
    have hjhi : (j : ℝ) ≤ N := by exact_mod_cast hj₂
    have hz : ζ j ∈ Set.Ioo (-1 : ℝ) 1 := by
      dsimp [ζ]
      constructor
      · linarith [div_pos (show 0 < 2 * (j : ℝ) - 1 by linarith) hNr]
      · have := (div_lt_iff₀ hNr).mpr (show 2 * (j : ℝ) - 1 < 2 * N by linarith)
        linarith
    have hc : Real.cos (b * (ζ j + 1)) = 0 := by
      apply Real.cos_eq_zero_iff.mpr
      refine ⟨(j : ℤ)-1, ?_⟩
      dsimp [b, ζ]
      push_cast
      field_simp
      ring
    have hs : |Real.sin (b * (ζ j + 1))| = 1 := by
      rcases Real.cos_eq_zero_iff_sin_eq.mp hc with h | h <;> simp [h]
    have hdiff : DifferentiableAt ℝ (fun x => (-1 : ℝ)^N * G x) (ζ j) := by
      dsimp only [G]
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.mul <;> apply DifferentiableAt.comp _ (Real.differentiableAt_Gamma _) _ 
      all_goals try fun_prop
      all_goals
        intro m
        have hm : (0 : ℝ) ≤ m := by positivity
        nlinarith [mul_pos hNr (show 0 < 1 + ζ j by linarith [hz.1]),
          mul_pos hNr (show 0 < 1 - ζ j by linarith [hz.2])]
    have harg : HasDerivAt (fun x : ℝ => b * (x + 1)) b (ζ j) := by
      simpa using (((hasDerivAt_id (ζ j)).add_const 1).const_mul b)
    have hd := hdiff.hasDerivAt.mul harg.cos
    have heq : (fun x => T.eval x) =ᶠ[nhds (ζ j)]
        (fun x => (-1 : ℝ)^N * G x * Real.cos (b * (x+1))) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo hz] with x hx
      exact signed x ⟨hx.1.le,hx.2.le⟩
    have hh := (T.hasDerivAt (ζ j)).unique (hd.congr_of_eventuallyEq heq)
    rw [hh]
    simp only [hc, mul_zero, zero_add, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      hs, abs_of_pos (posG _ ⟨hz.1.le,hz.2.le⟩), abs_of_pos (show 0 < b by dsimp [b]; positivity)]
