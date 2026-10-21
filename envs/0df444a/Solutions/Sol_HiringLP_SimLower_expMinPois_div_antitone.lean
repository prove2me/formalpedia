-- Prove2me | solution 1 for HiringLP.SimLower.expMinPois_div_antitone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:06:01.259119+00:00
-- url     : https://prove2.me/submissions/d6bd88c7-7a8d-4295-badc-66370379d0a2

import Mathlib
import Definitions.Def_HiringLP_SimLower_PoissonRatio

set_option autoImplicit false
open HiringLP.SimLower Finset

noncomputable def pp (x : ℝ) (j : ℕ) : ℝ := Real.exp (-x) * x ^ j / (j.factorial : ℝ)

noncomputable def SS (m : ℕ) (x : ℝ) : ℝ := ∑ i ∈ range m, pp x i

theorem pp_hasSum (l : ℝ) : HasSum (pp l) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) l).mul_left (Real.exp (-l))
  rw [← Real.exp_eq_exp_ℝ] at h
  have e : Real.exp (-l) * Real.exp l = 1 := by rw [← Real.exp_add]; simp
  rw [e] at h
  have e2 : pp l = fun j : ℕ => Real.exp (-l) * (l ^ j / (j.factorial : ℝ)) := by
    funext j; unfold pp; ring
  rw [e2]; exact h

theorem pp_rec (l : ℝ) (m : ℕ) : ((m + 1 : ℕ) : ℝ) * pp l (m + 1) = l * pp l m := by
  unfold pp
  rw [Nat.factorial_succ]
  push_cast
  have : ((m.factorial : ℝ)) ≠ 0 := by positivity
  have : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem pp_partial (l : ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), (i : ℝ) * pp l i = l * SS m l := by
  unfold SS
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ _ m, pp_rec l m]
    ring

theorem pp_nonneg (l : ℝ) (hl : 0 ≤ l) (j : ℕ) : 0 ≤ pp l j := by
  unfold pp; positivity

theorem SS_le_one (l : ℝ) (hl : 0 ≤ l) (m : ℕ) : SS m l ≤ 1 :=
  sum_le_hasSum (range m) (fun i _ => pp_nonneg l hl i) (pp_hasSum l)

theorem expMin_formula (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    expMinPois x k = x * SS k x + k * (1 - SS (k + 1) x) := by
  have hP2 : HasSum (fun n => pp x (n + (k + 1))) (1 - ∑ i ∈ range (k + 1), pp x i) :=
    (hasSum_nat_add_iff' (k + 1)).2 (pp_hasSum x)
  have hF : HasSum (fun n : ℕ => min ((n + (k + 1) : ℕ) : ℝ) (k : ℝ) * pp x (n + (k + 1)))
      ((k : ℝ) * (1 - ∑ i ∈ range (k + 1), pp x i)) := by
    have e : (fun n : ℕ => min ((n + (k + 1) : ℕ) : ℝ) (k : ℝ) * pp x (n + (k + 1))) =
        fun n : ℕ => (k : ℝ) * pp x (n + (k + 1)) := by
      funext n
      have : min ((n + (k + 1) : ℕ) : ℝ) (k : ℝ) = k := by
        apply min_eq_right; exact_mod_cast (by omega : k ≤ n + (k + 1))
      rw [this]
    rw [e]; exact hP2.mul_left _
  have hF2 : HasSum (fun j : ℕ => min (j : ℝ) (k : ℝ) * pp x j)
      ((k : ℝ) * (1 - ∑ i ∈ range (k + 1), pp x i) +
        ∑ i ∈ range (k + 1), min (i : ℝ) (k : ℝ) * pp x i) := by
    refine (hasSum_nat_add_iff' (f := fun j : ℕ => min (j : ℝ) (k : ℝ) * pp x j) (k + 1)).1 ?_
    have e3 : (k : ℝ) * (1 - ∑ i ∈ range (k + 1), pp x i) +
            ∑ i ∈ range (k + 1), min (i : ℝ) (k : ℝ) * pp x i -
            ∑ i ∈ range (k + 1), min (i : ℝ) (k : ℝ) * pp x i =
            (k : ℝ) * (1 - ∑ i ∈ range (k + 1), pp x i) := by ring
    rw [e3]; exact hF
  have hmin : ∑ i ∈ range (k + 1), min (i : ℝ) (k : ℝ) * pp x i =
      ∑ i ∈ range (k + 1), (i : ℝ) * pp x i := by
    apply sum_congr rfl
    intro i hi
    have : (i : ℝ) ≤ (k : ℝ) := by
      have := mem_range.1 hi
      exact_mod_cast (by omega : i ≤ k)
    rw [min_eq_left this]
  have : expMinPois x k = ∑' j : ℕ, min (j : ℝ) (k : ℝ) * pp x j := rfl
  rw [this, hF2.tsum_eq, hmin, pp_partial x k]
  unfold SS
  ring

theorem pp_deriv (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y => pp y (j + 1)) (pp x j - pp x (j + 1)) x := by
  unfold pp
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa using (hasDerivAt_neg x).exp
  have h2 : HasDerivAt (fun y : ℝ => y ^ (j + 1)) (((j + 1 : ℕ) : ℝ) * x ^ j) x := by
    simpa using hasDerivAt_pow (j + 1) x
  have h3 := (h1.mul h2).div_const (((j + 1).factorial : ℕ) : ℝ)
  refine h3.congr_deriv ?_
  rw [Nat.factorial_succ]
  push_cast
  have : ((j.factorial : ℝ)) ≠ 0 := by positivity
  have : ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem pp_deriv0 (x : ℝ) : HasDerivAt (fun y => pp y 0) (-pp x 0) x := by
  unfold pp
  simpa using (hasDerivAt_neg x).exp

theorem SS_deriv (n : ℕ) (x : ℝ) : HasDerivAt (fun y => SS (n + 1) y) (-pp x n) x := by
  induction n with
  | zero => simpa [SS] using pp_deriv0 x
  | succ n ih =>
    have h := ih.add (pp_deriv n x)
    have e : (fun y => SS (n + 1 + 1) y) = fun y => SS (n + 1) y + pp y (n + 1) := by
      funext y; unfold SS; rw [sum_range_succ _ (n + 1)]
    rw [e]
    refine h.congr_deriv ?_
    ring

theorem solution (k : ℕ) :
    AntitoneOn (fun x : ℝ => expMinPois x k / x) (Set.Ioi 0) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro a _ b _ _
    simp [expMinPois]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  set F : ℝ → ℝ := fun x => SS (n + 1) x + ((n + 1 : ℕ) : ℝ) * (1 - SS (n + 1 + 1) x) / x with hF
  have hEq : ∀ x ∈ Set.Ioi (0 : ℝ), expMinPois x (n + 1) / x = F x := by
    intro x hx
    have hx' : 0 < x := hx
    rw [expMin_formula x hx'.le, hF]
    field_simp
  have hD : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt F (-(((n + 1 : ℕ) : ℝ) * (1 - SS (n + 1 + 1) x) / x ^ 2)) x := by
    intro x hx
    have hx' : 0 < x := hx
    have hS1 := SS_deriv n x
    have hS2 := SS_deriv (n + 1) x
    have h4 : HasDerivAt (fun y => ((n + 1 : ℕ) : ℝ) * (1 - SS (n + 1 + 1) y))
        (((n + 1 : ℕ) : ℝ) * (0 - (-pp x (n + 1)))) x :=
      ((hasDerivAt_const x (1 : ℝ)).sub hS2).const_mul _
    have h5 := h4.div (hasDerivAt_id x) hx'.ne'
    have h6 := hS1.add h5
    have hrec := pp_rec x n
    refine h6.congr_deriv ?_
    simp only [id]
    have e : ((n + 1 : ℕ) : ℝ) * (0 - -pp x (n + 1)) * x = x ^ 2 * pp x n := by
      calc ((n + 1 : ℕ) : ℝ) * (0 - -pp x (n + 1)) * x
          = (((n + 1 : ℕ) : ℝ) * pp x (n + 1)) * x := by ring
        _ = x ^ 2 * pp x n := by rw [hrec]; ring
    rw [e]
    field_simp
    ring
  have hanti : AntitoneOn F (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro x hx; exact (hD x hx).continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Ioi] at hx; exact (hD x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      rw [(hD x hx).deriv]
      have hx' : 0 < x := hx
      have := SS_le_one x hx'.le (n + 1 + 1)
      have : 0 ≤ ((n + 1 : ℕ) : ℝ) * (1 - SS (n + 1 + 1) x) / x ^ 2 := by
        apply div_nonneg
        · apply mul_nonneg (by positivity); linarith
        · positivity
      linarith
  intro a ha b hb hab
  show expMinPois b (n + 1) / b ≤ expMinPois a (n + 1) / a
  rw [hEq a ha, hEq b hb]
  exact hanti ha hb hab
