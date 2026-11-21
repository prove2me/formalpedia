-- Prove2me | solution 1 for MomentSearch.rakhmanov_weighted_grid_basis
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:20:32.613288+00:00
-- url     : https://prove2.me/submissions/f7ba9f39-5858-43f8-9956-a40c1dc2dedb

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_midpoint_nodal_envelope

theorem solution :
    ∃ A : ℝ, 0 < A ∧
      ∀ N : ℕ, 0 < N →
      let ζ : ℕ → ℝ := fun j => -1 + (2 * (j : ℝ) - 1) / (N : ℝ)
      let w : ℝ → ℝ := fun z => Real.exp (-(N : ℝ) / 2 *
        ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ j ∈ Finset.Icc 1 N,
        |(Lagrange.basis (Finset.Icc 1 N) ζ j).eval x| ≤
          A * (w (ζ j) / w x) / max 1 ((N : ℝ) * |ζ j - x|) := by
  refine ⟨2, by norm_num, ?_⟩
  intro N hN ζ w x hx j hj
  let s : Finset ℕ := Finset.Icc 1 N
  have hjs : j ∈ s := hj
  let T := Lagrange.nodal s ζ
  let b : ℝ := Real.pi * N / 2
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hbN : (N : ℝ) ≤ b := by
    have hp : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
    calc
      (N : ℝ) = (N : ℝ) * 1 := by ring
      _ ≤ (N : ℝ) * (Real.pi / 2) := mul_le_mul_of_nonneg_left hp hNr.le
      _ = b := by dsimp [b]; ring
  have hb : 0 < b := hNr.trans_le hbN
  have hw (u : ℝ) : 0 < w u := Real.exp_pos _
  have hinj : Set.InjOn ζ ↑s := by
    intro i _ k _ hik
    change -1 + (2 * (i : ℝ) - 1) / (N : ℝ) =
      -1 + (2 * (k : ℝ) - 1) / (N : ℝ) at hik
    have hh : (2 * (i : ℝ) - 1) / (N : ℝ) = (2 * (k : ℝ) - 1) / (N : ℝ) := by
      linarith
    have hh' := congrArg (fun z : ℝ => z * (N : ℝ)) hh
    simp only [div_mul_cancel₀ _ hNr.ne'] at hh'
    have heq : (i : ℝ) = (k : ℝ) := by linarith
    exact_mod_cast heq
  by_cases hnode : x = ζ j
  · rw [hnode, Lagrange.eval_basis_self hinj hj, sub_self, abs_zero, mul_zero,
      max_eq_left zero_le_one, div_self (hw _).ne']
    norm_num
  obtain ⟨c, hc, hT, hTd⟩ := MomentSearch.rakhmanov_midpoint_nodal_envelope N hN
  let d : ℝ := |x - ζ j|
  let e : ℝ := |T.derivative.eval (ζ j)|
  let R : ℝ := w (ζ j) / w x
  let u : ℝ := |(Lagrange.basis s ζ j).eval x|
  have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hnode)
  have hR : 0 < R := div_pos (hw _) (hw _)
  have he : 0 < e := (div_pos (mul_pos hc hb) (hw _)).trans_le (hTd j hj)
  have hder : c * b / w (ζ j) ≤ e := hTd j hj
  have hg : u * (e * d) = |T.eval x| := by
    dsimp [u, e, d, T]
    rw [Lagrange.eval_basis_not_at_node hjs hnode, Lagrange.nodalWeight_eq_eval_derivative_nodal hjs]
    simp only [abs_mul, abs_inv]
    field_simp [(abs_pos.mpr (sub_ne_zero.mpr hnode)).ne', he.ne']
    exact mul_div_cancel_right₀ _ he.ne'
  have hphase : b * (ζ j + 1) = (j : ℝ) * Real.pi - Real.pi / 2 := by
    change (Real.pi * (N : ℝ) / 2) * ((-1 + (2 * (j : ℝ) - 1) / (N : ℝ)) + 1) = _
    field_simp
    ring
  have hcos0 : Real.cos (b * (ζ j + 1)) = 0 := by
    rw [hphase, Real.cos_nat_mul_pi_sub, Real.cos_pi_div_two, mul_zero]
  let a := |Real.cos (b * (x + 1))|
  have ha0 : 0 ≤ a := abs_nonneg _
  have ha1 : a ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hac : a ≤ b * d := by
    have hh := Real.abs_cos_sub_cos_le (b * (x + 1)) (b * (ζ j + 1))
    rw [hcos0, sub_zero, ← mul_sub, show x + 1 - (ζ j + 1) = x - ζ j by ring,
      abs_mul, abs_of_pos hb] at hh
    exact hh
  have hu : u ≤ (2 * R) * (a / (b * d)) := by
    apply (mul_le_mul_iff_left₀ (mul_pos he hd)).mp
    calc
      u * (e * d) = |T.eval x| := hg
      _ ≤ 2 * c * a / w x := hT x hx
      _ = ((2 * R) * (a / (b * d))) * ((c * b / w (ζ j)) * d) := by
        dsimp [R]
        field_simp [(hw x).ne', (hw (ζ j)).ne', hb.ne', hd.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hder hd.le)
        (mul_nonneg (by positivity) (div_nonneg ha0 (mul_nonneg hb.le hd.le)))
  have hu1 : u ≤ 2 * R :=
    hu.trans (mul_le_of_le_one_right (by positivity) ((div_le_one (mul_pos hb hd)).2 hac))
  have hu2 : u ≤ (2 * R) / ((N : ℝ) * d) := by
    calc
      u ≤ (2 * R) * (a / (b * d)) := hu
      _ ≤ (2 * R) * (1 / (b * d)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ha1 (by positivity)) (by positivity)
      _ ≤ (2 * R) * (1 / ((N : ℝ) * d)) :=
        mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (mul_pos hNr hd) (mul_le_mul_of_nonneg_right hbN hd.le))
          (by positivity)
      _ = _ := by ring
  change u ≤ (2 * R) / max 1 ((N : ℝ) * |ζ j - x|)
  rw [abs_sub_comm (ζ j) x]
  change u ≤ (2 * R) / max 1 ((N : ℝ) * d)
  rcases le_total ((N : ℝ) * d) 1 with h | h
  · rwa [max_eq_left h, div_one]
  · rwa [max_eq_right h]
