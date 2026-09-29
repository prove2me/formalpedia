-- Prove2me | solution 1 for GiuntiStudenikin2015.oscillation_probability
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T09:32:01.128053+00:00
-- url     : https://prove2.me/submissions/c37c4fb4-ae80-44ed-94eb-91f225ccb2f7

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem gs15_exp_neg (φ : ℝ) :
    Complex.exp (-(Complex.I * (φ : ℂ))) = (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I := by
  rw [show -(Complex.I * (φ : ℂ)) = ((-φ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem gs15_unit (φ : ℝ) :
    Complex.exp (-(Complex.I * (φ : ℂ))) * (starRingEnd ℂ) (Complex.exp (-(Complex.I * (φ : ℂ)))) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    show -(Complex.I * (φ : ℂ)) = ((-φ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem gs15_phase (a b : ℝ) :
    Complex.exp (-(Complex.I * (a : ℂ))) * (starRingEnd ℂ) (Complex.exp (-(Complex.I * (b : ℂ)))) =
      (Real.cos (a - b) : ℂ) - (Real.sin (a - b) : ℂ) * Complex.I := by
  rw [gs15_exp_neg, gs15_exp_neg, Real.cos_sub, Real.sin_sub]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im] <;> ring

theorem gs15_normSq_sum {n : ℕ} (w : Fin n → ℂ) :
    Complex.normSq (∑ k, w k) = ∑ k, ∑ j, (w k * (starRingEnd ℂ) (w j)).re := by
  have h := Complex.mul_conj (∑ k, w k)
  rw [map_sum, Finset.sum_mul_sum] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum, Complex.ofReal_re] at h2
  rw [← h2]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Complex.re_sum]

theorem gs15_sym_sum {n : ℕ} (g : Fin n → Fin n → ℝ) (hs : ∀ k j, g k j = g j k)
    (hd : ∀ k, g k k = 0) :
    ∑ k, ∑ j, g k j = ∑ k, ∑ j ∈ Finset.univ.filter (fun j => j < k), 2 * g k j := by
  have e1 : ∑ k, ∑ j, g k j =
      ∑ k, ∑ j, ((if j < k then g k j else 0) + (if k < j then g k j else 0)) := by
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    rcases lt_trichotomy j k with h | h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
    · subst h; simp [hd]
    · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add]
  have e2 : ∑ k, ∑ j, (if k < j then g k j else 0) = ∑ k, ∑ j, (if j < k then g k j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hs]
  rw [e1]
  simp only [Finset.sum_add_distrib, e2, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> ring

theorem gs15_expand {n : ℕ} (a z : Fin n → ℂ) (hz : ∀ k, z k * (starRingEnd ℂ) (z k) = 1) :
    Complex.normSq (∑ k, a k * z k) = Complex.normSq (∑ k, a k) +
      ∑ k, ∑ j ∈ Finset.univ.filter (fun j => j < k),
        2 * (a k * (starRingEnd ℂ) (a j) * (z k * (starRingEnd ℂ) (z j) - 1)).re := by
  have hsym := gs15_sym_sum (fun k j => (a k * (starRingEnd ℂ) (a j) *
    (z k * (starRingEnd ℂ) (z j) - 1)).re) (by
      intro k j
      rw [← Complex.conj_re]
      congr 1
      simp only [map_mul, map_sub, map_one, Complex.conj_conj]
      ring) (by
      intro k
      rw [hz k, sub_self, mul_zero, Complex.zero_re])
  rw [gs15_normSq_sum, gs15_normSq_sum, ← hsym, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Complex.add_re]
  congr 1
  rw [map_mul]
  ring

theorem gs15_pt (X : ℂ) (C S s : ℝ) (hC : C = 1 - 2 * s ^ 2) :
    2 * (X * ((C : ℂ) - (S : ℂ) * Complex.I - 1)).re =
      -(4 * (X.re * s ^ 2)) - 2 * (((starRingEnd ℂ) X).im * S) := by
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.mul_im, Complex.conj_im]
  rw [hC]
  ring

open GiuntiStudenikin2015 in
theorem solution {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (m : Fin n → ℝ) (L E : ℝ) (hE : 0 < E)
    (l l' : Fin n) :
    oscProb U m L E l l' =
      (if l = l' then 1 else 0)
      - 4 * ∑ k : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j < k),
          (star (U l k) * U l' k * U l j * star (U l' j)).re *
            Real.sin ((m k ^ 2 - m j ^ 2) * L / (4 * E)) ^ 2
      - 2 * ∑ k : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j < k),
          (U l k * star (U l j) * star (U l' k) * U l' j).im *
            Real.sin ((m k ^ 2 - m j ^ 2) * L / (2 * E)) := by
  have hexp := gs15_expand (fun k => star (U l k) * U l' k)
    (fun k => Complex.exp (-(Complex.I * ((m k ^ 2 * L / (2 * E) : ℝ) : ℂ))))
    (fun k => gs15_unit _)
  try simp only [] at hexp
  have hrow : ∑ k, star (U l k) * U l' k = if l' = l then 1 else 0 := by
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) l') l
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.star_apply]
    ring
  have hδ : Complex.normSq (if l' = l then (1 : ℂ) else 0) = if l = l' then 1 else 0 := by
    by_cases h : l = l'
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]; simp
  have hT : ∀ k j : Fin n,
      2 * (star (U l k) * U l' k * (starRingEnd ℂ) (star (U l j) * U l' j) *
        (Complex.exp (-(Complex.I * ((m k ^ 2 * L / (2 * E) : ℝ) : ℂ))) *
          (starRingEnd ℂ) (Complex.exp (-(Complex.I * ((m j ^ 2 * L / (2 * E) : ℝ) : ℂ)))) - 1)).re =
      -(4 * ((star (U l k) * U l' k * U l j * star (U l' j)).re *
            Real.sin ((m k ^ 2 - m j ^ 2) * L / (4 * E)) ^ 2))
        - 2 * ((U l k * star (U l j) * star (U l' k) * U l' j).im *
            Real.sin ((m k ^ 2 - m j ^ 2) * L / (2 * E))) := by
    intro k j
    have e1 : star (U l k) * U l' k * (starRingEnd ℂ) (star (U l j) * U l' j) =
        star (U l k) * U l' k * U l j * star (U l' j) := by
      simp only [map_mul, starRingEnd_apply, star_star]
      ring
    have e2 : U l k * star (U l j) * star (U l' k) * U l' j =
        (starRingEnd ℂ) (star (U l k) * U l' k * U l j * star (U l' j)) := by
      simp only [map_mul, starRingEnd_apply, star_star]
      ring
    rw [gs15_phase, e1, e2,
      show (m k ^ 2 - m j ^ 2) * L / (2 * E) = m k ^ 2 * L / (2 * E) - m j ^ 2 * L / (2 * E) by ring]
    apply gs15_pt
    rw [show m k ^ 2 * L / (2 * E) - m j ^ 2 * L / (2 * E) =
      2 * ((m k ^ 2 - m j ^ 2) * L / (4 * E)) by ring, Real.cos_two_mul_eq_one_sub]
  unfold oscProb
  rw [show (∑ k, star (U l k) * Complex.exp (-(Complex.I * ((m k ^ 2 * L / (2 * E) : ℝ) : ℂ))) *
      U l' k) = ∑ k, star (U l k) * U l' k *
        Complex.exp (-(Complex.I * ((m k ^ 2 * L / (2 * E) : ℝ) : ℂ))) from
      Finset.sum_congr rfl (fun k _ => by ring)]
  rw [hexp, hrow, hδ]
  simp only [hT, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring
