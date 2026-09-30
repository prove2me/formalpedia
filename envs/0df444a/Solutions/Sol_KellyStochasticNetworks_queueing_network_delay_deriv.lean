-- Prove2me | solution 1 for KellyStochasticNetworks.queueing_network_delay_deriv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T22:37:21.638006+00:00
-- url     : https://prove2.me/submissions/087fb5a8-6a35-491f-9577-0cd9ae897064

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

open KellyStochasticNetworks

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℝ) (w ν : Fin R → ℝ)
    (φ : Fin J → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hstab : ∀ j, (∑ r', A j r' * ν r') < φ j) (r : Fin R) :
    HasDerivAt (fun t : ℝ => queueingCost A w (Function.update ν r t) φ)
      (∑ j, A j r * (w r / (φ j - ∑ r', A j r' * ν r')
        + ∑ r', A j r' * (ν r' * w r') / (φ j - ∑ r'', A j r'' * ν r'') ^ 2))
      (ν r) := by
  classical
  set u : ℝ → Fin R → ℝ := fun t => Function.update ν r t with hu_def
  have hu0 : u (ν r) = ν := by simp [hu_def]
  have hu : ∀ r', HasDerivAt (fun t => u t r') (if r' = r then 1 else 0) (ν r) := by
    intro r'
    by_cases h : r' = r
    · subst h; simpa [hu_def] using hasDerivAt_id' (x := ν r')
    · simpa [hu_def, Function.update_of_ne h, h] using hasDerivAt_const (ν r) (ν r')
  set L : Fin J → ℝ := fun j => ∑ r', A j r' * ν r' with hL
  have hlam : ∀ j, HasDerivAt (fun t => ∑ r', A j r' * u t r') (A j r) (ν r) := by
    intro j
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun r' _ => (hu r').const_mul (A j r'))
    refine this.congr_deriv ?_
    simp [mul_ite]
  have hden : ∀ j, HasDerivAt (fun t => φ j - ∑ r', A j r' * u t r') (-A j r) (ν r) := by
    intro j; exact (hlam j).const_sub (φ j)
  have hne : ∀ j, φ j - ∑ r', A j r' * u (ν r) r' ≠ 0 := by
    intro j; rw [hu0]; linarith [hstab j]
  have hterm : ∀ r'' j, HasDerivAt (fun t => u t r'' / (φ j - ∑ r', A j r' * u t r'))
      (((if r'' = r then 1 else 0) * (φ j - L j) - ν r'' * (-A j r)) / (φ j - L j) ^ 2) (ν r) := by
    intro r'' j
    have := (hu r'').fun_div (hden j) (hne j)
    simpa [hu0, hL] using this
  have hall := HasDerivAt.fun_sum (u := Finset.univ) (fun r'' _ =>
    (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hterm r'' j).const_mul (A j r''))).const_mul
      (w r''))
  unfold queueingCost
  refine hall.congr_deriv ?_
  have hpos : ∀ j, φ j - L j ≠ 0 := fun j => by simp only [hL]; linarith [hstab j]
  -- rewrite each summand
  have key : ∀ r'' j, A j r'' * (((if r'' = r then 1 else 0) * (φ j - L j) - ν r'' * (-A j r))
      / (φ j - L j) ^ 2)
      = (if r'' = r then A j r / (φ j - L j) else 0) + A j r * (A j r'' * ν r'') / (φ j - L j) ^ 2 := by
    intro r'' j
    have h := hpos j
    split_ifs with hr
    · subst hr; field_simp; ring
    · field_simp; ring
  simp_rw [key, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  · ring
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by simp only [hL]; ring

