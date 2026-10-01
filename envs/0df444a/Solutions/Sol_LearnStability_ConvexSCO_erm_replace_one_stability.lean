-- Prove2me | solution 1 for LearnStability.ConvexSCO.erm_replace_one_stability
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:45:32.918188+00:00
-- url     : https://prove2.me/submissions/c6f3c6d6-d585-49d4-b621-4b3c389b12f8

import Definitions.Def_LearnStability_ConvexSCO_Problem
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
open LearnStability.ConvexSCO

private theorem growth {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {H : Set E} {f : E → Z → ℝ} {lam : ℝ}
    (hcv : Convex ℝ H) (hsc : ∀ z, StrongConvexOn H lam (fun h => f h z))
    {m : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) {x y : E} (hx : x∈H) (hy : y∈H)
    (hmin : ∀ z∈H, empRisk f S x ≤ empRisk f S z) :
    lam/4*(m : ℝ)*‖x-y‖^2 ≤ (∑ i, f y (S i))-(∑ i, f x (S i)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmid : (1/2 : ℝ) • x+(1/2 : ℝ) • y∈H :=
    hcv hx hy (by norm_num) (by norm_num) (by norm_num)
  have hmin' := (div_le_div_iff_of_pos_right hm0).mp (hmin _ hmid)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i∈Finset.univ) =>
    (hsc (S i)).2 hx hy (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num))
  simp only [smul_eq_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  nlinarith

private theorem sum_replacement {Z E : Type*} {f : E → Z → ℝ} {m : ℕ}
    (S : Fin m → Z) (i : Fin m) (z : Z) (h : E) :
    (∑ j, f h (Function.update S i z j))-(∑ j, f h (S j)) = f h z-f h (S i) := by
  classical
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

theorem solution {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {Hset : Set E} {f : E → Z → ℝ} {L C lam : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (hlam : 0 < lam)
    (hsc : ∀ z, StrongConvexOn Hset lam (fun h => f h z))
    {m : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) (i : Fin m) (z'_i : Z) {hS hSi : E}
    (hS_mem : hS ∈ Hset) (hS_min : ∀ h ∈ Hset, empRisk f S hS ≤ empRisk f S h)
    (hSi_mem : hSi ∈ Hset)
    (hSi_min : ∀ h ∈ Hset,
      empRisk f (Function.update S i z'_i) hSi ≤ empRisk f (Function.update S i z'_i) h) :
    ∀ z : Z, |f hS z - f hSi z| ≤ 4*L^2/(lam*m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hprod : 0 < lam*(m : ℝ) := mul_pos hlam hm0
  have h1 := growth hP.convex hsc hm S hS_mem hSi_mem hS_min
  have h2 := growth hP.convex hsc hm (Function.update S i z'_i) hSi_mem hS_mem hSi_min
  rw [norm_sub_rev hSi hS] at h2
  have h3 := sum_replacement (f := f) S i z'_i hS
  have h4 := sum_replacement (f := f) S i z'_i hSi
  have h5 := (le_abs_self (f hS z'_i-f hSi z'_i)).trans (hP.lipschitz z'_i hS hS_mem hSi hSi_mem)
  have h6 := (neg_le_abs (f hS (S i)-f hSi (S i))).trans (hP.lipschitz (S i) hS hS_mem hSi hSi_mem)
  have hh : lam*(m : ℝ)*‖hS-hSi‖^2 ≤ 4*L*‖hS-hSi‖ := by nlinarith
  have hd : ‖hS-hSi‖ ≤ 4*L/(lam*m) := by
    rcases eq_or_lt_of_le (norm_nonneg (hS-hSi)) with hzero | hpos
    · rw [← hzero]
      exact div_nonneg (mul_nonneg (by norm_num) hP.lipschitz_nonneg) hprod.le
    · apply (le_div_iff₀ hprod).mpr
      have hlin : (lam*(m : ℝ)*‖hS-hSi‖)*‖hS-hSi‖ ≤ (4*L)*‖hS-hSi‖ := by nlinarith [hh]
      have hc := le_of_mul_le_mul_right hlin hpos
      nlinarith
  intro z
  apply (hP.lipschitz z hS hS_mem hSi hSi_mem).trans
  calc
    _ ≤ L*(4*L/(lam*m)) := mul_le_mul_of_nonneg_left hd hP.lipschitz_nonneg
    _ = _ := by ring

