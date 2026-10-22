-- Prove2me | solution 1 for KellyLossNetworks.Primal.complementary_suffices
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:30:57.248784+00:00
-- url     : https://prove2.me/submissions/a0037963-329e-44e0-8bce-74b97a22b670

import Mathlib
import Definitions.Def_KellyLossNetworks_Primal_Problem

set_option autoImplicit false
open KellyLossNetworks.Primal

namespace KLPHelp
open KellyLossNetworks.Primal

theorem term_le (ν a t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    t * Real.log ν - t * a - t * Real.log t + t ≤ ν * Real.exp (-a) := by
  have hw : 0 < ν * Real.exp (-a) := mul_pos hν (Real.exp_pos _)
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0; simpa using hw.le
  · have hlogw : Real.log (ν * Real.exp (-a)) = Real.log ν - a := by
      rw [Real.log_mul hν.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    have h1 : Real.log ((ν * Real.exp (-a)) / t) ≤ (ν * Real.exp (-a)) / t - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hw hpos)
    rw [Real.log_div hw.ne' hpos.ne', hlogw] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    have h3 : t * ((ν * Real.exp (-a)) / t - 1) = ν * Real.exp (-a) - t := by
      field_simp
    nlinarith

theorem term_eq (ν a : ℝ) (hν : 0 < ν) :
    (ν * Real.exp (-a)) * Real.log ν - (ν * Real.exp (-a)) * a
      - (ν * Real.exp (-a)) * Real.log (ν * Real.exp (-a)) + ν * Real.exp (-a)
      = ν * Real.exp (-a) := by
  rw [Real.log_mul hν.ne' (Real.exp_pos _).ne', Real.log_exp]; ring

theorem lag_eq {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℕ)
    (x : Fin R → ℝ) (z y : Fin J → ℝ) :
    lagrangian A ν C x z y =
      (∑ r, (x r * Real.log (ν r) - x r * (∑ j, y j * (A j r : ℝ))
        - x r * Real.log (x r) + x r)) + ∑ j, y j * (C j : ℝ) - ∑ j, y j * z j := by
  unfold lagrangian primalObjective
  have h : ∑ j, y j * (∑ r, (A j r : ℝ) * x r) = ∑ r, x r * (∑ j, y j * (A j r : ℝ)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j, y j * ((C j : ℝ) - ∑ r, (A j r : ℝ) * x r - z j)
      = ∑ j, y j * (C j : ℝ) - ∑ j, y j * (∑ r, (A j r : ℝ) * x r) - ∑ j, y j * z j := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  have h3 : ∑ r, (x r * Real.log (ν r) - x r * (∑ j, y j * (A j r : ℝ))
        - x r * Real.log (x r) + x r) = ∑ r, (x r * Real.log (ν r) - x r * Real.log (x r) + x r)
        - ∑ r, x r * (∑ j, y j * (A j r : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [h2, h, h3]
  ring

theorem lag_le {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℕ)
    (hν : ∀ r, 0 < ν r) (y : Fin J → ℝ) (hy : ∀ j, 0 ≤ y j)
    (x : Fin R → ℝ) (z : Fin J → ℝ) (hx : ∀ r, 0 ≤ x r) (hz : ∀ j, 0 ≤ z j) :
    lagrangian A ν C x z y ≤ KellyStochasticNetworks.dualObjective A ν C y := by
  rw [lag_eq]
  unfold KellyStochasticNetworks.dualObjective
  have h1 : ∑ r, (x r * Real.log (ν r) - x r * (∑ j, y j * (A j r : ℝ))
        - x r * Real.log (x r) + x r) ≤ ∑ r, ν r * Real.exp (-∑ j, y j * (A j r : ℝ)) :=
    Finset.sum_le_sum fun r _ => term_le _ _ _ (hν r) (hx r)
  have h2 : 0 ≤ ∑ j, y j * z j := Finset.sum_nonneg fun j _ => mul_nonneg (hy j) (hz j)
  linarith

theorem lag_at {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℕ)
    (hν : ∀ r, 0 < ν r) (y : Fin J → ℝ) :
    lagrangian A ν C (primalPoint A ν y) (fun _ => 0) y
      = KellyStochasticNetworks.dualObjective A ν C y := by
  rw [lag_eq]
  unfold KellyStochasticNetworks.dualObjective primalPoint
  have h1 : ∑ r, (ν r * Real.exp (-∑ j, y j * (A j r : ℝ)) * Real.log (ν r)
      - ν r * Real.exp (-∑ j, y j * (A j r : ℝ)) * (∑ j, y j * (A j r : ℝ))
      - ν r * Real.exp (-∑ j, y j * (A j r : ℝ)) * Real.log (ν r * Real.exp (-∑ j, y j * (A j r : ℝ)))
      + ν r * Real.exp (-∑ j, y j * (A j r : ℝ))) = ∑ r, ν r * Real.exp (-∑ j, y j * (A j r : ℝ)) :=
    Finset.sum_congr rfl fun r _ => term_eq _ _ (hν r)
  rw [h1]
  simp

theorem B_nonneg_iff (y : ℝ) : 0 ≤ 1 - Real.exp (-y) ↔ 0 ≤ y := by
  constructor
  · intro h
    by_contra hy
    push Not at hy
    have : 1 < Real.exp (-y) := Real.one_lt_exp_iff.mpr (by linarith)
    linarith
  · intro h
    have : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith

theorem B_pos_iff (y : ℝ) : 0 < 1 - Real.exp (-y) ↔ 0 < y := by
  constructor
  · intro h
    by_contra hy
    push Not at hy
    have : 1 ≤ Real.exp (-y) := Real.one_le_exp (by linarith)
    linarith
  · intro h
    have : Real.exp (-y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith

theorem prod_eq {J R : ℕ} (A : Fin J → Fin R → ℕ) (y : Fin J → ℝ) (r : Fin R) :
    ∏ i, (1 - blockingFromDual y i) ^ (A i r) = Real.exp (-∑ j, y j * (A j r : ℝ)) := by
  unfold blockingFromDual
  simp only [sub_sub_cancel]
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem cov {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (y : Fin J → ℝ) :
    complementary A ν C y ↔ ConditionsOnB A ν C (blockingFromDual y) := by
  have hs : ∀ j, (∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - blockingFromDual y i) ^ (A i r))
      = ∑ r, (A j r : ℝ) * primalPoint A ν y r := by
    intro j
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [prod_eq, primalPoint]; ring
  have hB : ∀ j, blockingFromDual y j = 1 - Real.exp (-y j) := fun j => rfl
  unfold ConditionsOnB complementary
  simp_rw [hs, hB]
  constructor
  · rintro ⟨hy, hle, hsum⟩
    have hterm : ∀ j, y j * ((C j : ℝ) - ∑ r, (A j r : ℝ) * primalPoint A ν y r) = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hy j) (sub_nonneg.mpr (hle j)))).mp hsum
      intro j; exact this j (Finset.mem_univ j)
    refine ⟨fun j => ⟨(B_nonneg_iff _).mpr (hy j), by have := Real.exp_pos (-y j); linarith⟩, fun j => ⟨fun hj => ?_, fun _ => hle j⟩⟩
    have hyj : 0 < y j := (B_pos_iff _).mp hj
    have := hterm j
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hyj.ne'
    · linarith
  · rintro ⟨hB1, hB2⟩
    have hy : ∀ j, 0 ≤ y j := fun j => (B_nonneg_iff _).mp (hB1 j).1
    have hle : ∀ j, (∑ r, (A j r : ℝ) * primalPoint A ν y r) ≤ (C j : ℝ) := by
      intro j
      rcases ((hB1 j).1).eq_or_lt with h0 | hpos
      · exact (hB2 j).2 h0.symm
      · exact ((hB2 j).1 hpos).le
    refine ⟨hy, hle, ?_⟩
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases (hy j).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have := (hB2 j).1 ((B_pos_iff _).mpr hpos)
      rw [this]; simp

theorem lag_feas {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℕ)
    (x : Fin R → ℝ) (y : Fin J → ℝ) :
    lagrangian A ν C x (fun j => (C j : ℝ) - ∑ r, (A j r : ℝ) * x r) y = primalObjective ν x := by
  unfold lagrangian
  simp

theorem cs {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r)
    (y : Fin J → ℝ) (h : complementary A ν C y) :
    (primalPoint A ν y ∈ primalFeasible A C ∧
      IsMaxOn (primalObjective ν) (primalFeasible A C) (primalPoint A ν y)) ∧
    IsDualOpt A ν C y := by
  obtain ⟨hy, hle, hsum⟩ := h
  have hxb : ∀ r, 0 ≤ primalPoint A ν y r := fun r => (mul_pos (hν r) (Real.exp_pos _)).le
  have hfeas : primalPoint A ν y ∈ primalFeasible A C := ⟨hxb, hle⟩
  have hzb : ∀ j, 0 ≤ (C j : ℝ) - ∑ r, (A j r : ℝ) * primalPoint A ν y r :=
    fun j => sub_nonneg.mpr (hle j)
  have hval : primalObjective ν (primalPoint A ν y) = KellyStochasticNetworks.dualObjective A ν C y := by
    rw [← lag_feas A ν C (primalPoint A ν y) y, ← lag_at A ν C hν y, lag_eq, lag_eq]
    have : ∑ j, y j * ((C j : ℝ) - ∑ r, (A j r : ℝ) * primalPoint A ν y r) = 0 := hsum
    simp only [Finset.sum_const_zero, mul_zero, sub_zero, this]
  refine ⟨⟨hfeas, ?_⟩, hy, ?_⟩
  · intro x hx
    have hx' : x ∈ primalFeasible A C := hx
    have : primalObjective ν x ≤ KellyStochasticNetworks.dualObjective A ν C y := by
      rw [← lag_feas A ν C x y]
      exact lag_le A ν C hν y hy x _ hx'.1 (fun j => sub_nonneg.mpr (hx'.2 j))
    show primalObjective ν x ≤ primalObjective ν (primalPoint A ν y)
    rw [hval]; exact this
  · intro z hz
    rw [← hval, ← lag_feas A ν C (primalPoint A ν y) z]
    exact lag_le A ν C hν z hz _ _ hxb hzb

end KLPHelp

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r)
    (y : Fin J → ℝ) (h : complementary A ν C y) :
    (primalPoint A ν y ∈ primalFeasible A C ∧
      IsMaxOn (primalObjective ν) (primalFeasible A C) (primalPoint A ν y)) ∧
    IsDualOpt A ν C y :=
  KLPHelp.cs A ν C hν y h
