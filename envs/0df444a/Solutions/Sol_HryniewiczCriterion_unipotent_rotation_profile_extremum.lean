-- Prove2me | solution 1 for HryniewiczCriterion.unipotent_rotation_profile_extremum
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T20:40:33.20842+00:00
-- url     : https://prove2.me/submissions/7adc4c58-1074-46bf-84c0-7088d31a7097

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

open HryniewiczCriterion Set
set_option maxHeartbeats 800000

theorem solution
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det = 1)
    (hdeg : (A - 1).det = 0) (Δ : ℝ → ℝ) (hΔ : Continuous Δ)
    (hpolar : ∀ s : ℝ, ∃ r : ℝ, 0 < r ∧
      A.mulVec (rotationVector s) = r • rotationVector (s + 2 * Real.pi * Δ s)) :
    ∃ k : ℤ, IsLeast (Set.range Δ) (k : ℝ) ∨
      IsGreatest (Set.range Δ) (k : ℝ) := by
  have htr : A 0 0 + A 1 1 = 2 := by
    simp only [Matrix.det_fin_two] at hA hdeg
    simp only [Matrix.sub_apply, Matrix.one_apply, Fin.zero_ne_one,
      Ne.symm Fin.zero_ne_one, if_true, if_false, sub_zero] at hdeg
    nlinarith
  have hbc : A 0 1 * A 1 0 = -(A 0 0 - 1)^2 := by
    simp only [Matrix.det_fin_two] at hA
    linear_combination A 0 0 * htr - hA
  let q : ℝ → ℝ := fun s =>
    Real.cos s * (A.mulVec (rotationVector s) 1) -
      Real.sin s * (A.mulVec (rotationVector s) 0)
  have hq (s : ℝ) : q s =
      A 1 0 * Real.cos s ^ 2 + (A 1 1 - A 0 0) * Real.cos s * Real.sin s -
        A 0 1 * Real.sin s ^ 2 := by
    simp [q, rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hsquare (s : ℝ) : A 0 1 * q s =
      -((A 0 0 - 1) * Real.cos s + A 0 1 * Real.sin s)^2 := by
    rw [hq]
    linear_combination (Real.cos s)^2 * hbc +
      A 0 1 * Real.cos s * Real.sin s * htr
  have hsign : (∀ s, 0 ≤ q s) ∨ (∀ s, q s ≤ 0) := by
    rcases lt_trichotomy (A 0 1) 0 with hb | hb | hb
    · left
      intro s
      have := hsquare s
      nlinarith [sq_nonneg ((A 0 0 - 1) * Real.cos s + A 0 1 * Real.sin s)]
    · have ha : A 0 0 = 1 := by rw [hb] at hbc; nlinarith [sq_nonneg (A 0 0 - 1)]
      have hd : A 1 1 = 1 := by linarith
      rcases le_total 0 (A 1 0) with hc | hc
      · left
        intro s
        rw [hq, ha, hd, hb]
        nlinarith [mul_nonneg hc (sq_nonneg (Real.cos s))]
      · right
        intro s
        rw [hq, ha, hd, hb]
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg (Real.cos s))]
    · right
      intro s
      have := hsquare s
      nlinarith [sq_nonneg ((A 0 0 - 1) * Real.cos s + A 0 1 * Real.sin s)]
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdeg
  have hfix : A.mulVec v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hker
    exact hker
  let z : ℂ := ⟨v 0, v 1⟩
  have hz : z ≠ 0 := by
    intro h
    apply hv
    ext i
    fin_cases i
    · exact congrArg Complex.re h
    · exact congrArg Complex.im h
  let s₀ := Complex.arg z
  have hvpolar : v = ‖z‖ • rotationVector s₀ := by
    ext i
    fin_cases i <;>
      simp [rotationVector, s₀, z, Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
  have hdir : A.mulVec (rotationVector s₀) = rotationVector s₀ := by
    rw [hvpolar, Matrix.mulVec_smul] at hfix
    ext i
    exact mul_left_cancel₀ (ne_of_gt (norm_pos_iff.mpr hz)) (congrFun hfix i)
  obtain ⟨r, hr, hvec⟩ := hpolar s₀
  rw [hdir] at hvec
  have hc := congrFun hvec 0
  have hs := congrFun hvec 1
  simp only [rotationVector, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.smul_apply, smul_eq_mul] at hc hs
  have hr2 : r^2 = 1 := by
    have hsq : Real.cos s₀^2 + Real.sin s₀^2 =
        r^2 * (Real.cos (s₀ + 2 * Real.pi * Δ s₀)^2 +
          Real.sin (s₀ + 2 * Real.pi * Δ s₀)^2) := by rw [hc, hs]; ring
    rw [Real.cos_sq_add_sin_sq, Real.cos_sq_add_sin_sq, mul_one] at hsq
    exact hsq.symm
  have hr1 : r = 1 := by nlinarith
  rw [hr1, one_mul] at hc hs
  have hcos : Real.cos (2 * Real.pi * Δ s₀) = 1 := by
    have h := Real.cos_sub (s₀ + 2 * Real.pi * Δ s₀) s₀
    rw [← hc, ← hs] at h
    have ha : s₀ + 2 * Real.pi * Δ s₀ - s₀ = 2 * Real.pi * Δ s₀ := by ring
    rw [ha] at h
    nlinarith [Real.cos_sq_add_sin_sq s₀]
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
  have hΔ0 : Δ s₀ = k := by nlinarith [Real.pi_pos]
  have hsin (s : ℝ) : ∃ r : ℝ, 0 < r ∧
      q s = r * Real.sin (2 * Real.pi * Δ s) := by
    obtain ⟨r, hr, he⟩ := hpolar s
    refine ⟨r, hr, ?_⟩
    dsimp [q]
    rw [he]
    simp only [rotationVector, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hh := Real.sin_sub (s + 2 * Real.pi * Δ s) s
    have ha : s + 2 * Real.pi * Δ s - s = 2 * Real.pi * Δ s := by ring
    rw [ha] at hh
    rw [hh]
    ring
  have hleast (f : ℝ → ℝ) (hf : Continuous f) (u : ℝ) (n : ℤ)
      (hu : f u = n) (hpos : ∀ s, 0 ≤ Real.sin (2 * Real.pi * f s)) :
      IsLeast (Set.range f) (n : ℝ) := by
    refine ⟨⟨u, hu⟩, ?_⟩
    rintro _ ⟨t, rfl⟩
    by_contra! ht
    let e : ℝ := min (((n : ℝ) - f t) / 2) (1 / 4)
    have he : 0 < e := lt_min (by linarith) (by norm_num)
    have he₁ : e ≤ ((n : ℝ) - f t) / 2 := min_le_left _ _
    have he₂ : e ≤ 1 / 4 := min_le_right _ _
    obtain ⟨w, hw⟩ := intermediate_value_univ t u hf
      (show (n : ℝ) - e ∈ Set.Icc (f t) (f u) from by rw [hu]; constructor <;> linarith)
    have hp := hpos w
    rw [hw] at hp
    have hid : 2 * Real.pi * ((n : ℝ) - e) = (-2 * Real.pi * e) + n * (2 * Real.pi) := by ring
    rw [hid, Real.sin_add_int_mul_two_pi] at hp
    have hneg : -2 * Real.pi * e = -(2 * Real.pi * e) := by ring
    rw [hneg, Real.sin_neg] at hp
    have hstrict := Real.sin_pos_of_pos_of_lt_pi
      (show 0 < 2 * Real.pi * e by positivity)
      (show 2 * Real.pi * e < Real.pi by nlinarith [Real.pi_pos])
    linarith
  refine ⟨k, ?_⟩
  rcases hsign with hsign | hsign
  · left
    apply hleast Δ hΔ s₀ k hΔ0
    intro s
    obtain ⟨r, hr, he⟩ := hsin s
    have hq := hsign s
    rw [he] at hq
    exact (mul_nonneg_iff_of_pos_left hr).mp hq
  · right
    have hn : IsLeast (Set.range (fun s => -Δ s)) ((-k : ℤ) : ℝ) := by
      apply hleast (fun s => -Δ s) hΔ.neg s₀ (-k) (by simp [hΔ0])
      intro s
      obtain ⟨r, hr, he⟩ := hsin s
      have hq := hsign s
      rw [he] at hq
      have hh : Real.sin (2 * Real.pi * Δ s) ≤ 0 :=
        by nlinarith
      simpa using neg_nonneg.mpr hh
    refine ⟨⟨s₀, hΔ0⟩, ?_⟩
    rintro _ ⟨s, rfl⟩
    have hh := hn.2 (Set.mem_range_self s)
    simpa using hh



