-- Prove2me | solution 1 for Kyprianou.Ch05.slowlyVaryingAtInfinity_rpow
-- status  : ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-27T05:44:04.552628+00:00
-- url     : https://prove2.me/submissions/9f1c97b0-5500-4b4a-8eda-0e972c6e5c84

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05 Set

/-- H1: a continuous slowly varying function is dominated by every power
at infinity. Dyadic comparison at a = 2, with the ratio bounds from slow
variation and boundedness on the compact [X, 2X] from continuity.
Continuity is essential: a spike on one compact interval satisfies all
ratio bounds but is not o(x^eps). -/
theorem solution
    (L : Real → Real)
    (hpos : ∀ x : Real, 0 < x → 0 < L x)
    (hslow : ∀ a : Real, 0 < a →
      Tendsto (fun x : Real => L (a * x) / L x) atTop (nhds 1))
    (hcont : ContinuousOn L (Set.Ioi (0 : Real))) :
    ∀ eps : Real, 0 < eps →
      Tendsto (fun x : Real => L x / x ^ eps) atTop (nhds 0) ∧
      Tendsto (fun x : Real => L x * x ^ eps) atTop atTop := by
  intro eps heps
  -- Dyadic decomposition: for x >= X >= 1, with n = log2 floor(x/X),
  -- y = x / 2^n lies in [X, 2X) and x = 2^n * y.
  have hdyad : ∀ X : Real, 1 ≤ X → ∀ x : Real, X ≤ x →
      let n := Nat.log 2 ⌊x / X⌋₊
      (x / (2 : Real) ^ n) ∈ Set.Ico X (2 * X) ∧ x = (2 : Real) ^ n * (x / (2 : Real) ^ n) := by
    intro X hX x hx
    have hXpos : (0 : Real) < X := by linarith
    have hdiv : (1 : Real) ≤ x / X := by
      rw [le_div_iff₀ hXpos]
      linarith
    have hm : 1 ≤ ⌊x / X⌋₊ := Nat.le_floor (by exact_mod_cast hdiv)
    have hmn : ⌊x / X⌋₊ ≠ 0 := by omega
    have hpow : (2 : ℕ) ^ Nat.log 2 ⌊x / X⌋₊ ≤ ⌊x / X⌋₊ :=
      Nat.pow_log_le_self 2 hmn
    have hlt : ⌊x / X⌋₊ < (2 : ℕ) ^ (Nat.log 2 ⌊x / X⌋₊ + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have h2n : (0 : Real) < (2 : Real) ^ Nat.log 2 ⌊x / X⌋₊ :=
      pow_pos (by norm_num : (0 : Real) < 2) _
    constructor
    · constructor
      · -- X <= x / 2^n
        rw [le_div_iff₀ h2n]
        have h1 : ((2 : ℕ) ^ Nat.log 2 ⌊x / X⌋₊ : Real) ≤ x / X := by
          calc ((2 : ℕ) ^ Nat.log 2 ⌊x / X⌋₊ : Real)
              ≤ (⌊x / X⌋₊ : Real) := by exact_mod_cast hpow
            _ ≤ x / X := Nat.floor_le (by positivity)
        rw [le_div_iff₀ hXpos] at h1
        have hcast : ((2 : ℕ) ^ Nat.log 2 ⌊x / X⌋₊ : Real)
            = (2 : Real) ^ Nat.log 2 ⌊x / X⌋₊ := by push_cast; ring
        rw [hcast] at h1
        rw [mul_comm]
        exact h1
      · -- x / 2^n < 2 * X
        rw [div_lt_iff₀ h2n]
        have h2 : x / X < ((2 : ℕ) ^ (Nat.log 2 ⌊x / X⌋₊ + 1) : Real) := by
          calc x / X < (⌊x / X⌋₊ : Real) + 1 := Nat.lt_floor_add_one _
            _ ≤ ((2 : ℕ) ^ (Nat.log 2 ⌊x / X⌋₊ + 1) : Real) := by
                have hnat : ⌊x / X⌋₊ + 1 ≤ (2 : ℕ) ^ (Nat.log 2 ⌊x / X⌋₊ + 1) := hlt
                exact_mod_cast hnat
        rw [div_lt_iff₀ hXpos] at h2
        calc x < (2 : Real) ^ (Nat.log 2 ⌊x / X⌋₊ + 1) * X := h2
          _ = 2 * ((2 : Real) ^ Nat.log 2 ⌊x / X⌋₊ * X) := by
              rw [pow_succ]
              push_cast
              ring
          _ = 2 * X * (2 : Real) ^ Nat.log 2 ⌊x / X⌋₊ := by ring
    · field_simp
  -- n(x) -> atTop as x -> atTop.
  have hlog : ∀ X : Real, 1 ≤ X →
      Tendsto (fun x : Real => Nat.log 2 ⌊x / X⌋₊) atTop atTop := by
    intro X hX
    rw [tendsto_atTop]
    intro N
    have hXpos : (0 : Real) < X := by linarith
    apply eventually_atTop.mpr
    refine ⟨X * (2 : Real) ^ N, ?_⟩
    intro x hx
    have h1 : ((2 : ℕ) ^ N : Real) ≤ x / X := by
      rw [le_div_iff₀ hXpos]
      have h2 : ((2 : ℕ) ^ N : Real) = (2 : Real) ^ N := by push_cast; ring
      rw [h2]
      linarith [hx]
    have h2 : (2 : ℕ) ^ N ≤ ⌊x / X⌋₊ := Nat.le_floor (by exact_mod_cast h1)
    exact Nat.le_log_of_pow_le (by norm_num) h2
  -- ((2^n)^eps) = ((2^eps)^n), by rpow algebra.
  have hpow : ∀ n : ℕ, ((2 : Real) ^ n) ^ eps = ((2 : Real) ^ eps) ^ n := by
    intro n
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show (0 : Real) ≤ 2 by norm_num),
      ← Real.rpow_natCast ((2 : Real) ^ eps) n,
      ← Real.rpow_mul (show (0 : Real) ≤ 2 by norm_num)]
    congr 1
    ring
  constructor
  · -- Direction 1: L x / x^eps -> 0.
    have h2eps : (1 : Real) < (2 : Real) ^ eps := Real.one_lt_rpow (by norm_num) heps
    set δ := ((2 : Real) ^ eps - 1) / 2 with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      linarith
    have hδlt : 1 + δ < (2 : Real) ^ eps := by
      rw [hδ]
      linarith
    have hX : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
        L (2 * x) / L x < 1 + δ := by
      have h := hslow 2 (by norm_num)
      have hev : ∀ᶠ x in atTop, L (2 * x) / L x < 1 + δ :=
        h.eventually (Iio_mem_nhds (by linarith : (1 : Real) < 1 + δ))
      obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hev
      exact ⟨max X₀ 1, le_max_right _ _, fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)⟩
    obtain ⟨X, hX1, hXr⟩ := hX
    have hXpos : (0 : Real) < X := by linarith
    -- max of L on [X, 2X]
    obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_Icc).exists_isMaxOn
      (Set.nonempty_Icc.mpr (by linarith : X ≤ 2 * X))
      (hcont.mono ((Set.Icc_subset_Ioi_iff (by linarith : X ≤ 2 * X)).mpr (by linarith : (0 : Real) < X)))
    set C := L x₀ with hC
    have hCpos : 0 < C := hpos x₀ (lt_of_lt_of_le hXpos hx₀.1)
    -- dyadic upper bound
    have hup : ∀ n : ℕ, ∀ y : Real, y ∈ Set.Ico X (2 * X) →
        L ((2 : Real) ^ n * y) ≤ C * (1 + δ) ^ n := by
      intro n
      induction n with
      | zero =>
        intro y hy
        simp only [pow_zero, one_mul, mul_one]
        exact (hmax ⟨hy.1, le_of_lt hy.2⟩ : L y ≤ L x₀)
      | succ n ih =>
        intro y hy
        have hz : X ≤ (2 : Real) ^ n * y := by
          calc X ≤ y := hy.1
            _ ≤ (2 : Real) ^ n * y := by
                have h1 : (1 : Real) ≤ (2 : Real) ^ n :=
                  one_le_pow₀ (by norm_num : (1 : Real) ≤ 2)
                calc y = 1 * y := by ring
                  _ ≤ (2 : Real) ^ n * y :=
                      mul_le_mul_of_nonneg_right h1 (le_of_lt (lt_of_lt_of_le hXpos hy.1))
        have hr := hXr _ hz
        have hLz : 0 < L ((2 : Real) ^ n * y) := hpos _ (lt_of_lt_of_le hXpos hz)
        have hstep : L ((2 : Real) ^ (n + 1) * y) = L (2 * ((2 : Real) ^ n * y)) := by
          congr 1
          rw [pow_succ]
          ring
        rw [hstep]
        have h1 : L (2 * ((2 : Real) ^ n * y)) < (1 + δ) * L ((2 : Real) ^ n * y) := by
          rw [div_lt_iff₀ hLz] at hr
          linarith [hr]
        calc L (2 * ((2 : Real) ^ n * y)) ≤ (1 + δ) * L ((2 : Real) ^ n * y) :=
              le_of_lt h1
          _ ≤ (1 + δ) * (C * (1 + δ) ^ n) :=
              mul_le_mul_of_nonneg_left (ih y hy) (by linarith : (0:Real) ≤ 1 + δ)
          _ = C * (1 + δ) ^ (n + 1) := by
              rw [pow_succ]
              ring
    -- squeeze
    set r := (1 + δ) / (2 : Real) ^ eps with hr
    have hr0 : 0 < r := by
      rw [hr]
      exact div_pos (by linarith) (by positivity)
    have hr1 : r < 1 := by
      rw [hr, div_lt_one (by positivity : (0:Real) < (2:Real) ^ eps)]
      exact hδlt
    have hbound : Tendsto (fun x : Real => (C / X ^ eps) * r ^ (Nat.log 2 ⌊x / X⌋₊))
        atTop (nhds 0) := by
      have hgeo : Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
      have hcomp := hgeo.comp (hlog X hX1)
      simpa using hcomp.const_mul (C / X ^ eps)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    · filter_upwards [eventually_ge_atTop X] with x hx
      exact div_nonneg (le_of_lt (hpos x (lt_of_lt_of_le hXpos hx)))
        (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hXpos hx)) _)
    · filter_upwards [eventually_ge_atTop X] with x hx
      obtain ⟨hy, hxy⟩ := hdyad X hX1 x hx
      have hL : L x ≤ C * (1 + δ) ^ (Nat.log 2 ⌊x / X⌋₊) := by
        have h := hup (Nat.log 2 ⌊x / X⌋₊) _ hy
        rw [← hxy] at h
        exact h
      have hyep : X ^ eps ≤ (x / (2 : Real) ^ Nat.log 2 ⌊x / X⌋₊) ^ eps :=
        Real.rpow_le_rpow hXpos.le hy.1 (le_of_lt heps)
      have hfac : x ^ eps = ((2 : Real) ^ eps) ^ (Nat.log 2 ⌊x / X⌋₊) *
          (x / (2 : Real) ^ Nat.log 2 ⌊x / X⌋₊) ^ eps := by
        conv_lhs => rw [hxy]
        rw [Real.mul_rpow (pow_nonneg (by norm_num : (0 : Real) ≤ 2) _)
          (le_of_lt (lt_of_lt_of_le hXpos hy.1)), hpow]
      have hden : (0 : Real) < ((2 : Real) ^ eps) ^ (Nat.log 2 ⌊x / X⌋₊) * X ^ eps :=
        mul_pos (pow_pos (by positivity) _) (Real.rpow_pos_of_pos hXpos _)
      have hcd : ((2 : Real) ^ eps) ^ (Nat.log 2 ⌊x / X⌋₊) * X ^ eps ≤
          ((2 : Real) ^ eps) ^ (Nat.log 2 ⌊x / X⌋₊) *
          (x / (2 : Real) ^ Nat.log 2 ⌊x / X⌋₊) ^ eps :=
        mul_le_mul_of_nonneg_left hyep (pow_nonneg (by positivity) _)
      calc L x / x ^ eps
          ≤ (C * (1 + δ) ^ (Nat.log 2 ⌊x / X⌋₊)) /
            (((2 : Real) ^ eps) ^ (Nat.log 2 ⌊x / X⌋₊) * X ^ eps) := by
            rw [hfac, div_le_div_iff₀ (mul_pos (pow_pos (Real.rpow_pos_of_pos (by norm_num) _) _)
              (Real.rpow_pos_of_pos (lt_of_lt_of_le hXpos hy.1) _)) hden]
            exact mul_le_mul hL hcd hden.le
              (mul_nonneg hCpos.le (pow_nonneg (by linarith : (0 : Real) ≤ 1 + δ) _))
        _ = (C / X ^ eps) * r ^ (Nat.log 2 ⌊x / X⌋₊) := by
            rw [hr, div_pow]
            field_simp
  · -- Direction 2: L x * x^eps -> atTop.
    have h2eps : (2 : Real) ^ (-eps) < 1 := by
      rw [Real.rpow_neg (by norm_num : (0:Real) ≤ 2)]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) heps)
    set δ := (1 - (2 : Real) ^ (-eps)) / 2 with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      linarith
    have hδlt : (2 : Real) ^ (-eps) < 1 - δ := by
      rw [hδ]
      linarith
    have hX : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
        1 - δ < L (2 * x) / L x := by
      have h := hslow 2 (by norm_num)
      have hev : ∀ᶠ x in atTop, 1 - δ < L (2 * x) / L x :=
        h.eventually (Ioi_mem_nhds (by linarith : 1 - δ < 1))
      obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hev
      exact ⟨max X₀ 1, le_max_right _ _, fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)⟩
    obtain ⟨X, hX1, hXr⟩ := hX
    have hXpos : (0 : Real) < X := by linarith
    obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_Icc).exists_isMinOn
      (Set.nonempty_Icc.mpr (by linarith : X ≤ 2 * X))
      (hcont.mono ((Set.Icc_subset_Ioi_iff (by linarith : X ≤ 2 * X)).mpr (by linarith : (0 : Real) < X)))
    set c := L x₀ with hc
    have hcpos : 0 < c := hpos x₀ (lt_of_lt_of_le hXpos hx₀.1)
    have hlow : ∀ n : ℕ, ∀ y : Real, y ∈ Set.Ico X (2 * X) →
        c * (1 - δ) ^ n ≤ L ((2 : Real) ^ n * y) := by
      intro n
      induction n with
      | zero =>
        intro y hy
        simp only [pow_zero, one_mul, mul_one]
        exact hmin ⟨hy.1, le_of_lt hy.2⟩
      | succ n ih =>
        intro y hy
        have hz : X ≤ (2 : Real) ^ n * y := by
          calc X ≤ y := hy.1
            _ ≤ (2 : Real) ^ n * y := by
                have h1 : (1 : Real) ≤ (2 : Real) ^ n :=
                  one_le_pow₀ (by norm_num : (1 : Real) ≤ 2)
                calc y = 1 * y := by ring
                  _ ≤ (2 : Real) ^ n * y :=
                      mul_le_mul_of_nonneg_right h1 (le_of_lt (lt_of_lt_of_le hXpos hy.1))
        have hr := hXr _ hz
        have hLz : 0 < L ((2 : Real) ^ n * y) := hpos _ (lt_of_lt_of_le hXpos hz)
        have hstep : L ((2 : Real) ^ (n + 1) * y) = L (2 * ((2 : Real) ^ n * y)) := by
          congr 1
          rw [pow_succ]
          ring
        rw [hstep]
        have h1 : (1 - δ) * L ((2 : Real) ^ n * y) < L (2 * ((2 : Real) ^ n * y)) := by
          rw [lt_div_iff₀ hLz] at hr
          linarith [hr]
        calc c * (1 - δ) ^ (n + 1) = (1 - δ) * (c * (1 - δ) ^ n) := by
              rw [pow_succ]
              ring
          _ ≤ (1 - δ) * L ((2 : Real) ^ n * y) :=
              mul_le_mul_of_nonneg_left (ih y hy) (by
                have h2e : (0 : Real) < (2 : Real) ^ (-eps) :=
                  Real.rpow_pos_of_pos (by norm_num) _
                linarith)
          _ ≤ L (2 * ((2 : Real) ^ n * y)) := le_of_lt h1
    set R := (1 - δ) * (2 : Real) ^ eps with hR
    have hR1 : 1 < R := by
      rw [hR]
      have h : (2 : Real) ^ (-eps) * (2 : Real) ^ eps = 1 := by
        rw [← Real.rpow_add (by norm_num : (0:Real) < 2)]
        simp
      have hpos2 : (0:Real) < (2:Real) ^ eps := by positivity
      calc 1 = (2 : Real) ^ (-eps) * (2 : Real) ^ eps := h.symm
        _ < (1 - δ) * (2 : Real) ^ eps :=
            mul_lt_mul_of_pos_right hδlt hpos2
    have hbound : Tendsto (fun x : Real => (c * X ^ eps) * R ^ (Nat.log 2 ⌊x / X⌋₊))
        atTop atTop := by
      have hgeo : Tendsto (fun n : ℕ => R ^ n) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt hR1
      have hcomp := hgeo.comp (hlog X hX1)
      exact hcomp.const_mul_atTop (mul_pos hcpos (Real.rpow_pos_of_pos hXpos _))
    apply tendsto_atTop_mono' atTop _ hbound
    filter_upwards [eventually_ge_atTop X] with x hx
    obtain ⟨hy, hxy⟩ := hdyad X hX1 x hx
    have hL : c * (1 - δ) ^ (Nat.log 2 ⌊x / X⌋₊) ≤ L x := by
      have h := hlow (Nat.log 2 ⌊x / X⌋₊) _ hy
      rw [← hxy] at h
      exact h
    have hfac : x ^ eps = ((2 : Real) ^ eps) ^ (Nat.log 2 ⌊x / X⌋₊) *
        (x / (2 : Real) ^ Nat.log 2 ⌊x / X⌋₊) ^ eps := by
      conv_lhs => rw [hxy]
      rw [Real.mul_rpow (pow_nonneg (by norm_num : (0 : Real) ≤ 2) _)
        (le_of_lt (lt_of_lt_of_le hXpos hy.1)), hpow]
    rw [hfac]
    calc (c * X ^ eps) * R ^ (Nat.log 2 ⌊x / X⌋₊)
        = c * (1 - δ) ^ (Nat.log 2 ⌊x / X⌋₊) *
          (((2 : Real) ^ eps) ^ (Nat.log 2 ⌊x / X⌋₊) * X ^ eps) := by
          rw [hR, mul_pow]
          ring
      _ ≤ L x * (((2 : Real) ^ eps) ^ (Nat.log 2 ⌊x / X⌋₊) *
          (x / (2 : Real) ^ Nat.log 2 ⌊x / X⌋₊) ^ eps) := by
          apply mul_le_mul hL _ (by positivity)
            (le_of_lt (hpos x (lt_of_lt_of_le hXpos hx)))
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow hXpos.le hy.1 (le_of_lt heps)
