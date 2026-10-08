-- Prove2me | solution 1 for LogSobolevMC.Metropolis.example_3_3_compare
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:16:52.579979+00:00
-- url     : https://prove2.me/submissions/681558ae-df28-4e3d-be38-dafc74f49215

import Mathlib
import Definitions.Def_LogSobolevMC_Metropolis_Setting
import Definitions.Def_LogSobolevMC_Metropolis_Chains

open scoped BigOperators
open LogSobolevMC.Metropolis

private lemma adjacent_ratio (n k : ℕ) (hk : k < n) :
    ((n.choose (k + 1) : ℝ) / 2 ^ n) / ((n.choose k : ℝ) / 2 ^ n) =
      ((n : ℝ) - k) / ((k : ℝ) + 1) := by
  have hp : (n.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k ≤ n)).ne'
  have ht : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hid := Nat.choose_succ_right_eq n k
  have hid' : (n.choose (k + 1) : ℝ) * (k + 1) =
      (n.choose k : ℝ) * ((n : ℝ) - k) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub (by omega : k ≤ n)] using congrArg (fun z : ℕ => (z : ℝ)) hid
  field_simp
  nlinarith [hid']

private lemma min_ratio_bounds (a b n : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (han : a ≤ n) (hbn : b ≤ n) (hs : a + b = n + 1) :
    1 / 2 * (a / n) ≤ 1 / 2 * min 1 (a / b) ∧
      1 / 2 * min 1 (a / b) ≤ a / n := by
  have hn : 0 < n := by linarith
  have hb0 : 0 < b := by linarith
  by_cases h : b ≤ a
  · rw [min_eq_left ((le_div_iff₀ hb0).2 (by linarith))]
    constructor
    · have := (div_le_one hn).2 han
      linarith
    · apply (le_div_iff₀ hn).2
      linarith
  · rw [min_eq_right ((div_le_one hb0).2 (by linarith))]
    constructor
    · have := (div_le_div_iff₀ hn hb0).2 (by nlinarith : a * b ≤ a * n)
      linarith
    · apply (le_div_iff₀ hn).2
      have he : a / b * b = a := div_mul_cancel₀ a hb0.ne'
      have hp : 0 ≤ a / b := div_nonneg (by linarith) hb0.le
      nlinarith

private lemma offdiag (n : ℕ) (hn : 1 ≤ n) (x y : Fin (n + 1)) (hxy : x ≠ y) :
    1 / 2 * ehrenfest n x y ≤ binomMetropolis n x y ∧
      binomMetropolis n x y ≤ ehrenfest n x y := by
  have hx : x.val ≤ n := by omega
  have hy : y.val ≤ n := by omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  unfold binomMetropolis MarkovMixing.metropolis
  rw [if_neg (Ne.symm hxy)]
  by_cases hup : y.val = x.val + 1
  · have hxlt : x.val < n := by omega
    have hr : binomPi n y / binomPi n x =
        ((n : ℝ) - x.val) / ((x.val : ℝ) + 1) := by
      simpa only [binomPi, hup] using adjacent_ratio n x.val hxlt
    rw [hr]
    simp only [baseWalk, hup, true_or, if_true, ehrenfest]
    have hx' : (x.val : ℝ) + 1 ≤ n := by exact_mod_cast hxlt
    have hxn : (x.val : ℝ) ≤ n := by exact_mod_cast hx
    exact min_ratio_bounds _ _ _ (by linarith) (by have := Nat.cast_nonneg (α := ℝ) x.val; linarith)
      (by have := Nat.cast_nonneg (α := ℝ) x.val; linarith) hx' (by ring)
  · by_cases hdown : y.val + 1 = x.val
    · have hylt : y.val < n := by omega
      have hr : binomPi n y / binomPi n x =
          (x.val : ℝ) / ((n : ℝ) - x.val + 1) := by
        have hh := adjacent_ratio n y.val hylt
        have hh' : binomPi n x / binomPi n y =
            ((n : ℝ) - y.val) / ((y.val : ℝ) + 1) := by
          simpa only [binomPi, hdown] using hh
        have hv : (y.val : ℝ) + 1 = x.val := by exact_mod_cast hdown
        have := congrArg (fun z : ℝ => z⁻¹) hh'
        rw [inv_div, inv_div] at this
        convert this using 1 <;> congr 1 <;> linarith
      rw [hr]
      simp only [baseWalk, hup, hdown, false_or, if_true, ehrenfest, if_false]
      have hx' : 1 ≤ (x.val : ℝ) := by exact_mod_cast (by omega : 1 ≤ x.val)
      have hx'' : (x.val : ℝ) ≤ n := by exact_mod_cast hx
      exact min_ratio_bounds _ _ _ hx' (by linarith) hx'' (by linarith) (by ring)
    · simp [baseWalk, hup, hdown, hxy, ehrenfest]

private lemma dirichlet_square {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (π : V → ℝ)
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hbal : ∀ x y, π x * K x y = π y * K y x) (f : V → ℝ) :
    LogSobolevMC.ChiSquare.dirichlet K π f f =
      1 / 2 * ∑ x, ∑ y, (f x - f y)^2 * (π x * K x y) := by
  have he : LogSobolevMC.ChiSquare.dirichlet K π f f =
      ∑ x, ∑ y, (f x - f y) * f x * (π x * K x y) := by
    unfold LogSobolevMC.ChiSquare.dirichlet
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Matrix.mulVec, dotProduct]
    calc
      (f x - ∑ y, K x y * f y) * f x * π x =
          (∑ y, (f x * K x y - K x y * f y)) * f x * π x := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hrow, mul_one]
      _ = ∑ y, (f x - f y) * f x * (π x * K x y) := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro y hy
        ring
  have hs : (∑ x, ∑ y, (f x - f y) * f x * (π x * K x y)) =
      ∑ x, ∑ y, (f y - f x) * f y * (π x * K x y) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [hbal y x]
  have ha : (∑ x, ∑ y, (f x - f y) * f x * (π x * K x y)) +
      (∑ x, ∑ y, (f y - f x) * f y * (π x * K x y)) =
      ∑ x, ∑ y, (f x - f y)^2 * (π x * K x y) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [he]
  linarith

private lemma metropolis_row {V : Type*} [Fintype V] [DecidableEq V]
    (Ψ : Matrix V V ℝ) (π : V → ℝ) (x : V) :
    ∑ y, MarkovMixing.metropolis Ψ π x y = 1 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
  have he : (∑ y ∈ Finset.univ.erase x, MarkovMixing.metropolis Ψ π x y) =
      ∑ y ∈ ({x}ᶜ : Finset V), Ψ x y * min 1 (π y / π x) := by
    have hset : Finset.univ.erase x = ({x}ᶜ : Finset V) := by ext y; simp
    rw [hset]
    apply Finset.sum_congr rfl
    intro y hy
    simp only [Finset.mem_compl, Finset.mem_singleton] at hy
    simp [MarkovMixing.metropolis, hy]
  rw [he]
  simp [MarkovMixing.metropolis]

private lemma metropolis_balance {V : Type*} [Fintype V] [DecidableEq V]
    (Ψ : Matrix V V ℝ) (π : V → ℝ) (hp : ∀ x, 0 < π x)
    (hs : ∀ x y, Ψ x y = Ψ y x) (x y : V) :
    π x * MarkovMixing.metropolis Ψ π x y =
      π y * MarkovMixing.metropolis Ψ π y x := by
  by_cases h : x = y
  · subst y; rfl
  · simp only [MarkovMixing.metropolis, if_neg h, if_neg (Ne.symm h)]
    have he (a b : V) : π a * min 1 (π b / π a) = min (π a) (π b) := by
      by_cases hh : 1 ≤ π b / π a
      · rw [min_eq_left hh, mul_one, min_eq_left]
        simpa using (le_div_iff₀ (hp a)).1 hh
      · rw [min_eq_right (le_of_not_ge hh), mul_div_cancel₀ _ (hp a).ne',
          min_eq_right]
        have := (div_le_one (hp a)).1 (le_of_not_ge hh)
        exact this
    calc
      _ = Ψ x y * (π x * min 1 (π y / π x)) := by ring
      _ = Ψ y x * min (π x) (π y) := by rw [he, hs]
      _ = Ψ y x * (π y * min 1 (π x / π y)) := by rw [he, min_comm]
      _ = _ := by ring

private lemma sum_fin_value (n k : ℕ) (a : ℝ) :
    (∑ y : Fin (n + 1), if y.val = k then a else 0) =
      if k < n + 1 then a else 0 := by
  by_cases hk : k < n + 1
  · let z : Fin (n + 1) := ⟨k, hk⟩
    have he (y : Fin (n + 1)) : y.val = k ↔ y = z := by
      exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp [he, hk]
  · have he (y : Fin (n + 1)) : y.val ≠ k := by omega
    simp [he, hk]

private lemma ehrenfest_row (n : ℕ) (hn : 1 ≤ n) (x : Fin (n + 1)) :
    ∑ y, ehrenfest n x y = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have he (y : Fin (n + 1)) : ehrenfest n x y =
      (if y.val = x.val + 1 then ((n : ℝ) - x.val) / n else 0) +
      (if y.val = x.val - 1 ∧ 0 < x.val then (x.val : ℝ) / n else 0) := by
    unfold ehrenfest
    split_ifs <;> simp_all <;> omega
  simp only [he, Finset.sum_add_distrib]
  rw [sum_fin_value]
  by_cases hx0 : x.val = 0
  · simp [hx0, hn, hn0, show 1 < n + 1 by omega]
  · have hp : 0 < x.val := by omega
    simp only [hp, and_true]
    rw [sum_fin_value]
    have hm : x.val - 1 < n + 1 := by omega
    rw [if_pos hm]
    by_cases htop : x.val = n
    · simp [htop, hn0]
    · rw [if_pos (by omega)]
      field_simp
      ring

private lemma binom_positive (n : ℕ) (x : Fin (n + 1)) : 0 < binomPi n x := by
  unfold binomPi
  apply div_pos
  · exact_mod_cast Nat.choose_pos (by omega : x.val ≤ n)
  · positivity

private lemma ehrenfest_balance (n : ℕ) (x y : Fin (n + 1)) :
    binomPi n x * ehrenfest n x y = binomPi n y * ehrenfest n y x := by
  have step (a b : Fin (n + 1)) (h : b.val = a.val + 1) :
      binomPi n a * ehrenfest n a b = binomPi n b * ehrenfest n b a := by
    have ha : a.val < n := by omega
    have hh := adjacent_ratio n a.val ha
    have hb : (b.val : ℝ) = (a.val : ℝ) + 1 := by exact_mod_cast h
    have hbr : binomPi n b / binomPi n a =
        ((n : ℝ) - a.val) / ((a.val : ℝ) + 1) := by
      simpa only [binomPi, h] using hh
    have hp := binom_positive n a
    have hc := (div_eq_div_iff hp.ne' (by positivity : (a.val : ℝ) + 1 ≠ 0)).1 hbr
    have hnot : ¬ a.val = a.val + 1 + 1 := by omega
    simp only [ehrenfest, h, if_true, if_neg hnot, Nat.cast_add, Nat.cast_one]
    rw [← mul_div_assoc, ← mul_div_assoc]
    congr 1
    nlinarith
  by_cases h : y.val = x.val + 1
  · exact step x y h
  · by_cases h' : x.val = y.val + 1
    · exact (step y x h').symm
    · simp [ehrenfest, h, h', show ¬ y.val + 1 = x.val by omega,
        show ¬ x.val + 1 = y.val by omega]

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (∀ x y : Fin (n + 1), x ≠ y →
      1 / 2 * ehrenfest n x y ≤ binomMetropolis n x y ∧
        binomMetropolis n x y ≤ ehrenfest n x y) ∧
    (∀ f : Fin (n + 1) → ℝ,
      LogSobolevMC.ChiSquare.dirichlet (binomMetropolis n) (binomPi n) f f ≤ LogSobolevMC.ChiSquare.dirichlet (ehrenfest n) (binomPi n) f f ∧
        LogSobolevMC.ChiSquare.dirichlet (ehrenfest n) (binomPi n) f f ≤
          2 * LogSobolevMC.ChiSquare.dirichlet (binomMetropolis n) (binomPi n) f f) := by
  refine ⟨offdiag n hn, ?_⟩
  intro f
  have hs (x y : Fin (n + 1)) : baseWalk n x y = baseWalk n y x := by
    unfold baseWalk
    by_cases hxy : x = y
    · subst y; rfl
    · have hyx := Ne.symm hxy
      simp only [hxy, hyx, false_and, if_false]
      have he : (y.val = x.val + 1 ∨ y.val + 1 = x.val) ↔
          (x.val = y.val + 1 ∨ x.val + 1 = y.val) := by omega
      simp only [he]
  have hmr : ∀ x, ∑ y, binomMetropolis n x y = 1 := metropolis_row _ _
  have hmb : ∀ x y, binomPi n x * binomMetropolis n x y =
      binomPi n y * binomMetropolis n y x :=
    metropolis_balance _ _ (binom_positive n) hs
  rw [dirichlet_square _ _ hmr hmb,
    dirichlet_square _ _ (ehrenfest_row n hn) (ehrenfest_balance n)]
  have hlo : (∑ x, ∑ y, (f x - f y)^2 * (binomPi n x * binomMetropolis n x y)) ≤
      ∑ x, ∑ y, (f x - f y)^2 * (binomPi n x * ehrenfest n x y) := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro y hy
    by_cases hxy : x = y
    · subst y; simp
    · exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (offdiag n hn x y hxy).2 (binom_positive n x).le)
        (sq_nonneg _)
  have hhi : (∑ x, ∑ y, (f x - f y)^2 * (binomPi n x * ehrenfest n x y)) ≤
      2 * ∑ x, ∑ y, (f x - f y)^2 * (binomPi n x * binomMetropolis n x y) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro y hy
    by_cases hxy : x = y
    · subst y; simp
    · have hh := (offdiag n hn x y hxy).1
      have hh' : ehrenfest n x y ≤ 2 * binomMetropolis n x y := by linarith
      have ht := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hh' (binom_positive n x).le) (sq_nonneg (f x - f y))
      nlinarith [ht]
  constructor <;> linarith

#print axioms solution
