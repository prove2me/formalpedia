-- Prove2me | solution 1 for LCAGroup.unitAddTorus_sobolev_inequality
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:11:34.142609+00:00
-- url     : https://prove2.me/submissions/178a4970-0a98-4807-8acd-709749b2db28

import Mathlib

open MeasureTheory UnitAddTorus
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_LCAGroup_unitAddTorus_sobolev_inequality

open Finset

/-- The sum over `ℤⁿ` of a product weight is the `n`-th power of the one-dimensional sum. -/
theorem tsum_pi_prod (G : ℤ → ℝ≥0∞) (n : ℕ) :
    ∑' a : Fin n → ℤ, ∏ i, G (a i) = (∑' k : ℤ, G k) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, tsum_eq_single (default : Fin 0 → ℤ)]
    · simp
    · intro a ha
      exact (ha (Subsingleton.elim a default)).elim
  | succ n ih =>
    let e : ℤ × (Fin n → ℤ) ≃ (Fin (n + 1) → ℤ) := Fin.snocEquiv (fun _ ↦ ℤ)
    have hfun (k : ℤ) (b : Fin n → ℤ) :
        ∏ i, G (e (k, b) i) = (∏ i, G (b i)) * G k := by
      simp only [e, Fin.snocEquiv_apply]
      rw [Fin.prod_univ_castSucc]
      congr 1
      · refine prod_congr rfl fun i _ => ?_
        rw [Fin.snoc_castSucc]
      · rw [Fin.snoc_last]
    rw [← e.tsum_eq (fun a => ∏ i, G (a i))]
    simp_rw [hfun]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_right]
    rw [ih, ENNReal.tsum_mul_left, ← pow_succ]

/-- `∑_{k ∈ ℤ} (1 + k²)^{-t}` converges for `t > 1/2`. -/
theorem summable_one_add_sq_rpow_neg {t : ℝ} (ht : 1 / 2 < t) :
    Summable (fun k : ℤ => (1 + (k : ℝ) ^ 2) ^ (-t)) := by
  have hb : 1 < 2 * t := by linarith
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow hb) ?_
  have hcof : {k : ℤ | k ≠ 0} ∈ Filter.cofinite := by
    rw [Filter.mem_cofinite]
    simp
  filter_upwards [hcof] with k hk
  have hk' : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    positivity
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 : |(k : ℝ)| ^ (-(2 * t)) = ((k : ℝ) ^ 2) ^ (-t) := by
    rw [show -(2 * t) = (2 : ℝ) * (-t) by ring, Real.rpow_mul (abs_nonneg _)]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [h1]
  exact Real.rpow_le_rpow_of_nonpos hk' (by linarith) (by linarith)

/-- Comparison of the radial weight with a product weight. -/
theorem rpow_neg_le_prod {n : ℕ} (hn : n ≠ 0) (s : ℝ) (hs : 0 ≤ s) (ξ : Fin n → ℤ) :
    (1 + ∑ i, (ξ i : ℝ) ^ 2) ^ (-s) ≤ ∏ i, (1 + (ξ i : ℝ) ^ 2) ^ (-(s / n)) := by
  have hpos : ∀ i, 0 < 1 + (ξ i : ℝ) ^ 2 := fun i => by positivity
  have hW : 0 ≤ 1 + ∑ i, (ξ i : ℝ) ^ 2 := by positivity
  have hP : ∏ i, (1 + (ξ i : ℝ) ^ 2) ≤ (1 + ∑ j, (ξ j : ℝ) ^ 2) ^ n := by
    calc ∏ i, (1 + (ξ i : ℝ) ^ 2) ≤ ∏ _i : Fin n, (1 + ∑ j, (ξ j : ℝ) ^ 2) := by
          refine Finset.prod_le_prod (fun i _ => (hpos i).le) fun i _ => ?_
          have : (ξ i : ℝ) ^ 2 ≤ ∑ j, (ξ j : ℝ) ^ 2 :=
            Finset.single_le_sum (f := fun j => (ξ j : ℝ) ^ 2) (fun j _ => by positivity)
              (Finset.mem_univ i)
          linarith
      _ = (1 + ∑ j, (ξ j : ℝ) ^ 2) ^ n := by simp
  rw [Real.finsetProd_rpow _ _ (fun i _ => (hpos i).le)]
  have hneg : -(s / n) ≤ 0 := by
    have : (0 : ℝ) ≤ s / n := by positivity
    linarith
  calc (1 + ∑ i, (ξ i : ℝ) ^ 2) ^ (-s)
      = ((1 + ∑ i, (ξ i : ℝ) ^ 2) ^ n) ^ (-(s / n)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW]
        congr 1
        field_simp
    _ ≤ (∏ i, (1 + (ξ i : ℝ) ^ 2)) ^ (-(s / n)) :=
        Real.rpow_le_rpow_of_nonpos (Finset.prod_pos fun i _ => hpos i) hP hneg

/-- Summability of a nonnegative real family from finiteness of the `ℝ≥0∞`-sum. -/
theorem summable_of_tsum_ofReal_ne_top {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i)
    (h : ∑' i, ENNReal.ofReal (f i) ≠ ⊤) : Summable f := by
  have := ENNReal.summable_toReal h
  simpa [ENNReal.toReal_ofReal (hf _)] using this

/-- `∑_{ξ ∈ ℤⁿ} (1 + |ξ|²)^{-s}` converges for `s > n/2`. -/
theorem summable_weight (n : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 < s) :
    Summable (fun ξ : Fin n → ℤ => (1 + ∑ i, (ξ i : ℝ) ^ 2) ^ (-s)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Summable.of_finite
  have hn' : n ≠ 0 := hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ n / 2 := by positivity
    linarith
  have ht : 1 / 2 < s / n := by
    rw [lt_div_iff₀ hnR]
    linarith
  set g : ℤ → ℝ := fun k => (1 + (k : ℝ) ^ 2) ^ (-(s / n)) with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => by positivity
  have h1 : Summable g := summable_one_add_sq_rpow_neg ht
  have hprod : Summable (fun ξ : Fin n → ℤ => ∏ i, g (ξ i)) := by
    refine summable_of_tsum_ofReal_ne_top (fun ξ => Finset.prod_nonneg fun i _ => hg0 _) ?_
    have : ∀ ξ : Fin n → ℤ, ENNReal.ofReal (∏ i, g (ξ i)) = ∏ i, ENNReal.ofReal (g (ξ i)) :=
      fun ξ => ENNReal.ofReal_prod_of_nonneg fun i _ => hg0 _
    simp_rw [this]
    rw [tsum_pi_prod (fun k => ENNReal.ofReal (g k)) n]
    exact ENNReal.pow_ne_top h1.tsum_ofReal_ne_top
  refine Summable.of_nonneg_of_le (fun ξ => by positivity) (fun ξ => ?_) hprod
  exact rpow_neg_le_prod hn' s hs0 ξ

/-- The weight `1 + |ξ|²`. -/
def wt {n : ℕ} (ξ : Fin n → ℤ) : ℝ := 1 + ∑ i, (ξ i : ℝ) ^ 2

theorem one_le_wt {n : ℕ} (ξ : Fin n → ℤ) : 1 ≤ wt ξ := by
  have : 0 ≤ ∑ i, (ξ i : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  unfold wt
  linarith

theorem wt_pos {n : ℕ} (ξ : Fin n → ℤ) : 0 < wt ξ := lt_of_lt_of_le one_pos (one_le_wt ξ)

/-- The pointwise bound in the case of a finite Sobolev norm. -/
theorem main_bound (n : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 < s)
    (φ : C(UnitAddTorus (Fin n), ℂ)) (z : UnitAddTorus (Fin n))
    (hS : ∑' ξ : Fin n → ℤ, ENNReal.ofReal (wt ξ ^ s) * ‖mFourierCoeff (⇑φ) ξ‖ₑ ^ 2 ≠ ⊤) :
    ‖φ z‖ₑ ^ 2 ≤ ENNReal.ofReal (∑' ξ : Fin n → ℤ, wt ξ ^ (-s)) *
      ∑' ξ : Fin n → ℤ, ENNReal.ofReal (wt ξ ^ s) * ‖mFourierCoeff (⇑φ) ξ‖ₑ ^ 2 := by
  set c := mFourierCoeff (⇑φ) with hc
  have hsum : Summable (fun ξ : Fin n → ℤ => wt ξ ^ (-s)) := summable_weight n s hs
  have hK0 : 0 ≤ ∑' ξ : Fin n → ℤ, wt ξ ^ (-s) :=
    tsum_nonneg fun ξ => Real.rpow_nonneg (wt_pos ξ).le _
  have hterm : ∀ ξ : Fin n → ℤ, ENNReal.ofReal (wt ξ ^ s * ‖c ξ‖ ^ 2) =
      ENNReal.ofReal (wt ξ ^ s) * ‖c ξ‖ₑ ^ 2 := by
    intro ξ
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos ξ).le _),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hB0 : ∀ ξ : Fin n → ℤ, 0 ≤ wt ξ ^ s * ‖c ξ‖ ^ 2 := fun ξ =>
    mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _)
  have hg2 : Summable (fun ξ : Fin n → ℤ => wt ξ ^ s * ‖c ξ‖ ^ 2) := by
    refine summable_of_tsum_ofReal_ne_top hB0 ?_
    simp_rw [hterm]
    exact hS
  have hSeq : ENNReal.ofReal (∑' ξ : Fin n → ℤ, wt ξ ^ s * ‖c ξ‖ ^ 2) =
      ∑' ξ : Fin n → ℤ, ENNReal.ofReal (wt ξ ^ s) * ‖c ξ‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_tsum_of_nonneg hB0 hg2]
    simp_rw [hterm]
  -- Cauchy--Schwarz
  let f : (Fin n → ℤ) → ℝ := fun ξ => wt ξ ^ (-s / 2)
  let g : (Fin n → ℤ) → ℝ := fun ξ => wt ξ ^ (s / 2) * ‖c ξ‖
  have hf0 : ∀ ξ, 0 ≤ f ξ := fun ξ => Real.rpow_nonneg (wt_pos ξ).le _
  have hg0 : ∀ ξ, 0 ≤ g ξ := fun ξ =>
    mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (norm_nonneg _)
  have hf2 : ∀ ξ, f ξ ^ (2 : ℝ) = wt ξ ^ (-s) := by
    intro ξ
    simp only [f]
    rw [← Real.rpow_mul (wt_pos ξ).le]
    congr 1
    ring
  have hg2' : ∀ ξ, g ξ ^ (2 : ℝ) = wt ξ ^ s * ‖c ξ‖ ^ 2 := by
    intro ξ
    simp only [g]
    rw [Real.rpow_two, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (wt_pos ξ).le]
    norm_num
  have hfg : ∀ ξ, f ξ * g ξ = ‖c ξ‖ := by
    intro ξ
    simp only [f, g]
    rw [← mul_assoc, ← Real.rpow_add (wt_pos ξ), show -s / 2 + s / 2 = (0 : ℝ) by ring,
      Real.rpow_zero, one_mul]
  have hfs : Summable fun ξ => f ξ ^ (2 : ℝ) := by
    simp_rw [hf2]
    exact hsum
  have hgs : Summable fun ξ => g ξ ^ (2 : ℝ) := by
    simp_rw [hg2']
    exact hg2
  obtain ⟨hcs, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two hf0 hg0 hfs hgs
  simp only [hfg, hf2, hg2'] at hcs hle
  -- the Fourier series
  have hcsum : Summable c := hcs.of_norm
  have hser := hasSum_mFourier_series_apply_of_summable hcsum z
  have hnorm : ‖φ z‖ ≤ ∑' ξ, ‖c ξ‖ := by
    rw [← hser.tsum_eq]
    refine tsum_of_norm_bounded hcs.hasSum fun ξ => ?_
    rw [norm_smul]
    have h1 : ‖(mFourier ξ) z‖ ≤ 1 := by
      have := ContinuousMap.norm_coe_le_norm (mFourier ξ) z
      rwa [mFourier_norm] at this
    calc ‖c ξ‖ * ‖(mFourier ξ) z‖ ≤ ‖c ξ‖ * 1 := by gcongr
      _ = ‖c ξ‖ := mul_one _
  set A := ∑' ξ : Fin n → ℤ, wt ξ ^ (-s) with hA
  set B := ∑' ξ : Fin n → ℤ, wt ξ ^ s * ‖c ξ‖ ^ 2 with hB
  have hB0' : 0 ≤ B := tsum_nonneg hB0
  have hsq : ‖φ z‖ ^ 2 ≤ A * B := by
    have h0 : 0 ≤ ‖φ z‖ := norm_nonneg _
    have h2 : ‖φ z‖ ≤ A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := hnorm.trans hle
    calc ‖φ z‖ ^ 2 ≤ (A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
      _ = A * B := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (B ^ (1 / 2 : ℝ)),
          ← Real.rpow_mul hK0, ← Real.rpow_mul hB0']
        norm_num
  calc ‖φ z‖ₑ ^ 2 = ENNReal.ofReal (‖φ z‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ ENNReal.ofReal (A * B) := ENNReal.ofReal_le_ofReal hsq
    _ = ENNReal.ofReal A * ENNReal.ofReal B := ENNReal.ofReal_mul hK0
    _ = ENNReal.ofReal A *
        ∑' ξ : Fin n → ℤ, ENNReal.ofReal (wt ξ ^ s) * ‖c ξ‖ₑ ^ 2 := by rw [hSeq]

end Sol_LCAGroup_unitAddTorus_sobolev_inequality

open Sol_LCAGroup_unitAddTorus_sobolev_inequality in
theorem solution (n : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 < s) :
    ∃ C : ℝ≥0, ∀ (φ : C(UnitAddTorus (Fin n), ℂ)) (z : UnitAddTorus (Fin n)),
      ‖φ z‖ₑ ^ 2 ≤ C * ∑' ξ : Fin n → ℤ,
        ENNReal.ofReal ((1 + ∑ i, (ξ i : ℝ) ^ 2) ^ s) * ‖mFourierCoeff (⇑φ) ξ‖ₑ ^ 2 := by
  refine ⟨(∑' ξ : Fin n → ℤ, wt ξ ^ (-s)).toNNReal + 1, fun φ z => ?_⟩
  change ‖φ z‖ₑ ^ 2 ≤ _ * ∑' ξ : Fin n → ℤ, ENNReal.ofReal (wt ξ ^ s) * ‖mFourierCoeff (⇑φ) ξ‖ₑ ^ 2
  by_cases hS : ∑' ξ : Fin n → ℤ, ENNReal.ofReal (wt ξ ^ s) * ‖mFourierCoeff (⇑φ) ξ‖ₑ ^ 2 = ⊤
  · rw [hS, ENNReal.mul_top (ENNReal.coe_ne_zero.mpr (by positivity))]
    exact le_top
  refine (main_bound n s hs φ z hS).trans ?_
  gcongr
  exact ENNReal.coe_le_coe.mpr le_self_add
