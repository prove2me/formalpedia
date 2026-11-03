-- Prove2me | solution 1 for MultiPriceOnline.Balance.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:07:24.646509+00:00
-- url     : https://prove2.me/submissions/9f5e1677-a49b-444b-b9fa-13163e985100

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet
import Definitions.Def_MultiPriceOnline_Balance_Procedure

open MultiPriceOnline.Balance MeasureTheory

private lemma lsum_bounds {m : ℕ} {r α : ℕ → ℝ} (hα : IsBookingLimits m r α) (j : ℕ) (hj : j ≤ m) :
    0 ≤ Lsum α j ∧ Lsum α j ≤ 1 := by
  unfold Lsum
  have hnonneg : ∀ i ∈ Finset.Icc 1 m, 0 ≤ α i := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact le_of_lt (hα.1 i hi.1 hi.2)
  have hsub : Finset.Icc 1 j ⊆ Finset.Icc 1 m := Finset.Icc_subset_Icc_right hj
  refine ⟨Finset.sum_nonneg (fun i hi => hnonneg i (hsub hi)), ?_⟩
  calc
    ∑ i ∈ Finset.Icc 1 j, α i ≤ ∑ i ∈ Finset.Icc 1 m, α i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hnonneg i hi)
    _ = 1 := hα.2.1

private lemma cv_def3Config_eq {k m : ℕ} {r α : ℕ → ℝ} (hα : IsBookingLimits m r α)
    (j : ℕ) (hj : j ≤ m) (W : ℝ) (hW : 0 ≤ W) :
    (cv (def3Config k m α W) j : ℝ) =
      (⌊Lsum α j * k⌋₊ : ℝ) + if W < Lsum α j * k - ⌊Lsum α j * k⌋₊ then 1 else 0 := by
  unfold cv def3Config
  rw [dif_pos (Nat.lt_succ_of_le hj)]
  dsimp
  have hL := lsum_bounds hα j hj
  have hk_nonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hx0 : 0 ≤ Lsum α j * k := mul_nonneg hL.1 hk_nonneg
  have hxk : Lsum α j * k ≤ k := by nlinarith
  have hfloor_le : ⌊Lsum α j * k⌋₊ ≤ k := Nat.floor_le_of_le hxk
  have hle : ⌊Lsum α j * k⌋₊ + (if W < Lsum α j * k - ⌊Lsum α j * k⌋₊ then 1 else 0) ≤ k := by
    split_ifs with h
    · have hlt : (⌊Lsum α j * k⌋₊ : ℝ) < k := by linarith
      exact Nat.succ_le_of_lt (Nat.cast_lt.mp hlt)
    · omega
  rw [min_eq_right hle]
  push_cast
  split_ifs <;> ring

theorem solution (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (r α : ℕ → ℝ)
    (hr : IsPriceSet m r) (hα : IsBookingLimits m r α) :
    (∀ j, j ≤ m →
      ∫ W in (0 : ℝ)..1, (cv (def3Config k m α W) j : ℝ) / k = Lsum α j) ∧
    (∀ W ∈ Set.Icc (0 : ℝ) 1, ∀ j j' : ℕ, 1 ≤ j' → j' < j → j ≤ m →
      |((cv (def3Config k m α W) j : ℝ) / k - (cv (def3Config k m α W) j' : ℝ) / k) -
          (Lsum α j - Lsum α j')| ≤ 1 / k) := by
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast ( by omega : 0 < k )
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  refine ⟨?_, ?_⟩
  · intro j hj
    have hL := lsum_bounds hα j hj
    set x : ℝ := Lsum α j * k
    set n : ℕ := ⌊x⌋₊
    set f : ℝ := x - n
    have hx0 : 0 ≤ x := mul_nonneg hL.1 (le_of_lt hk_pos)
    have hn_le : (n : ℝ) ≤ x := Nat.floor_le hx0
    have hx_lt : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
    have hf0 : 0 ≤ f := by dsimp [f]; linarith
    have hf1 : f ≤ 1 := by dsimp [f]; linarith
    have hcongr : Set.EqOn (fun W => (cv (def3Config k m α W) j : ℝ) / k)
        (fun W => ((n : ℝ) + Set.indicator (Set.Iio f) (fun _ => (1 : ℝ)) W) / k)
        (Set.uIcc (0 : ℝ) 1) := by
      intro W hW
      rw [Set.uIcc_of_le zero_le_one] at hW
      dsimp only
      rw [cv_def3Config_eq hα j hj W hW.1]
      simp only [Set.indicator_apply, Set.mem_Iio, x, n, f]
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_div,
        intervalIntegral.integral_of_le zero_le_one]
    have hint1 : IntegrableOn (fun _ : ℝ => (n : ℝ)) (Set.Ioc 0 1) volume :=
      intervalIntegrable_const.1
    have hint2 : IntegrableOn (Set.indicator (Set.Iio f) (fun _ : ℝ => (1 : ℝ))) (Set.Ioc 0 1) volume :=
      intervalIntegrable_const.1.indicator measurableSet_Iio
    rw [integral_add hint1 hint2]
    have hI1 : ∫ _ in Set.Ioc (0 : ℝ) 1, (n : ℝ) = (n : ℝ) := by
      simp [Measure.real]
    have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Iio f = Set.Ioo (0 : ℝ) f := by
      ext W
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
    have hI2 : ∫ W in Set.Ioc (0 : ℝ) 1, Set.indicator (Set.Iio f) (fun _ : ℝ => (1 : ℝ)) W = f := by
      rw [setIntegral_indicator measurableSet_Iio, hset]
      simp [Measure.real, Real.volume_Ioo, hf0]
    rw [hI1, hI2]
    have hnf : (n : ℝ) + f = Lsum α j * k := by dsimp [f, x]; ring
    rw [hnf, mul_div_cancel_right₀ _ hk_ne]
  · intro W hW j j' hj'1 hj'j hjm
    have hj'm : j' ≤ m := by omega
    rw [cv_def3Config_eq hα j hjm W hW.1, cv_def3Config_eq hα j' hj'm W hW.1]
    have hLj := lsum_bounds hα j hjm
    have hLj' := lsum_bounds hα j' hj'm
    set x : ℝ := Lsum α j * k
    set x' : ℝ := Lsum α j' * k
    set n : ℕ := ⌊x⌋₊
    set n' : ℕ := ⌊x'⌋₊
    set f : ℝ := x - n
    set f' : ℝ := x' - n'
    have hx0 : 0 ≤ x := mul_nonneg hLj.1 (le_of_lt hk_pos)
    have hx'0 : 0 ≤ x' := mul_nonneg hLj'.1 (le_of_lt hk_pos)
    have hn_le : (n : ℝ) ≤ x := Nat.floor_le hx0
    have hx_lt : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
    have hn'_le : (n' : ℝ) ≤ x' := Nat.floor_le hx'0
    have hx'_lt : x' < (n' : ℝ) + 1 := Nat.lt_floor_add_one x'
    have hf0 : 0 ≤ f := by dsimp [f]; linarith
    have hf1 : f ≤ 1 := by dsimp [f]; linarith
    have hf'0 : 0 ≤ f' := by dsimp [f']; linarith
    have hf'1 : f' ≤ 1 := by dsimp [f']; linarith
    let I : ℝ := if W < f then 1 else 0
    let I' : ℝ := if W < f' then 1 else 0
    have hdiff : (((n : ℝ) + I) / k - ((n' : ℝ) + I') / k) - (Lsum α j - Lsum α j') =
        ((I - I') - (f - f')) / k := by
      have hx_eq : (n : ℝ) + f = Lsum α j * k := by dsimp [f, x]; ring
      have hx'_eq : (n' : ℝ) + f' = Lsum α j' * k := by dsimp [f', x']; ring
      apply mul_right_cancel₀ hk_ne
      calc
        ((((n : ℝ) + I) / k - ((n' : ℝ) + I') / k) - (Lsum α j - Lsum α j')) * k
          = ((n : ℝ) + I) / k * k - ((n' : ℝ) + I') / k * k - (Lsum α j * k - Lsum α j' * k) := by ring
        _ = ((n : ℝ) + I) - ((n' : ℝ) + I') - (((n : ℝ) + f) - ((n' : ℝ) + f')) := by
          rw [div_mul_cancel₀ _ hk_ne, div_mul_cancel₀ _ hk_ne, hx_eq, hx'_eq]
        _ = (I - I') - (f - f') := by ring
        _ = ((I - I') - (f - f')) / k * k := by rw [div_mul_cancel₀ _ hk_ne]
    change |(((n : ℝ) + I) / k - ((n' : ℝ) + I') / k) - (Lsum α j - Lsum α j')| ≤ 1 / k
    rw [hdiff, abs_div, abs_of_pos hk_pos]
    apply div_le_div_of_nonneg_right _ (le_of_lt hk_pos)
    dsimp [I, I']
    rw [abs_le]
    split_ifs <;> constructor <;> linarith
