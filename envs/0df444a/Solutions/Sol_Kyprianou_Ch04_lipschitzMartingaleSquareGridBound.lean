-- Prove2me | solution 1 for Kyprianou.Ch04.lipschitzMartingaleSquareGridBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:06:12.807113+00:00
-- url     : https://prove2.me/submissions/04dce55b-5427-47da-be66-a38069265473

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_martingaleSampledGridEnergy
open Kyprianou.Ch04
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- A Lipschitz martingale starting at zero has squared expectation bounded by its grid energy. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : NNReal → Omega → ℝ) (hM : Martingale M F P)
    (h0 : ∀ᵐ w ∂P, M 0 w = 0) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ s t : NNReal, s ≤ t → ∀ᵐ w ∂P,
      |M t w - M s w| ≤ C * ((t : ℝ) - (s : ℝ)))
    (t : NNReal) (N : ℕ) (hN : 0 < N) :
    (∫ w, (M t w)^2 ∂P) ≤ (C*(t : ℝ))^2 / (N : ℝ) := by
  let e : ℕ → NNReal := fun j => (j : NNReal) * (t / (N : NNReal))
  have he : Monotone e := by
    intro i j hij
    dsimp only [e]
    gcongr
  have h0e : e 0 = 0 := by simp [e]
  have hNe : e N = t := by
    have hn : (N : NNReal) ≠ 0 := by exact_mod_cast hN.ne'
    change (N : NNReal) * (t / (N : NNReal)) = t
    rw [mul_comm,div_mul_cancel₀ _ hn]
  let V : ℕ → Omega → ℝ := fun j w => M (e (j+1)) w-M (e j) w
  have hV (j : ℕ) : ∀ᵐ w ∂P, |V j w| ≤ C*(t : ℝ)/(N : ℝ) := by
    have hj := hL (e j) (e (j+1)) (he (Nat.le_succ j))
    filter_upwards [hj] with w hw
    have hd : (e (j+1) : ℝ) - (e j : ℝ) = (t : ℝ)/(N : ℝ) := by
      simp only [e,NNReal.coe_mul,NNReal.coe_div,NNReal.coe_natCast,Nat.cast_add,Nat.cast_one,NNReal.coe_add,NNReal.coe_one]
      ring
    simpa only [V,hd,mul_div_assoc] using hw
  have hE := martingaleSampledGridEnergy P F M hM e he _ hV N
  rw [hNe,h0e] at hE
  have hsum : ∀ᵐ w ∂P, (M t w-M 0 w)^2 = (M t w)^2 := by
    filter_upwards [h0] with w hw
    rw [hw,sub_zero]
  rw [integral_congr_ae hsum] at hE
  rw [hE]
  have hB : 0 ≤ C*(t : ℝ)/(N : ℝ) := by positivity
  calc
    _ ≤ ∑ j ∈ Finset.range N, (C*(t : ℝ)/(N : ℝ))^2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hm := ((hM.integrable (e (j+1))).sub (hM.integrable (e j))).aestronglyMeasurable
      have hmem : MemLp (V j) 2 P := MemLp.of_bound hm _ (by
        simpa only [Real.norm_eq_abs] using hV j)
      have hi := (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem
      have hle : ∀ᵐ w ∂P, (V j w)^2 ≤ (C*(t : ℝ)/(N : ℝ))^2 := by
        filter_upwards [hV j] with w hw
        exact sq_le_sq.mpr (by rwa [abs_of_nonneg hB])
      simpa using integral_mono_ae hi (integrable_const _) hle
    _ = _ := by
      rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
