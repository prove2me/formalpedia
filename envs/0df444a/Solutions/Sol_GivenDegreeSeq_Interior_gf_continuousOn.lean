-- Prove2me | solution 1 for GivenDegreeSeq.Interior.gf_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:27:31.524163+00:00
-- url     : https://prove2.me/submissions/1725a22c-4e05-4e68-9caa-fcf645142cb9

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_DPrime

set_option autoImplicit false
open GivenDegreeSeq.Interior MeasureTheory intervalIntegral

lemma gdi_int_anti (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Icc 0 1)) (a b : ℝ)
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    IntervalIntegrable f volume a b := by
  apply AntitoneOn.intervalIntegrable
  intro x hx y hy hxy
  have h01 : Set.uIcc a b ⊆ Set.Icc (0:ℝ) 1 := Set.uIcc_subset_Icc ha hb
  exact hf (h01 hx) (h01 hy) hxy

lemma gdi_min_anti (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Icc 0 1)) (x : ℝ) :
    AntitoneOn (fun y => min (f y) x) (Set.Icc 0 1) := by
  intro a ha b hb hab
  exact min_le_min_right _ (hf ha hb hab)

lemma gdi_T1_lip (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Icc 0 1)) :
    LipschitzOnWith (|f 0| + |f 1| + 2).toNNReal
      (fun x => ∫ y in x..1, min (f y) x) (Set.Icc 0 1) := by
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hM : (0:ℝ) ≤ |f 0| + |f 1| + 2 := by positivity
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx x0 hx0
  rw [Real.coe_toNNReal _ hM, Real.dist_eq, Real.dist_eq]
  have Mx := gdi_int_anti _ (gdi_min_anti f hf x) x 1 hx h1
  have Mx0 := gdi_int_anti _ (gdi_min_anti f hf x0) x 1 hx h1
  have Mx0' := gdi_int_anti _ (gdi_min_anti f hf x0) x x0 hx hx0
  have Mx0'' := gdi_int_anti _ (gdi_min_anti f hf x0) x0 1 hx0 h1
  have e : (∫ y in x..1, min (f y) x) - ∫ y in x0..1, min (f y) x0 =
      (∫ y in x..1, (min (f y) x - min (f y) x0)) + ∫ y in x..x0, min (f y) x0 := by
    rw [integral_sub Mx Mx0, ← integral_add_adjacent_intervals Mx0' Mx0'']
    ring
  rw [e]
  have b1 : ‖∫ y in x..1, (min (f y) x - min (f y) x0)‖ ≤ |x - x0| * |1 - x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y _
    have := abs_min_sub_min_le_max (f y) x (f y) x0
    simpa using this
  have b2 : ‖∫ y in x..x0, min (f y) x0‖ ≤ (|f 0| + |f 1| + 1) * |x0 - x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    have hy' : y ∈ Set.Icc (0:ℝ) 1 := Set.uIcc_subset_Icc hx hx0 (Set.uIoc_subset_uIcc hy)
    have a1 := hf h0 hy' hy'.1
    have a2 := hf hy' h1 hy'.2
    have a3 : |f y| ≤ |f 0| + |f 1| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (f 0), neg_abs_le (f 1), le_abs_self (f 0), le_abs_self (f 1)]
    have a4 := abs_min_sub_min_le_max (f y) x0 (0:ℝ) 0
    have a5 : |min (f y) x0| ≤ |f y| + 1 := by
      have := hx0.2
      have h6 : |min (f y) x0| ≤ max |f y| |x0| := by
        rcases min_choice (f y) x0 with h | h <;> rw [h]
        · exact le_max_left _ _
        · exact le_max_right _ _
      have h7 : |x0| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx0.1, hx0.2]
      rcases max_cases |f y| |x0| with h | h <;> linarith [abs_nonneg (f y)]
    simpa [Real.norm_eq_abs] using (by linarith : |min (f y) x0| ≤ |f 0| + |f 1| + 1)
  have hx1 : |1 - x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hxx : |x0 - x| = |x - x0| := abs_sub_comm _ _
  have hn : 0 ≤ |x - x0| := abs_nonneg _
  rw [Real.norm_eq_abs] at b1 b2
  calc |(∫ y in x..1, (min (f y) x - min (f y) x0)) + ∫ y in x..x0, min (f y) x0|
      ≤ |∫ y in x..1, (min (f y) x - min (f y) x0)| + |∫ y in x..x0, min (f y) x0| := abs_add_le _ _
    _ ≤ _ := by
      rw [hxx] at b2
      nlinarith [abs_nonneg (f 0), abs_nonneg (f 1), mul_le_mul_of_nonneg_left hx1 hn]

theorem solution (f : ℝ → ℝ) (hf : InDprime f) :
    ContinuousOn (Gf f) (Set.Icc 0 1) := by
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hT1 := (gdi_T1_lip f hf.1).continuousOn
  have hT3 : ContinuousOn (fun x => ∫ y in (0:ℝ)..x, f y) (Set.Icc 0 1) := by
    have hI : IntegrableOn f (Set.uIcc (0:ℝ) 1) volume := by
      rw [Set.uIcc_of_le zero_le_one]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 (gdi_int_anti f hf.1 0 1 h0 h1)
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := 1) hI
    rwa [Set.uIcc_of_le zero_le_one] at this
  unfold Gf
  exact (hT1.add (continuousOn_pow 2)).sub hT3
