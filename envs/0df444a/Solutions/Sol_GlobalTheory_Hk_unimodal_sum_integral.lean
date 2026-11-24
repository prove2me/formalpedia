-- Prove2me | solution 1 for GlobalTheory.Hk.unimodal_sum_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:35:07.694447+00:00
-- url     : https://prove2.me/submissions/365019dc-60b4-4a26-9d11-f9863e2b86d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution (f : ℝ → ℝ) (h0 : ∀ t, 0 ≤ f t)
    (hf : ∀ s t, |s| ≤ |t| → f t ≤ f s) (x₀ : ℝ) (n : ℕ) :
    |∑ i ∈ Finset.range n, f (x₀ + i) - ∫ t in x₀..x₀ + n, f t| ≤ f 0 := by
  have hmono : MonotoneOn f (Set.Iic 0) := by
    intro s hs t ht hst
    apply hf
    rw [abs_of_nonpos (Set.mem_Iic.mp ht), abs_of_nonpos (Set.mem_Iic.mp hs)]
    linarith
  have hanti : AntitoneOn f (Set.Ici 0) := by
    intro s hs t ht hst
    apply hf
    rw [abs_of_nonneg (Set.mem_Ici.mp hs), abs_of_nonneg (Set.mem_Ici.mp ht)]
    exact hst
  have hI0 : ∀ a : ℝ, IntervalIntegrable f MeasureTheory.volume a 0 := by
    intro a
    rcases le_total a 0 with ha | ha
    · apply MonotoneOn.intervalIntegrable
      apply hmono.mono
      rw [Set.uIcc_of_le ha]
      exact Set.Icc_subset_Iic_self
    · apply AntitoneOn.intervalIntegrable
      apply hanti.mono
      rw [Set.uIcc_of_ge ha]
      exact Set.Icc_subset_Ici_self
  have hI : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => (hI0 a).trans (hI0 b).symm
  have hle0 : ∀ t, f t ≤ f 0 := fun t => hf 0 t (by simp)
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ y, G y = f (min y 0) := ⟨_, fun _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ, ∀ y, H y = f (max y 0) := ⟨_, fun _ => rfl⟩
  have hPA : ∀ p t, p ≤ t → t ≤ p + 1 → f t ≤ f p + (G (p + 1) - G p) := by
    intro p t hpt htq
    rw [hG, hG]
    rcases le_total 0 p with hp | hp
    · rw [min_eq_right hp, min_eq_right (by linarith : (0:ℝ) ≤ p + 1)]
      have : f t ≤ f p := hf p t (by
        rw [abs_of_nonneg hp, abs_of_nonneg (by linarith : (0:ℝ) ≤ t)]; exact hpt)
      linarith
    · rw [min_eq_left hp]
      rcases le_total (p + 1) 0 with hq | hq
      · rw [min_eq_left hq]
        have : f t ≤ f (p + 1) := hf (p + 1) t (by
          rw [abs_of_nonpos hq, abs_of_nonpos (by linarith : t ≤ 0)]; linarith)
        linarith
      · rw [min_eq_right hq]
        have := hle0 t
        linarith
  have hPB : ∀ p t, p ≤ t → t ≤ p + 1 → f p - (H p - H (p + 1)) ≤ f t := by
    intro p t hpt htq
    rw [hH, hH]
    rcases le_total 0 p with hp | hp
    · rw [max_eq_left hp, max_eq_left (by linarith : (0:ℝ) ≤ p + 1)]
      have : f (p + 1) ≤ f t := hf t (p + 1) (by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t), abs_of_nonneg (by linarith : (0:ℝ) ≤ p + 1)]
        exact htq)
      linarith
    · rw [max_eq_right hp]
      rcases le_total (p + 1) 0 with hq | hq
      · rw [max_eq_right hq]
        have : f p ≤ f t := hf t p (by
          rw [abs_of_nonpos (by linarith : t ≤ 0), abs_of_nonpos hp]; linarith)
        linarith
      · rw [max_eq_left hq]
        have h1 := hle0 p
        have h2 := hle0 (p + 1)
        rcases le_total t 0 with ht | ht
        · have : f p ≤ f t := hf t p (by rw [abs_of_nonpos ht, abs_of_nonpos hp]; linarith)
          linarith
        · have : f (p + 1) ≤ f t := hf t (p + 1) (by
            rw [abs_of_nonneg ht, abs_of_nonneg hq]; linarith)
          linarith
  have hA : ∀ p, ∫ t in p..p + 1, f t ≤ f p + (G (p + 1) - G p) := by
    intro p
    have := intervalIntegral.integral_mono_on (by linarith : p ≤ p + 1) (hI p (p + 1))
      intervalIntegrable_const (fun t ht => hPA p t ht.1 ht.2)
    rw [intervalIntegral.integral_const, show p + 1 - p = 1 by ring, one_smul] at this
    exact this
  have hB : ∀ p, f p - (H p - H (p + 1)) ≤ ∫ t in p..p + 1, f t := by
    intro p
    have := intervalIntegral.integral_mono_on (by linarith : p ≤ p + 1) intervalIntegrable_const
      (hI p (p + 1)) (fun t ht => hPB p t ht.1 ht.2)
    rw [intervalIntegral.integral_const, show p + 1 - p = 1 by ring, one_smul] at this
    exact this
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := f) (a := fun i : ℕ => x₀ + (i : ℝ)) (n := n) (fun k _ => hI _ _)
  simp only [Nat.cast_zero, add_zero, Nat.cast_succ, ← add_assoc] at hsplit
  rw [← hsplit]
  have tG : ∑ i ∈ Finset.range n, (G (x₀ + i + 1) - G (x₀ + i)) = G (x₀ + n) - G x₀ := by
    have := Finset.sum_range_sub (fun i : ℕ => G (x₀ + i)) n
    simpa [Nat.cast_succ, add_assoc] using this
  have tH : ∑ i ∈ Finset.range n, (H (x₀ + i) - H (x₀ + i + 1)) = H x₀ - H (x₀ + n) := by
    have := Finset.sum_range_sub' (fun i : ℕ => H (x₀ + i)) n
    simpa [Nat.cast_succ, add_assoc] using this
  have hG0 : G (x₀ + n) ≤ f 0 := by rw [hG]; exact hle0 _
  have hG1 : 0 ≤ G x₀ := by rw [hG]; exact h0 _
  have hH0 : H x₀ ≤ f 0 := by rw [hH]; exact hle0 _
  have hH1 : 0 ≤ H (x₀ + n) := by rw [hH]; exact h0 _
  rw [abs_sub_le_iff]
  constructor
  · have : (∑ i ∈ Finset.range n, f (x₀ + i)) - (∑ i ∈ Finset.range n, ∫ t in x₀ + i..x₀ + i + 1, f t)
        ≤ ∑ i ∈ Finset.range n, (H (x₀ + i) - H (x₀ + i + 1)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro i _
      have := hB (x₀ + i)
      linarith
    linarith
  · have : (∑ i ∈ Finset.range n, ∫ t in x₀ + i..x₀ + i + 1, f t) - (∑ i ∈ Finset.range n, f (x₀ + i))
        ≤ ∑ i ∈ Finset.range n, (G (x₀ + i + 1) - G (x₀ + i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro i _
      have := hA (x₀ + i)
      linarith
    linarith
end GlobalTheory.Hk
