-- Prove2me | solution 1 for ModernOnlineLearning.SaddlePoint.theorem_15_12
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:36:58.51552+00:00
-- url     : https://prove2.me/submissions/af373a94-56d9-46c5-a2ef-576fc911a3a4

import Definitions.Def_ModernOnlineLearning_SaddlePoint_Setting

set_option autoImplicit false
open ModernOnlineLearning.SaddlePoint

theorem solution {EX EY : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] [FiniteDimensional ℝ EY]
    (X : Set EX) (Y : Set EY) (f : EX → EY → ℝ)
    (x : ℕ → EX) (y : ℕ → EY) (T : ℕ)
    (hT : 1 ≤ T) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXclosed : IsClosed X) (hYclosed : IsClosed Y)
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hx : ∀ t ∈ Finset.Icc 1 T, x t ∈ X)
    (hy : ∀ t ∈ Finset.Icc 1 T, y t ∈ Y)
    (hfx : ∀ v ∈ Y, ConvexOn ℝ X (fun w => f w v))
    (hfy : ∀ u ∈ X, ConcaveOn ℝ Y (f u))
    (xm : EX) (ym : EY)
    (hmin : ModernOnlineLearning.SaddlePoint.IsMinOn X (fun w => f w (avg T y)) xm)
    (hmax : ModernOnlineLearning.SaddlePoint.IsMaxOn Y (f (avg T x)) ym) :
    (∀ u ∈ X,
      (∑ t ∈ Finset.Icc 1 T, f (x t) (y t)) / T -
        (∑ t ∈ Finset.Icc 1 T, f u (y t)) / T =
        (∑ t ∈ Finset.Icc 1 T, (f (x t) (y t) - f u (y t))) / T) ∧
    (∀ v ∈ Y,
      (∑ t ∈ Finset.Icc 1 T, f (x t) v) / T -
        (∑ t ∈ Finset.Icc 1 T, f (x t) (y t)) / T =
        (∑ t ∈ Finset.Icc 1 T, (f (x t) v - f (x t) (y t))) / T) ∧
    (f (avg T x) ym - f xm (avg T y) ≤
      ((∑ t ∈ Finset.Icc 1 T, (f (x t) (y t) - f xm (y t))) +
        (∑ t ∈ Finset.Icc 1 T, (f (x t) ym - f (x t) (y t)))) / T)  := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hcard : (Finset.Icc 1 T).card = T := by simp
  have hweights : (∑ t ∈ Finset.Icc 1 T, (T : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, hcard, nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt hTp)
  have hnonneg : ∀ t ∈ Finset.Icc 1 T, (0:ℝ) ≤ (T:ℝ)⁻¹ := by intros; positivity
  have hcx := (hfx ym hmax.1).map_sum_le hnonneg hweights hx
  have hcy := (hfy xm hmin.1).le_map_sum hnonneg hweights hy
  simp only [← Finset.smul_sum, smul_eq_mul, ← Finset.mul_sum] at hcx hcy
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    rw [Finset.sum_sub_distrib, sub_div]
  · intro v hv
    rw [Finset.sum_sub_distrib, sub_div]
  · rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [avg, div_eq_inv_mul, mul_add, mul_sub]
    linarith

