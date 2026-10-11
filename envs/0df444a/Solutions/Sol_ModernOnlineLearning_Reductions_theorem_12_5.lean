-- Prove2me | solution 1 for ModernOnlineLearning.Reductions.theorem_12_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:15:48.449528+00:00
-- url     : https://prove2.me/submissions/4c91f92e-a5cf-4469-b5fc-47d60e5dac4d

import Mathlib
import Definitions.Def_ModernOnlineLearning_Reductions_Setting

namespace RRAux_ModernOnlineLearning_Reductions_theorem_12_5

open ModernOnlineLearning.Reductions

theorem round_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : Fin 4) (V : Set E) (l : E → ℝ) (g q : E →L[ℝ] ℝ) (x z u : E)
    (hu : u ∈ V) (hproj : IsProjection V z x)
    (hsub : ModernOnlineLearning.OMD.IsSubgradientOn V l x g)
    (hq : IsSubgradient (distance V) z q) :
    l x - l u ≤ surrogate k V g q x z z - surrogate k V g q x z u := by
  have hl : l x - l u ≤ g (x - u) := by
    have := hsub u hu
    have h2 : g (u - x) = - g (x - u) := by
      rw [← map_neg]; congr 1; abel
    linarith
  have hdu : distance V u = 0 := Metric.infDist_zero_of_mem hu
  have hdz : distance V z = ‖x - z‖ := by rw [← hproj.2, norm_sub_rev]
  have hgsplit : g (x - u) = g (x - z) + g (z - u) := by
    rw [← map_add]; congr 1; abel
  have hqz : distance V z ≤ q z - q u := by
    have := hq u
    rw [hdu] at this
    have h2 : q (u - z) = q u - q z := map_sub _ _ _
    linarith
  have hgle : g (x - z) ≤ ‖g‖ * ‖x - z‖ :=
    le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using g.le_opNorm (x - z))
  have hgnn : 0 ≤ ‖g‖ := norm_nonneg _
  have hzu : g z - g u = g (z - u) := (map_sub _ _ _).symm
  -- the c identity
  have hc : 0 < g (x - z) →
      g ((‖x - z‖)⁻¹ • (x - z)) * ‖x - z‖ = g (x - z) ∧
      0 < g ((‖x - z‖)⁻¹ • (x - z)) := by
    intro hpos
    have hne : x - z ≠ 0 := by
      intro h; rw [h, map_zero] at hpos; exact lt_irrefl _ hpos
    have hn : 0 < ‖x - z‖ := norm_pos_iff.mpr hne
    rw [map_smul, smul_eq_mul]
    refine ⟨?_, mul_pos (inv_pos.mpr hn) hpos⟩
    field_simp
  fin_cases k
  · simp only [surrogate]
    simp only [Fin.isValue, Fin.val_zero, if_true]
    rw [hdu, hdz]
    nlinarith
  · simp only [surrogate]
    simp only [Fin.isValue, Fin.val_one, one_ne_zero, if_false, if_true]
    have := mul_le_mul_of_nonneg_left hqz hgnn
    rw [hdz] at this
    nlinarith
  · simp only [surrogate]
    simp only [Fin.isValue, Fin.reduceFinMk, Fin.val_two, OfNat.ofNat_ne_zero, if_false, if_true,
      show (2:ℕ) ≠ 0 from by decide, show (2:ℕ) ≠ 1 from by decide]
    by_cases h : g (x - z) ≤ 0
    · simp only [h, if_true]; linarith
    · simp only [h, if_false]
      obtain ⟨h1, _⟩ := hc (lt_of_not_ge h)
      rw [hdu, hdz]
      linarith
  · simp only [surrogate]
    simp only [Fin.isValue, Fin.reduceFinMk,
      show ((3 : Fin 4) : ℕ) = 3 from rfl,
      show (3:ℕ) ≠ 0 from by decide, show (3:ℕ) ≠ 1 from by decide,
      show (3:ℕ) ≠ 2 from by decide, if_false]
    by_cases h : g (x - z) ≤ 0
    · simp only [h, if_true]; linarith
    · simp only [h, if_false]
      obtain ⟨h1, h2⟩ := hc (lt_of_not_ge h)
      have := mul_le_mul_of_nonneg_left hqz h2.le
      rw [hdz] at this
      have e : g ((‖x - z‖)⁻¹ • (x - z)) * q z - g ((‖x - z‖)⁻¹ • (x - z)) * q u
          = g ((‖x - z‖)⁻¹ • (x - z)) * (q z - q u) := by ring
      linarith

end RRAux_ModernOnlineLearning_Reductions_theorem_12_5

open ModernOnlineLearning.Reductions in
-- Orabona, Theorem 12.5
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V W : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V) (hVW : V ⊆ W)
    (loss : ℕ → E → ℝ) (z x : ℕ → E) (g q : ℕ → E →L[ℝ] ℝ)
    (T : ℕ) (hT : 1 ≤ T) (hRun : IsProjectedRun V W loss z x g q T)
    (u : E) (hu : u ∈ V) :
    ∀ k : Fin 4, ModernOnlineLearning.OGD.regret loss x u T ≤ surrogateRegret k V z x g q u T := by
  intro k
  unfold ModernOnlineLearning.OGD.regret surrogateRegret
  apply Finset.sum_le_sum
  intro t ht
  obtain ⟨_, hp, hs, hq⟩ := hRun t ht
  exact RRAux_ModernOnlineLearning_Reductions_theorem_12_5.round_le k V (loss t) (g t) (q t)
    (x t) (z t) u hu hp hs hq

#print axioms solution
