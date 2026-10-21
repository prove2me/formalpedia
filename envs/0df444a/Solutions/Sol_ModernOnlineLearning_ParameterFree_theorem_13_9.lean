-- Prove2me | solution 1 for ModernOnlineLearning.ParameterFree.theorem_13_9
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T05:15:21.580792+00:00
-- url     : https://prove2.me/submissions/bb616207-54b8-41f8-81a4-391334a4afb8

import Theorems.Thm_ModernOnlineLearning_ParameterFree_kt_one_dim_regret

open ModernOnlineLearning.ParameterFree

theorem solution (d : ℕ) (hd : 0 < d) (ε L : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (T : ℕ) (hT : 1 ≤ T)
    (ℓ : ℕ → (Fin d → ℝ) → ℝ) (g x : ℕ → Fin d → ℝ)
    (hrun : IsCoordKTRun ε L T ℓ g x) :
    ∀ u : Fin d → ℝ,
      (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
        L * (∑ i : Fin d, |u i| * Real.sqrt
          (2 * (T : ℝ) * Real.log
            (1 + Real.exp 1 * |u i| * (T : ℝ) / ε))) + (d : ℝ) * ε * L ∧
      L * (∑ i : Fin d, |u i| * Real.sqrt
        (2 * (T : ℝ) * Real.log
          (1 + Real.exp 1 * |u i| * (T : ℝ) / ε))) + (d : ℝ) * ε * L ≤
        (∑ i : Fin d, |u i|) * L * Real.sqrt
          (2 * (T : ℝ) * Real.log
            (1 + Real.exp 1 * ‖u‖ * (T : ℝ) / ε)) + (d : ℝ) * ε * L := by
  classical
  intro u
  have hcoord (i : Fin d) : IsOneDKTRun ε L T (fun t y => g t i * y)
      (fun t => g t i) (fun t => x t i) := by
    refine ⟨fun t ht => hrun.1 t ht i, ?_, ?_⟩
    · intro t ht
      refine ⟨?_, (hrun.2.1 t ht).2 i⟩
      intro y
      dsimp
      ring_nf
      exact le_rfl
    · intro t ht z
      refine ⟨g t i, ?_⟩
      intro y
      dsimp
      ring_nf
      exact le_rfl
  have hi (i : Fin d) := kt_one_dim_regret ε L hε hL T hT
    (fun t y => g t i * y) (fun t => g t i) (fun t => x t i) (hcoord i) (u i)
  constructor
  · calc
      _ ≤ ∑ t ∈ Finset.Icc 1 T, ∑ i : Fin d, (g t i * x t i - g t i * u i) := by
        apply Finset.sum_le_sum
        intro t ht
        have h := (hrun.2.1 t ht).1 u
        simp only [Finset.sum_sub_distrib, mul_sub] at h ⊢
        linarith
      _ = ∑ i : Fin d, ∑ t ∈ Finset.Icc 1 T, (g t i * x t i - g t i * u i) := by
        rw [Finset.sum_comm]
      _ ≤ ∑ i : Fin d, (|u i| * L * Real.sqrt
          (2 * (T : ℝ) * Real.log (1 + Real.exp 1 * |u i| * (T : ℝ) / ε)) + ε * L) :=
        Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          ring
        · ring
  · have hbound (i : Fin d) : |u i| ≤ ‖u‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i
    have hs : (∑ i : Fin d, |u i| * Real.sqrt
        (2 * (T : ℝ) * Real.log (1 + Real.exp 1 * |u i| * (T : ℝ) / ε))) ≤
        ∑ i : Fin d, |u i| * Real.sqrt
        (2 * (T : ℝ) * Real.log (1 + Real.exp 1 * ‖u‖ * (T : ℝ) / ε)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.log_le_log (by positivity)
      gcongr
      exact hbound i
    have h := mul_le_mul_of_nonneg_left hs hL.le
    rw [← Finset.sum_mul] at h
    nlinarith

