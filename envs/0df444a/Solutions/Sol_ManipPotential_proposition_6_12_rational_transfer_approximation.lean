-- Prove2me | solution 1 for ManipPotential.proposition_6_12_rational_transfer_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:58:16.694949+00:00
-- url     : https://prove2.me/submissions/74d10010-c1d1-4271-8b62-044f5b7ff404

import Mathlib
import Definitions.Def_ManipPotential_TransferVectors
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec
import Definitions.Def_ManipPotential_ExtRanking

open scoped NNReal Pointwise

open ManipPotential

theorem solution {m : ℕ} [NeZero m]
    (K : ℕ) (G : ((ExtRanking m → ℝ) × ℝ) → (Ranking m → ℝ))
    (z₀ : ((ExtRanking m → ℝ) × ℝ)) (i j : Fin m)
    (hmem :
      let D : ((ExtRanking m → ℝ) × ℝ) →ₗ[ℝ] (Ranking m → ℝ) :=
        (fderiv ℝ G z₀).toLinearMap
      let T : Submodule ℝ (Ranking m → ℝ) := LinearMap.range D
      let C : Submodule ℝ≥0 (Ranking m → ℝ) :=
        Submodule.span ℝ≥0 (TransferVectors ((K : ℝ) + 1) i j)
      (-(unitVec (ell i) - unitVec (ell j))) ∈
        closure ((C : Set (Ranking m → ℝ)) + (T : Set (Ranking m → ℝ))))
    (η : ℝ) (hη : 0 < η) :
    ∃ (v : ((ExtRanking m → ℝ) × ℝ)) (q : ℕ)
      (u : Fin q → Ranking m → ℝ) (β : Fin q → ℚ),
      (∀ h, u h ∈ TransferVectors ((K : ℝ) + 1) i j) ∧
      (∀ h, 0 ≤ β h) ∧
      ‖(∑ h, (β h : ℝ) • u h) -
        ((fderiv ℝ G z₀) v - (unitVec (ell i) - unitVec (ell j)))‖ < η := by
  dsimp only at hmem
  set V : Ranking m → ℝ := unitVec (ell i) - unitVec (ell j) with hV
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨b, hb, hdist⟩ := hmem (η / 2) (by linarith)
  obtain ⟨c0, hc0, t, ht, rfl⟩ := Set.mem_add.mp hb
  rw [SetLike.mem_coe, LinearMap.mem_range] at ht
  obtain ⟨w, rfl⟩ := ht
  rw [SetLike.mem_coe, Submodule.mem_span_set'] at hc0
  obtain ⟨n, f, g, hfg⟩ := hc0
  set δ : Fin n → ℝ := fun h => η / (2 * ((n : ℝ) + 1) * (‖(g h : Ranking m → ℝ)‖ + 1)) with hδ
  have hδpos : ∀ h, 0 < δ h := fun h => by
    simp only [hδ]; positivity
  have hex : ∀ h, ∃ β : ℚ, (f h : ℝ) < β ∧ (β : ℝ) < f h + δ h := fun h =>
    exists_rat_btwn (by linarith [hδpos h])
  choose β hβ1 hβ2 using hex
  refine ⟨-w, n, fun h => (g h : Ranking m → ℝ), β, fun h => (g h).2, fun h => ?_, ?_⟩
  · have := lt_of_le_of_lt (NNReal.coe_nonneg _) (hβ1 h)
    exact_mod_cast this.le
  · have key : (∑ h, (β h : ℝ) • (g h : Ranking m → ℝ)) - ((fderiv ℝ G z₀) (-w) - V) =
        (∑ h, ((β h : ℝ) - f h) • (g h : Ranking m → ℝ)) -
          (-V - (∑ h, f h • (g h : Ranking m → ℝ) + (fderiv ℝ G z₀).toLinearMap w)) := by
      simp only [sub_smul, Finset.sum_sub_distrib, map_neg, NNReal.smul_def,
        ContinuousLinearMap.coe_coe]
      abel
    rw [key]
    rw [hfg] at *
    have h2 : ‖-V - (c0 + (fderiv ℝ G z₀).toLinearMap w)‖ < η / 2 := by
      rw [← dist_eq_norm]; exact hdist
    have h1 : ‖∑ h, ((β h : ℝ) - f h) • (g h : Ranking m → ℝ)‖ ≤ η / 2 := by
      calc ‖∑ h, ((β h : ℝ) - f h) • (g h : Ranking m → ℝ)‖
          ≤ ∑ h, ‖((β h : ℝ) - f h) • (g h : Ranking m → ℝ)‖ := norm_sum_le _ _
        _ ≤ ∑ _h : Fin n, η / (2 * ((n : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro h _
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hβ1 h])]
          have hg0 : 0 ≤ ‖(g h : Ranking m → ℝ)‖ := norm_nonneg _
          have e : δ h * (‖(g h : Ranking m → ℝ)‖ + 1) = η / (2 * ((n : ℝ) + 1)) := by
            simp only [hδ]; field_simp
          rw [← e]
          have : (β h : ℝ) - f h ≤ δ h := by linarith [hβ2 h]
          calc ((β h : ℝ) - f h) * ‖(g h : Ranking m → ℝ)‖
              ≤ δ h * ‖(g h : Ranking m → ℝ)‖ := mul_le_mul_of_nonneg_right this hg0
            _ ≤ δ h * (‖(g h : Ranking m → ℝ)‖ + 1) := by nlinarith [hδpos h]
        _ = (n : ℝ) * (η / (2 * ((n : ℝ) + 1))) := by simp
        _ ≤ η / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
    calc _ ≤ ‖∑ h, ((β h : ℝ) - f h) • (g h : Ranking m → ℝ)‖ +
          ‖-V - (c0 + (fderiv ℝ G z₀).toLinearMap w)‖ := norm_sub_le _ _
      _ < η := by linarith
