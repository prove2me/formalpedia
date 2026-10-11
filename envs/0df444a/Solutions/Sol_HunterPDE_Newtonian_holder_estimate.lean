-- Prove2me | solution 1 for HunterPDE.Newtonian.holder_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T16:33:49.412166+00:00
-- url     : https://prove2.me/submissions/5046cd82-135e-4ae4-852c-4c144760e58d

import Theorems.Thm_HunterPDE_Newtonian_secondPartial_newtonianPotential_ball
import Theorems.Thm_HunterPDE_Newtonian_cancelled_hessian_ball_difference_le
import Theorems.Thm_HunterPDE_Shared_holderSeminorm_le_iff
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory HunterPDE.Newtonian
open scoped ContDiff ENNReal NNReal

theorem solution (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ i j : Fin n,
        HunterPDE.Shared.holderSeminorm α Set.univ (secondPartial (newtonianPotential n f) i j) ≤
          (C : ℝ≥0∞) * HunterPDE.Shared.holderSeminorm α Set.univ f := by
  classical
  obtain ⟨A, hA⟩ := cancelled_hessian_ball_difference_le n hn α hα₀ hα₁
  refine ⟨A + 1, ?_⟩
  intro f hf hfc i j
  by_cases hs : HunterPDE.Shared.holderSeminorm α Set.univ f = (⊤ : ℝ≥0∞)
  · simp [hs]
  · let H : ℝ≥0 := (HunterPDE.Shared.holderSeminorm α Set.univ f).toNNReal
    have hH : (H : ℝ≥0∞) = HunterPDE.Shared.holderSeminorm α Set.univ f :=
      ENNReal.coe_toNNReal hs
    have hincr : ∀ x y, |f x - f y| ≤ (H : ℝ) * ‖x - y‖ ^ α := by
      have hbound := (HunterPDE.Shared.holderSeminorm_le_iff n α Set.univ f H).mp
        (le_of_eq hH.symm)
      intro x y
      by_cases hxy : x = y
      · subst y
        simp only [sub_self, abs_zero]
        positivity
      · exact hbound x (Set.mem_univ x) y (Set.mem_univ y) hxy
    have hresult : HunterPDE.Shared.holderSeminorm α Set.univ
        (secondPartial (newtonianPotential n f) i j) ≤ (((A + 1) * H : ℝ≥0) : ℝ≥0∞) := by
      apply (HunterPDE.Shared.holderSeminorm_le_iff n α Set.univ _ ((A + 1) * H)).mpr
      intro x _ x' _ _
      obtain ⟨Rx, hRx, hsx⟩ := hfc.isCompact.isBounded.subset_ball_lt 0 x
      obtain ⟨Ry, hRy, hsy⟩ := hfc.isCompact.isBounded.subset_ball_lt 0 x'
      let R := max Rx Ry
      have hR : 0 < R := hRx.trans_le (le_max_left _ _)
      have hsuppx : tsupport f ⊆ Metric.ball x R :=
        hsx.trans (Metric.ball_subset_ball (le_max_left _ _))
      have hsuppy : tsupport f ⊆ Metric.ball x' R :=
        hsy.trans (Metric.ball_subset_ball (le_max_right _ _))
      have hx := (secondPartial_newtonianPotential_ball n hn f hf hfc x R hR hsuppx i j).2
      have hy := (secondPartial_newtonianPotential_ball n hn f hf hfc x' R hR hsuppy i j).2
      have hI := hA f hf hfc H hincr x x' R hR hsuppx hsuppy i j
      let c : ℝ := 1 / (n : ℝ) * (if i = j then 1 else 0)
      have hc : |c| ≤ 1 := by
        have hn1 : (1 : ℝ) ≤ n := by
          exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) hn)
        dsimp [c]
        split_ifs
        · simpa [abs_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ))] using
            (div_le_one (by linarith : (0 : ℝ) < n)).mpr hn1
        · norm_num
      have hcinc : |c * (f x - f x')| ≤ (H : ℝ) * ‖x - x'‖ ^ α := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right hc (abs_nonneg _)).trans (by simpa using hincr x x')
      rw [hx, hy]
      have heq (a b : ℝ) :
          (a - 1 / (n : ℝ) * f x * (if i = j then 1 else 0)) -
            (b - 1 / (n : ℝ) * f x' * (if i = j then 1 else 0)) =
          (a - b) - c * (f x - f x') := by dsimp [c]; ring
      rw [heq]
      calc
        _ ≤ _ := by
          simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le _ (0 : ℝ) _)
        _ ≤ (A : ℝ) * (H : ℝ) * ‖x - x'‖ ^ α + (H : ℝ) * ‖x - x'‖ ^ α :=
          add_le_add hI hcinc
        _ = ((((A + 1) * H : ℝ≥0) : ℝ)) * ‖x - x'‖ ^ α := by
          simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one]
          ring
    simpa only [ENNReal.coe_mul, hH] using hresult
