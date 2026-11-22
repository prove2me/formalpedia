-- Prove2me | solution 1 for Main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:22:38.52693+00:00
-- url     : https://prove2.me/submissions/bc4785e4-20e6-412f-b432-4fe6c8a61ae6

import Definitions.Def_PHigherOrder_HolderFromJets
import Definitions.Def_PHigherOrder_JetBounds
import Definitions.Def_PHigherOrder_LocalBoundednessInput
import Definitions.Def_PHigherOrder_Main
import Theorems.Thm_HolderFromJets
import Theorems.Thm_JetBounds


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hLR : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (hsm : SmoothAwayFromCriticalInput p) (hS : DivFormSchauderInput)
    (hLB : LocalBoundednessInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) u g →
        MeasureTheory.MemLp u (ENNReal.ofReal p)
          (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1)) →
        (∀ j : ℕ, j ≤ k → ∀ x ∈ Metric.ball (0 : Plane) (1 / 2), ∀ w : Plane,
            |iteratedFDeriv ℝ j u x (fun _ => w)|
              ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                    (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                * ‖w‖ ^ j)
          ∧ (∀ x ∈ Metric.ball (0 : Plane) (1 / 2), ∀ y ∈ Metric.ball (0 : Plane) (1 / 2),
              ∀ w : Plane,
                |iteratedFDeriv ℝ k u x (fun _ => w) - iteratedFDeriv ℝ k u y (fun _ => w)|
                  ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                        (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                    * ‖x - y‖ ^ β * ‖w‖ ^ k) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := JetBounds p hp hp2 hLR F hIM hsm hS hLB k hk β hβ0 hβ1 hks
  obtain ⟨C₂, hC₂pos, hC₂⟩ := HolderFromJets p hp hp2 hLR F hIM hsm hS hLB k hk β hβ0 hβ1 hks
  refine ⟨max C₁ (max C₂ hLB.Cb), lt_of_lt_of_le hC₁pos (le_max_left _ _), ?_⟩
  intro u g hph hLp
  have hN : (0:ℝ) ≤ (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
      (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal :=
    ENNReal.toReal_nonneg
  refine ⟨?_, ?_⟩
  · intro j hjk x hx w
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      have hx34 : x ∈ Metric.ball (0 : Plane) (3 / 4) :=
        Metric.mem_ball.mpr (by have := Metric.mem_ball.mp hx; linarith)
      have hb := hLB.bound u g hph hLp x hx34
      have hz : |iteratedFDeriv ℝ 0 u x (fun _ => w)| = |u x| := by
        simp [iteratedFDeriv_zero_apply]
      rw [hz, pow_zero, mul_one]
      refine hb.trans (mul_le_mul_of_nonneg_right ?_ hN)
      exact (le_max_right C₂ hLB.Cb).trans (le_max_right C₁ _)
    · refine ((hC₁ u g hph hLp x hx).1 j hj1 hjk w).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hN) (by positivity)
  · intro x hx y hy w
    refine (hC₂ u g hph hLp x hx y hy w).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          ((le_max_left C₂ hLB.Cb).trans (le_max_right C₁ _)) hN)
        (Real.rpow_nonneg (norm_nonneg _) _))
      (by positivity)
