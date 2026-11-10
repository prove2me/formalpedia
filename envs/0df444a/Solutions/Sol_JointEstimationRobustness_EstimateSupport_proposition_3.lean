-- Prove2me | solution 1 for JointEstimationRobustness.EstimateSupport.proposition_3
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:07:52.952919+00:00
-- url     : https://prove2.me/submissions/0a63c1fd-dd4b-4990-8edb-d0d308c2bfa9

import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_ConvexDuality
import Definitions.Def_JointEstimationRobustness_EstimateSupport_Estimation

open JointEstimationRobustness.EstimateSupport

theorem solution : ¬ (∀ {M : ℕ} (W Wbar : Set (Fin M → ℝ))
    (ρ : (Fin M → ℝ) → ℝ) (βhat : Fin M → ℝ)
    (hW : W ⊆ Wbar) (hEstimate : IsMinimizingEstimate W ρ βhat)
    (hConvex : ConvexOn ℝ Wbar ρ) (r : ℝ) (hr : 0 < r) (ν : Fin M → ℝ),
    FenchelRobust.Counterpart.supportFun (estimateSet W ρ βhat r) ν =
      ⨅ μ : {t : ℝ // 0 < t},
        ((((estimateValue ρ βhat + r) * (μ : ℝ)) : ℝ) : EReal) +
          ((μ : ℝ) : EReal) *
            FenchelRobust.Counterpart.convexConj Wbar ρ
              (fun i => ν i / (μ : ℝ))) := by
  intro h
  have hW : ({0} : Set (Fin 1 → ℝ)) ⊆ Set.univ := Set.subset_univ _
  have hEst : IsMinimizingEstimate ({0} : Set (Fin 1 → ℝ)) (fun _ => (0 : ℝ)) 0 :=
    ⟨Set.mem_singleton 0, fun _ _ => le_rfl⟩
  have hConv : ConvexOn ℝ (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (0 : ℝ)) :=
    convexOn_const (0 : ℝ) convex_univ
  have heq := h ({0} : Set (Fin 1 → ℝ)) Set.univ (fun _ => (0 : ℝ)) 0 hW hEst hConv 1
    zero_lt_one (fun _ => 1)
  have h_est_set : estimateSet ({0} : Set (Fin 1 → ℝ)) (fun _ => (0 : ℝ)) 0 1 = {0} := by
    ext a
    simp [estimateSet, estimateValue]
  have h_lhs : FenchelRobust.Counterpart.supportFun
      (estimateSet ({0} : Set (Fin 1 → ℝ)) (fun _ => (0 : ℝ)) 0 1) (fun _ => 1) ≤ (0 : EReal) := by
    rw [h_est_set]
    unfold FenchelRobust.Counterpart.supportFun
    refine iSup₂_le ?_
    intro a ha
    rw [Set.mem_singleton_iff.mp ha, dotProduct_zero]
    exact le_rfl
  have h_rhs : (1 : EReal) ≤ ⨅ μ : {t : ℝ // 0 < t},
      ((((estimateValue (fun _ : Fin 1 → ℝ => (0 : ℝ)) 0 + 1) * (μ : ℝ)) : ℝ) : EReal) +
        ((μ : ℝ) : EReal) *
          FenchelRobust.Counterpart.convexConj (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (0 : ℝ))
            (fun i => (1 : ℝ) / (μ : ℝ)) := by
    refine le_iInf ?_
    intro μ
    have hμ : 0 < (μ : ℝ) := μ.2
    have h_conj : (((1 : ℝ) / (μ : ℝ) : ℝ) : EReal) ≤
        FenchelRobust.Counterpart.convexConj (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (0 : ℝ))
          (fun _ => (1 : ℝ) / (μ : ℝ)) := by
      unfold FenchelRobust.Counterpart.convexConj
      refine le_iSup₂_of_le (fun _ : Fin 1 => (1 : ℝ)) (Set.mem_univ _) ?_
      simp [dotProduct]
    have h_mul : (1 : EReal) ≤ ((μ : ℝ) : EReal) *
        FenchelRobust.Counterpart.convexConj (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (0 : ℝ))
          (fun _ => (1 : ℝ) / (μ : ℝ)) := by
      have h1 : (1 : EReal) = (((μ : ℝ) * ((1 : ℝ) / (μ : ℝ)) : ℝ) : EReal) := by
        exact_mod_cast (mul_one_div_cancel (ne_of_gt hμ)).symm
      rw [h1, EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left h_conj (EReal.coe_nonneg.mpr (le_of_lt hμ))
    have h_first : (0 : EReal) ≤
        ((((estimateValue (fun _ : Fin 1 → ℝ => (0 : ℝ)) 0 + 1) * (μ : ℝ)) : ℝ) : EReal) := by
      simp [estimateValue, le_of_lt hμ]
    calc
      (1 : EReal) = 0 + 1 := by simp
      _ ≤ ((((estimateValue (fun _ : Fin 1 → ℝ => (0 : ℝ)) 0 + 1) * (μ : ℝ)) : ℝ) : EReal) +
          ((μ : ℝ) : EReal) *
            FenchelRobust.Counterpart.convexConj (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (0 : ℝ))
              (fun _ => (1 : ℝ) / (μ : ℝ)) := add_le_add h_first h_mul
  rw [heq] at h_lhs
  have h_contra : ((1 : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := le_trans h_rhs h_lhs
  have h_real : (1 : ℝ) ≤ (0 : ℝ) := EReal.coe_le_coe_iff.mp h_contra
  linarith
