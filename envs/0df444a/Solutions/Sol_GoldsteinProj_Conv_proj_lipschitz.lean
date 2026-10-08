-- Prove2me | solution 1 for GoldsteinProj.Conv.proj_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:20:03.058822+00:00
-- url     : https://prove2.me/submissions/88599a79-bf3c-442b-ba57-089e68a8792d

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

set_option autoImplicit false

open GoldsteinProj.Conv in
theorem cf7f5442_vi {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P) (x : H) :
    ∀ w ∈ C, ⟪x - P x, w - P x⟫ ≤ 0 := by
  have hPx := (hP x).1
  have hmin := (hP x).2
  have : Nonempty C := ⟨⟨P x, hPx⟩⟩
  have heq : ‖x - P x‖ = ⨅ w : C, ‖x - w‖ := by
    apply le_antisymm
    · exact le_ciInf (fun w => hmin w w.2)
    · exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨P x, hPx⟩ : C)
  exact (norm_eq_iInf_iff_real_inner_le_zero hCv hPx).1 heq

open GoldsteinProj.Conv in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P) :
    ∃ K : NNReal, LipschitzWith K P := by
  refine ⟨1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h1 := cf7f5442_vi C hCv P hP x (P y) (hP y).1
  have h2 := cf7f5442_vi C hCv P hP y (P x) (hP x).1
  have key : ‖P x - P y‖ ^ 2 ≤ ⟪x - y, P x - P y⟫ := by
    have e1 : ⟪x - P x, P y - P x⟫ + ⟪y - P y, P x - P y⟫
        = ⟪x - y, P y - P x⟫ + ‖P x - P y‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm (P x) (P y),
        real_inner_comm x (P y), real_inner_comm y (P x), real_inner_comm x y,
        real_inner_comm (P x) x, real_inner_comm (P y) y]
      ring
    have e2 : ⟪x - y, P y - P x⟫ = -⟪x - y, P x - P y⟫ := by
      rw [← inner_neg_right, neg_sub]
    linarith
  have hcs : ⟪x - y, P x - P y⟫ ≤ ‖x - y‖ * ‖P x - P y‖ := real_inner_le_norm _ _
  by_cases hz : ‖P x - P y‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hpos : 0 < ‖P x - P y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith
