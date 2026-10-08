-- Prove2me | solution 1 for GoldsteinProj.Conv.proj_inner_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:21:04.306826+00:00
-- url     : https://prove2.me/submissions/30aad2ca-89fb-4279-98f5-38a4bae7af66

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

set_option autoImplicit false

open Filter Topology RealInnerProductSpace

open GoldsteinProj.Conv RealInnerProductSpace in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P) :
    ∀ x : H, ∀ y ∈ C, ‖P x - y‖ ^ 2 ≤ ⟪x - y, P x - y⟫ := by
  intro x y hy
  obtain ⟨hPx, hmin⟩ := hP x
  have : Nonempty C := ⟨⟨P x, hPx⟩⟩
  have heq : ‖x - P x‖ = ⨅ w : C, ‖x - w‖ := by
    apply le_antisymm
    · exact le_ciInf (fun w => hmin w w.2)
    · have hbdd : BddBelow (Set.range fun w : C => ‖x - (w : H)‖) :=
        ⟨(0 : ℝ), by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
      exact ciInf_le hbdd (⟨P x, hPx⟩ : C)
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hCv hPx).1 heq y hy
  have hsplit : x - y = (x - P x) + (P x - y) := by abel
  have hneg : y - P x = -(P x - y) := by abel
  rw [hneg, inner_neg_right] at hvi
  rw [hsplit, inner_add_left, real_inner_self_eq_norm_sq]
  linarith
