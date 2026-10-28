-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.c1_shift_value_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:01:49.560383+00:00
-- url     : https://prove2.me/submissions/6247f1b8-6980-49c5-83f7-faf7e4f3af7b

import Mathlib
import Definitions.Def_OAIQ10Bp004

open OAI.HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction

theorem solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (α : ℝ) (hα : 0<α) (f : C1HolderSpace E α) :
    Continuous (fun h : ℂ => holderShift α h (c1HolderValue α f)) := by
  set v := c1HolderValue α f with hv
  set F : ℂ →ᵇ E := holderValue α v with hF
  set A : ℂ →ᵇ (ℂ →L[ℝ] E) := holderValue α (c1HolderDeriv α f) with hA
  set DA := holderDifference α (c1HolderDeriv α f) with hDA
  have hder : ∀ z, HasFDerivAt (F : ℂ → E) (A z) z := fun z => c1Holder_hasFDerivAt α f z
  -- first component: Lipschitz with constant ‖A‖
  have h1 : Continuous (fun h : ℂ => (holderShift α h v).val.1) := by
    apply LipschitzWith.continuous (K := ‖A‖₊)
    apply LipschitzWith.of_dist_le_mul
    intro h h0
    refine (BoundedContinuousFunction.dist_le (by positivity)).2 (fun z => ?_)
    change dist (F (z+h)) (F (z+h0)) ≤ _
    rw [dist_eq_norm, dist_eq_norm]
    have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := (F : ℂ → E)) (s := Set.univ) (x := z+h0) (y := z+h)
      (fun w _ => (hder w).hasFDerivWithinAt) (fun w _ => A.norm_coe_le_norm w) convex_univ
      (Set.mem_univ _) (Set.mem_univ _)
    simpa [add_sub_add_left_eq_sub] using this
  have h2 : Continuous (fun h : ℂ => (holderShift α h v).val.2) := by
    apply LipschitzWith.continuous (K := ‖DA‖₊)
    apply LipschitzWith.of_dist_le_mul
    intro h h0
    refine (BoundedContinuousFunction.dist_le (by positivity)).2 (fun p => ?_)
    obtain ⟨⟨x, y⟩, hxy⟩ := p
    have hd : 0 < dist x y := dist_pos.mpr hxy
    have hdα : 0 < (dist x y)^α := Real.rpow_pos_of_pos hd α
    have hrel : ∀ k : ℂ, F (x+k) - F (y+k) =
        (dist x y)^α • holderDifference α v ⟨(x+k, y+k), fun he => hxy (add_right_cancel he)⟩ := by
      intro k
      have := holderSpace_relation α v (x+k) (y+k) (fun he => hxy (add_right_cancel he))
      rw [dist_add_right] at this
      exact this
    have hrelA : ∀ k : ℂ, A (x+k) - A (y+k) =
        (dist x y)^α • DA ⟨(x+k, y+k), fun he => hxy (add_right_cancel he)⟩ := by
      intro k
      have := holderSpace_relation α (c1HolderDeriv α f) (x+k) (y+k) (fun he => hxy (add_right_cancel he))
      rw [dist_add_right] at this
      exact this
    change dist (holderDifference α v ⟨(x+h, y+h), _⟩) (holderDifference α v ⟨(x+h0, y+h0), _⟩) ≤ _
    -- φ k = F(x+k) - F(y+k)
    have hφ : ∀ k, HasFDerivAt (fun k : ℂ => F (x+k) - F (y+k)) (A (x+k) - A (y+k)) k := by
      intro k
      have e1 := (hder (x+k)).comp k ((hasFDerivAt_id k).const_add x)
      have e2 := (hder (y+k)).comp k ((hasFDerivAt_id k).const_add y)
      have e := e1.sub e2
      simp only [ContinuousLinearMap.comp_id] at e
      exact e
    have hb : ∀ k, ‖A (x+k) - A (y+k)‖ ≤ (dist x y)^α * ‖DA‖ := by
      intro k
      rw [hrelA k, norm_smul, Real.norm_eq_abs, abs_of_pos hdα]
      exact mul_le_mul_of_nonneg_left (DA.norm_coe_le_norm _) hdα.le
    have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun k : ℂ => F (x+k) - F (y+k)) (s := Set.univ) (x := h0) (y := h)
      (fun w _ => (hφ w).hasFDerivWithinAt) (fun w _ => hb w) convex_univ
      (Set.mem_univ _) (Set.mem_univ _)
    simp only [hrel] at hmv
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hdα, mul_assoc] at hmv
    rw [dist_eq_norm, dist_eq_norm]
    exact le_of_mul_le_mul_left hmv hdα
  have : (fun h : ℂ => holderShift α h v) = fun h => ⟨((holderShift α h v).val.1, (holderShift α h v).val.2),
      (holderShift α h v).property⟩ := by
    funext h; rfl
  rw [this]
  exact (h1.prodMk h2).subtype_mk _
