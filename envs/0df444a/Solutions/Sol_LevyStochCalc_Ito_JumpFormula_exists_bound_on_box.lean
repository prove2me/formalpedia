-- Prove2me | solution 1 for LevyStochCalc.Ito.JumpFormula.exists_bound_on_box
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:01:20.091214+00:00
-- url     : https://prove2.me/submissions/7c88007d-774d-4cfa-9eb4-a9f3a47fca25

import Definitions.Def_LevyStochCalc_Ito_LocalDerivBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Local bounds on the derivatives of a `C²` state function

A `C²` function of time and state has continuous time derivative, gradient and Hessian, so on a
compact time–space box each of them is bounded. `exists_bound_on_box` packages the three bounds
as a single constant, and `exists_bound_on_box_of_le` reads it along a path confined to a ball.

These are the local replacements for the global derivative bounds of the bounded-derivative
Itô–Lévy formula: where that theorem asks `|∂ₜu| ≤ K₀`, `|∇u| ≤ K₁` and `|∇²u| ≤ K₂` everywhere,
a path stopped on leaving a ball only meets the state function on a compact box, where the same
bounds hold for free.

## Main statements

* `exists_bound_on_box` — on `[a, b] × closedBall 0 R` the time derivative, every gradient entry
  and every Hessian entry of a `C²` function are bounded by one constant.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Ito.JumpFormula

universe u

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}



theorem _root_.solution (hu : ContDiff ℝ 2 (Function.uncurry u)) (a b R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ s x, s ∈ Set.Icc a b → ‖x‖ ≤ R → |timeDeriv u s x| ≤ K) ∧
      (∀ s x, s ∈ Set.Icc a b → ‖x‖ ≤ R → ∀ i, |gradient u s x i| ≤ K) ∧
      (∀ s x, s ∈ Set.Icc a b → ‖x‖ ≤ R → ∀ i j, |hessian u s x i j| ≤ K) := by
  let B : Set (ℝ × (Fin n → ℝ)) := Set.Icc a b ×ˢ Metric.closedBall 0 R
  have hB : IsCompact B := isCompact_Icc.prod (isCompact_closedBall _ _)
  have bound {f : ℝ × (Fin n → ℝ) → ℝ} (hf : Continuous f) :
      ∃ K, ∀ x ∈ B, f x ≤ K := by
    obtain ⟨K, hK⟩ := (hB.image hf).bddAbove
    exact ⟨K, fun x hx => hK (Set.mem_image_of_mem f hx)⟩
  have ht : Continuous (fun q : ℝ × (Fin n → ℝ) => timeDeriv u q.1 q.2) := by exact?
  obtain ⟨A,hA⟩ := bound ht.abs
  obtain ⟨G,hG⟩ := bound (continuous_sum_abs_gradient hu)
  obtain ⟨H,hH⟩ := bound (continuous_sum_abs_hessian hu)
  refine ⟨max 0 (max A (max G H)), le_max_left _ _, ?_, ?_, ?_⟩
  · intro s x hs hx
    have hmem : (s,x) ∈ B := ⟨hs, by simpa [Metric.mem_closedBall, dist_zero_right] using hx⟩
    exact (hA (s,x) hmem).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro s x hs hx i
    have hmem : (s,x) ∈ B := ⟨hs, by simpa [Metric.mem_closedBall, dist_zero_right] using hx⟩
    have hi : |gradient u s x i| ≤ ∑ j : Fin n, |gradient u s x j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (gradient u s x j)) (Finset.mem_univ i)
    exact hi.trans ((hG (s,x) hmem).trans (by exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  · intro s x hs hx i j
    have hmem : (s,x) ∈ B := ⟨hs, by simpa [Metric.mem_closedBall, dist_zero_right] using hx⟩
    have h1 : |hessian u s x i j| ≤ ∑ l : Fin n, |hessian u s x i l| :=
      Finset.single_le_sum (fun l _ => abs_nonneg (hessian u s x i l)) (Finset.mem_univ j)
    have h2 : (∑ l : Fin n, |hessian u s x i l|) ≤
        ∑ m : Fin n, ∑ l : Fin n, |hessian u s x m l| :=
      Finset.single_le_sum (fun m _ => Finset.sum_nonneg fun l _ => abs_nonneg (hessian u s x m l))
        (Finset.mem_univ i)
    exact h1.trans (h2.trans ((hH (s,x) hmem).trans (by exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
