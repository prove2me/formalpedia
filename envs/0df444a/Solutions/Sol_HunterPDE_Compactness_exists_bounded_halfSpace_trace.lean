-- Prove2me | solution 1 for HunterPDE.Compactness.exists_bounded_halfSpace_trace
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T20:51:55.024812+00:00
-- url     : https://prove2.me/submissions/4a03e2fc-6764-4a65-99b6-f40541f8c55b

import Theorems.Thm_HunterPDE_Compactness_smooth_halfSpace_trace_bound
import Theorems.Thm_HunterPDE_Compactness_extend_bounded_smooth_halfSpace_map
import Theorems.Thm_HunterPDE_Compactness_halfSpace_density
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℕ, ∃ T : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin m) → ℝ,
      (∀ f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        MemW 1 p (upperHalfSpace m) f → MemW 1 p (upperHalfSpace m) g → ∀ a b : ℝ,
          T (a • f + b • g) =ᵐ[volume] a • T f + b • T g) ∧ (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        MemLp (T f) p volume ∧
          eLpNorm (T f) p volume ≤ (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f) ∧ (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, IsSmoothCompactClosedHalfSpace f →
        T f =ᵐ[volume] fun x' => f (boundaryPoint x')) := by
  obtain ⟨C, hC⟩ := smooth_halfSpace_trace_bound p hp hp'
  refine ⟨C, fun m => ?_⟩
  let R : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin m) → ℝ :=
    fun f x' => f (boundaryPoint x')
  apply extend_bounded_smooth_halfSpace_map (k := 1) hp hp' C R
  · intro f hf ε hε
    exact halfSpace_density m 1 p hp hp' f hf ε hε
  · intro f g _ _ a b
    exact Filter.Eventually.of_forall (fun _ => rfl)
  · intro f hf
    exact hC m f hf
