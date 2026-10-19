-- Prove2me | solution 1 for HunterPDE.Compactness.halfSpace_trace
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T20:33:38.623366+00:00
-- url     : https://prove2.me/submissions/5e80d144-51c4-4fbc-93c2-a22d7340fe9d

import Theorems.Thm_HunterPDE_Compactness_exists_bounded_halfSpace_trace
import Theorems.Thm_HunterPDE_Compactness_memW0_of_bounded_trace_eq_zero
import Theorems.Thm_HunterPDE_Compactness_boundedMap_vanishes_on_memW0
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℕ, ∃ T : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin m) → ℝ,
      (∀ f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        MemW 1 p (upperHalfSpace m) f → MemW 1 p (upperHalfSpace m) g → ∀ a b : ℝ,
          T (a • f + b • g) =ᵐ[volume] a • T f + b • T g) ∧
      (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        MemLp (T f) p volume ∧
          eLpNorm (T f) p volume ≤ (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f) ∧
      (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, IsSmoothCompactClosedHalfSpace f →
        T f =ᵐ[volume] fun x' => f (boundaryPoint x')) ∧
      (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        (MemW0 1 p (upperHalfSpace m) f ↔ T f =ᵐ[volume] 0)) := by
  obtain ⟨C, hC⟩ := exists_bounded_halfSpace_trace p hp hp'
  refine ⟨C, fun m => ?_⟩
  obtain ⟨T, hlinear, hbound, hsmooth⟩ := hC m
  refine ⟨T, hlinear, hbound, hsmooth, fun f hf => ⟨?_, ?_⟩⟩
  · intro hf0
    apply boundedMap_vanishes_on_memW0 hp (upperHalfSpace m) T C
      (fun u v hu hv => ?_) hbound (fun φ hφ => ?_) f hf0
    · simpa only [one_smul, neg_one_smul, sub_eq_add_neg] using
        hlinear u v hu hv 1 (-1)
    · have hclosed : IsSmoothCompactClosedHalfSpace φ :=
        ⟨hφ.1.contDiffOn, tsupport φ, hφ.2.1, fun x _ hx =>
          image_eq_zero_of_notMem_tsupport hx⟩
      apply (hsmooth φ hclosed).trans
      apply Filter.Eventually.of_forall
      intro x'
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      have hpos := hφ.2.2 hx
      simpa [upperHalfSpace, boundaryPoint] using hpos
  · exact memW0_of_bounded_trace_eq_zero hp hp' C T hlinear hbound hsmooth f hf
