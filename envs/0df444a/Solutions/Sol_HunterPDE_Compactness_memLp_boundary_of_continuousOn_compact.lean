-- Prove2me | solution 1 for HunterPDE.Compactness.memLp_boundary_of_continuousOn_compact
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T09:48:58.50192+00:00
-- url     : https://prove2.me/submissions/52ef6fba-a982-44fe-ba56-f1b6ec372b12

import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory HunterPDE.Compactness
open scoped ENNReal
set_option autoImplicit false

theorem solution {m : ℕ} (p : ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : ContinuousOn f (closedUpperHalfSpace m))
    (hK : ∃ K : Set (EuclideanSpace ℝ (Fin (m + 1))), IsCompact K ∧
      ∀ x ∈ closedUpperHalfSpace m, x ∉ K → f x = 0) :
    MemLp (fun x' => f (boundaryPoint x')) p volume := by
  have hb : Continuous (@boundaryPoint m) := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (continuous_const :
        Continuous (fun _ : EuclideanSpace ℝ (Fin m) => (0 : ℝ)))
    · simpa only [Fin.snoc_castSucc] using
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin m => ℝ) j)
  have hbmem (x : EuclideanSpace ℝ (Fin m)) :
      boundaryPoint x ∈ closedUpperHalfSpace m := by
    simp [closedUpperHalfSpace, boundaryPoint]
  have hc : Continuous (fun x' => f (boundaryPoint x')) :=
    hf.comp_continuous hb hbmem
  let π : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin m) :=
    fun x => WithLp.toLp 2 (fun i => x i.castSucc)
  have hπ : Continuous π := by
    exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => (EuclideanSpace.proj i.castSucc).continuous)
  have hleft (x : EuclideanSpace ℝ (Fin m)) : π (boundaryPoint x) = x := by
    ext i
    simp [π, boundaryPoint]
  obtain ⟨K, hKc, hKf⟩ := hK
  have hsupport : Function.support (fun x' => f (boundaryPoint x')) ⊆ π '' K := by
    intro x hx
    refine ⟨boundaryPoint x, ?_, hleft x⟩
    by_contra h
    exact hx (hKf _ (hbmem x) h)
  have hcompact : HasCompactSupport (fun x' => f (boundaryPoint x')) :=
    (hKc.image hπ).of_isClosed_subset isClosed_closure
      (closure_minimal hsupport (hKc.image hπ).isClosed)
  exact hc.memLp_of_hasCompactSupport hcompact
