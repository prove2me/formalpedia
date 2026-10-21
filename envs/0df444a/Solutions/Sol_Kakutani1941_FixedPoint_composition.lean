-- Prove2me | solution 1 for Kakutani1941.FixedPoint.composition
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:58:12.108983+00:00
-- url     : https://prove2.me/submissions/727f0a53-5acd-459a-bedc-7fb4b8586503

import Mathlib
import Definitions.Def_Kakutani1941_FixedPoint_ClosedConvexSubset
import Definitions.Def_Kakutani1941_FixedPoint_UpperSemicontinuous
set_option autoImplicit false
open Kakutani1941.FixedPoint

theorem solution {m : ℕ} {S T : Set (EuclideanSpace ℝ (Fin m))}
    (hST : S ⊆ T)
    (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hψcont : ContinuousOn ψ T) (hψmap : Set.MapsTo ψ T S)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦ : ∀ x ∈ S, IsClosedConvexSubset S (Φ x))
    (hΦne : ∀ x ∈ S, (Φ x).Nonempty)
    (husc : IsUpperSemicontinuous S Φ) :
    IsUpperSemicontinuous T (fun x => Φ (ψ x)) ∧
      (∀ x ∈ T, IsClosedConvexSubset S (Φ (ψ x))) ∧
      (∀ x ∈ T, IsClosedConvexSubset T (Φ (ψ x))) ∧
      (∀ x ∈ T, (Φ (ψ x)).Nonempty) := by
  refine ⟨?_, fun x hx => hΦ _ (hψmap hx), fun x hx => ?_, fun x hx => hΦne _ (hψmap hx)⟩
  · intro x y x0 y0 hx hx0 hxl hy hyl
    have h1 : Filter.Tendsto (fun n => ψ (x n)) Filter.atTop (nhds (ψ x0)) := by
      have := (hψcont x0 hx0).tendsto
      exact this.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hxl
        (Filter.Eventually.of_forall hx))
    exact husc (fun n => ψ (x n)) y (ψ x0) y0 (fun n => hψmap (hx n)) (hψmap hx0) h1 hy hyl
  · obtain ⟨h1, h2, h3⟩ := hΦ _ (hψmap hx)
    exact ⟨h1.trans hST, h2, h3⟩
