-- Prove2me | solution 1 for HunterPDE.Shared.multiDeriv_bound_of_contDiffOn_closed
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T16:38:17.486277+00:00
-- url     : https://prove2.me/submissions/1b579b45-9976-4405-a021-17b5bb5889f2

import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open HunterPDE.Shared
open scoped ContDiff Topology
set_option autoImplicit false

theorem solution {n : ℕ} {S Ω K : Set (EuclideanSpace ℝ (Fin n))}
    (hS : IsClosed S) (hSd : UniqueDiffOn ℝ S) (hΩ : IsOpen Ω) (hΩS : Ω ⊆ S)
    (hK : IsCompact K) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiffOn ℝ ∞ f S) (hz : ∀ x ∈ Ω, x ∉ K → f x = 0)
    (α : Fin n → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ω, ‖multiDeriv f α x‖ ≤ K.indicator (fun _ => C) x := by
  have hext (l : List (Fin n)) : ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ g S ∧ Set.EqOn g (iteratedPartial f l) Ω := by
    induction l with
    | nil => exact ⟨f, hf, fun _ _ => rfl⟩
    | cons i l ih =>
      obtain ⟨g, hg, he⟩ := ih
      refine ⟨fun x => fderivWithin ℝ g S x (EuclideanSpace.single i 1),
        (hg.fderivWithin hSd (by simp)).clm_apply contDiffOn_const, ?_⟩
      intro x hx
      have hn : S ∈ 𝓝 x := Filter.mem_of_superset (hΩ.mem_nhds hx) hΩS
      change fderivWithin ℝ g S x (EuclideanSpace.single i 1) =
        fderiv ℝ (iteratedPartial f l) x (EuclideanSpace.single i 1)
      rw [fderivWithin_of_mem_nhds hn]
      exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.single i 1))
        (Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hΩ.mem_nhds hx) he))
  have hzero (l : List (Fin n)) : ∀ x ∈ Ω \ K, iteratedPartial f l x = 0 := by
    induction l with
    | nil => exact fun x hx => hz x hx.1 hx.2
    | cons i l ih =>
      intro x hx
      have hn : Ω \ K ∈ 𝓝 x := (hΩ.inter hK.isClosed.isOpen_compl).mem_nhds hx
      have he : iteratedPartial f l =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
        Filter.eventuallyEq_of_mem hn ih
      change fderiv ℝ (iteratedPartial f l) x (EuclideanSpace.single i 1) = 0
      rw [he.fderiv_eq]
      simp
  obtain ⟨g, hg, he⟩ := hext (multiIndexList α)
  obtain ⟨C, hC⟩ := (hK.inter_right hS).exists_bound_of_continuousOn
    (hg.continuousOn.mono Set.inter_subset_right)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  by_cases hxK : x ∈ K
  · rw [Set.indicator_of_mem hxK]
    change ‖iteratedPartial f (multiIndexList α) x‖ ≤ _
    rw [← he hx]
    exact (hC x ⟨hxK, hΩS hx⟩).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hxK]
    change ‖iteratedPartial f (multiIndexList α) x‖ ≤ 0
    rw [hzero _ x ⟨hx, hxK⟩, norm_zero]
