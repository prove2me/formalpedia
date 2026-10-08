-- Prove2me | solution 11 for MilnorDynamics.normal_disk_to_thrice_punctured_plane
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T15:42:32.33499+00:00
-- url     : https://prove2.me/submissions/01446c0f-42c7-4779-a7a7-a0d5726371f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_locally_bounded_holomorphic_subseq_locally_uniform
import Theorems.Thm_MilnorDynamics_either_limit_avoids_or_diverges
import Theorems.Thm_MilnorDynamics_not_locally_bounded_subseq_diverges

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- **Variant 14: repair of CE 6468 E01 by reindexing the conjunction at the
`either_limit_avoids_or_diverges` call site.**

CE 6468 declared 1 group, 1 diagnostic, 0 cascades; the `END OF CE REPORT`
marker agreed with the header and the report was read whole. Its evidence:

```
line 93: Application type mismatch: The argument
  hffM
has type
  ∀ (n : ℕ), DifferentiableOn ℂ (f n) (Metric.ball 0 1) ∧ MapsTo (f n) (Metric.ball 0 1) {0, 1}ᶜ
but is expected to have type
  ∀ (n : ℕ), DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1) ∧ MapsTo (f (φ n)) (Metric.ball 0 1) {0, 1}ᶜ
```

Variant 13 named `hffD`/`hffM` up front so that each lemma got the shape it
asks for, but it then passed the *unreindexed* `hffM` to a call whose first
argument is the reindexed sequence `fun n => f (φ n)`. A named hypothesis is
only correct for the site that keeps the original index; the reindexed site
must re-derive the conjunction at `φ n`.

So this variant keeps both named hypotheses (the structural asymmetry that
fixed the earlier projection defects) and adds the one thing that was missing:
a named reindexed conjunction

```
have hffMφ : ∀ n, DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1) ∧
    MapsTo (f (φ n)) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) := fun n => hff (φ n)
```

used at the reindexed call site, leaving `hffM` for `not_locally_bounded_subseq_diverges`,
which receives `f` itself and therefore wants the un-reindexed statement.

Full CE 6468 accounting: 1 declared group, 1 diagnostic, 0 cascades; the single
independent group is repaired here, and no other group existed in the report. -/
theorem solution (𝓕 : Set (ℂ → ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      MapsTo f (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) :
    IsNormalFamilyInto (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) 𝓕 := by
  intro f hf
  have hff : ∀ n, DifferentiableOn ℂ (f n) (Metric.ball 0 1) ∧
      MapsTo (f n) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) :=
    fun n => h𝓕 (f n) (hf n)
  have hffD : ∀ n, DifferentiableOn ℂ (f n) (Metric.ball 0 1) := fun n => (hff n).1
  have hffM : ∀ n, DifferentiableOn ℂ (f n) (Metric.ball 0 1) ∧
      MapsTo (f n) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) := hff
  by_cases hesc : ∃ K ⊆ Metric.ball 0 1, IsCompact K ∧
      ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
  · obtain ⟨φ, hφmono, hdiv⟩ :=
      MilnorDynamics.not_locally_bounded_subseq_diverges (Metric.ball 0 1)
        (Metric.isOpen_ball)
        (Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1))
        f hffM hesc
    exact ⟨φ, hφmono, Or.inr hdiv⟩
  · have hbdd : ∀ K ⊆ Metric.ball 0 1, IsCompact K →
        ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M := by
      intro K hKU hK
      by_contra hcon
      exact hesc ⟨K, hKU, hK, hcon⟩
    obtain ⟨φ, hφ, g, hg, hcv⟩ :=
      MilnorDynamics.locally_bounded_holomorphic_subseq_locally_uniform (Metric.ball 0 1)
        (Metric.isOpen_ball) f hffD hbdd
    have hffMφ : ∀ n, DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1) ∧
        MapsTo (f (φ n)) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) := fun n => hff (φ n)
    refine ⟨φ, hφ, ?_⟩
    rcases MilnorDynamics.either_limit_avoids_or_diverges (Metric.ball 0 1)
      (Metric.isOpen_ball)
      (Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1)) (fun n => f (φ n))
      hffMφ g hg hcv with hm | hd
    · exact Or.inl ⟨g, hg, hm, hcv⟩
    · exact Or.inr hd
