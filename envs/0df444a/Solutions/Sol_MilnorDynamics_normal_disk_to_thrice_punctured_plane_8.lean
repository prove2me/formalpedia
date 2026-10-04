-- Prove2me | solution 8 for MilnorDynamics.normal_disk_to_thrice_punctured_plane
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T21:12:40.574621+00:00
-- url     : https://prove2.me/submissions/51582c4d-c5da-4c38-9169-e54a03b0a243
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

/-- **Variant 14: repair of CE 6468 E01 by re-indexing the hypothesis through `φ`.**

CE 6468 declared 1 error group, 1 diagnostic, 0 cascades; the
`END OF CE REPORT` marker (`candidate=6468 submission=4ad96a43… groups=1
diagnostics=1`) agreed with the header counts, and the whole 71-line report was
read. Its sole group was an application type mismatch at line 93:

```
line 93: Application type mismatch: The argument
  Supplied term: Compile error in your proof: hffM
  Actual type:   ∀ (n : ℕ), DifferentiableOn ℂ (f n) (Metric.ball 0 1) ∧
                 MapsTo (f n) (Metric.ball 0 1) {0, 1}ᶜ
  Expected type: ∀ (n : ℕ), DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1) ∧
                 MapsTo (f (φ n)) (Metric.ball 0 1) {0, 1}ᶜ
  Applied as:
    either_limit_avoids_or_diverges (Metric.ball 0 1) Metric.isOpen_ball
      (Metric.isConnected_ball ?m.360) (fun n => f (φ n)) hffM
```

The evidence names which side is wrong: the supplied term, not the expected type.
`either_limit_avoids_or_diverges` (`da5d88b1`, **Proved**) is stated for a
family `f : ℕ → ℂ → ℂ` with `hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U …`,
and at this call site that family is `fun n => f (φ n)`. The argument that
matches is therefore `fun n => hff (φ n)`, whose type is the expected type
verbatim. Passing the un-reindexed `hff` asserts the same property for `f n`
instead of `f (φ n)`, which is the mismatch.

This is the third appearance of one recurring fault on this target. Variants 11
and 12 tried to fix the *projection* half of the mismatch (which lemma wants the
conjunction and which wants only `DifferentiableOn`) while leaving the *index*
half untouched, so CE 6447, 6453 and 6468 each reported the surviving half.
Variant 14 keeps the named-hypothesis structure of variant 13 and additionally
re-indexes the one term that is applied to a re-indexed family:

```
  have hffφM : ∀ n, DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1) ∧
      MapsTo (f (φ n)) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) := fun n => hff (φ n)
```

and passes `hffφM` at the `rcases` site. `hffD` and `hffM` keep their variant-13
meanings, because `not_locally_bounded_subseq_diverges` and
`locally_bounded_holomorphic_subseq_locally_uniform` are both applied to `f`
itself and so want un-re-indexed hypotheses.

Full CE 6468 accounting: 1 declared group, 1 diagnostic, 0 probable cascades;
the single independent group is repaired here and no other group existed. -/
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
    have hffφM : ∀ n, DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1) ∧
        MapsTo (f (φ n)) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) :=
      fun n => hff (φ n)
    refine ⟨φ, hφ, ?_⟩
    rcases MilnorDynamics.either_limit_avoids_or_diverges (Metric.ball 0 1)
      (Metric.isOpen_ball)
      (Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1)) (fun n => f (φ n))
      hffφM g hg hcv with hm | hd
    · exact Or.inl ⟨g, hg, hm, hcv⟩
    · exact Or.inr hd
