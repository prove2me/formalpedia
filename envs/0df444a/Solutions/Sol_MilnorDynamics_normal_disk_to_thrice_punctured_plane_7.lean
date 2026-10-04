-- Prove2me | solution 7 for MilnorDynamics.normal_disk_to_thrice_punctured_plane
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T20:31:34.690985+00:00
-- url     : https://prove2.me/submissions/3e92641c-1b97-4c8a-9653-af17cfbc6731
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

/-- **Variant 12: repair of CE 6453 E01 -- restore the conjunction at the
`either_limit_avoids_or_diverges` call site.**

CE 6453 declared exactly 1 error group, 1 diagnostic, 0 cascades, and the
`END OF CE REPORT` marker matched the header counts (candidate 6453,
submission ff749fd4, groups=1, diagnostics=1), so the report was read whole.
Its evidence, verbatim:

```
line 70: Type mismatch
  Supplied term: Compile error in your proof: (hff (φ n)).left
  Actual type:   DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1)
  Expected type: DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1) ∧
                 MapsTo (f (φ n)) (Metric.ball 0 1) {0, 1}ᶜ
```

Read against the goal state, this says two different things at two sites, and
variant 11 obeyed the wrong one of the pair:

* **Line 62 was genuinely broken.** `locally_bounded_holomorphic_subseq_locally_uniform`
  (`9827712e`, **Proved**) declares `hf : ∀ n, DifferentiableOn ℂ (f n) U`, and
  the conjunction `hff n` was handed over whole. Projecting to `(hff n).1` is
  the right repair and is kept here.
* **Line 67 was never broken.** `either_limit_avoids_or_diverges` (`da5d88b1`,
  **Proved**) declares `hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U V`
  -- it wants the *conjunction*, `MapsTo` half included.  Variant 11 projected
  it anyway, "for symmetry", and that is precisely the fault this report
  names: the supplied term had the `DifferentiableOn` half alone where the
  conjunction was expected.

So the actual/expected pair is the evidence, and it points in *opposite*
directions at the two sites.  Applying one rule uniformly is what produced this
compile error.  Repair: keep `(hff n).1` at the line-62 site and pass the
untouched conjunction `fun n => hff (φ n)` at the line-67 site.

Full CE 6453 accounting: 1 declared group, 1 diagnostic, 0 cascades; the single
independent group is repaired here, and no other group existed in the report.
The two facts differ only in this one argument, so the rest of the proof is
untouched. -/
theorem solution (𝓕 : Set (ℂ → ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      MapsTo f (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) :
    IsNormalFamilyInto (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) 𝓕 := by
  intro f hf
  have hff : ∀ n, DifferentiableOn ℂ (f n) (Metric.ball 0 1) ∧
      MapsTo (f n) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) :=
    fun n => h𝓕 (f n) (hf n)
  by_cases hesc : ∃ K ⊆ Metric.ball 0 1, IsCompact K ∧
      ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
  · obtain ⟨φ, hφmono, hdiv⟩ :=
      MilnorDynamics.not_locally_bounded_subseq_diverges (Metric.ball 0 1)
        (Metric.isOpen_ball)
        (Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1))
        f (fun n => hff n) hesc
    exact ⟨φ, hφmono, Or.inr hdiv⟩
  · have hbdd : ∀ K ⊆ Metric.ball 0 1, IsCompact K →
        ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M := by
      intro K hKU hK
      by_contra hcon
      exact hesc ⟨K, hKU, hK, hcon⟩
    obtain ⟨φ, hφ, g, hg, hcv⟩ :=
      MilnorDynamics.locally_bounded_holomorphic_subseq_locally_uniform (Metric.ball 0 1)
        -- CE 6447 E01: `locally_bounded_holomorphic_subseq_locally_uniform`
        -- takes `hf : ∀ n, DifferentiableOn ℂ (f n) U` alone, while `hff n` is
        -- the conjunction `DifferentiableOn ℂ (f n) (Metric.ball 0 1) ∧
        -- MapsTo (f n) (Metric.ball 0 1) {0, 1}ᶜ`.  The report gives both types
        -- verbatim, so the supplied term had to be projected.
        --
        -- The parenthesisation matters: `(hff n).1` projects from the *result* of
        -- applying `hff`, whereas `hff n.1` projects the argument `n`.  The other
        -- two call sites are deliberately left as conjunctions, because their
        -- targets genuinely ask for the pair:
        --   * `not_locally_bounded_diverges` (CE: `hf : ∀ n, DifferentiableOn … ∧
        --     MapsTo …`) — line 53 stays `(fun n => hff n)`;
        --   * `either_limit_avoids_or_diverges` (same conjunction shape) — the
        --     later `rcases` site stays `(fun n => hff (φ n))`.
        (Metric.isOpen_ball) f (fun n => (hff n).1) hbdd
    refine ⟨φ, hφ, ?_⟩
    rcases MilnorDynamics.either_limit_avoids_or_diverges (Metric.ball 0 1)
      (Metric.isOpen_ball)
      (Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1)) (fun n => f (φ n))
      (fun n => hff (φ n)) g hg hcv with hm | hd
    · exact Or.inl ⟨g, hg, hm, hcv⟩
    · exact Or.inr hd
