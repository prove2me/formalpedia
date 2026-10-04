-- Prove2me | solution 9 for MilnorDynamics.normal_disk_to_thrice_punctured_plane
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T21:15:14.904708+00:00
-- url     : https://prove2.me/submissions/9c6b7551-d29a-4e1b-a0dc-8cd5cbe181be
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

/-- **Variant 13: repair of CE 6453 E01 by naming both hypotheses up front
instead of projecting inline.**

Same single-group repair as variant 12. CE 6453 declared 1 group, 1
diagnostic, 0 cascades; the `END OF CE REPORT` marker matched the header, and
the report was read whole. Its evidence:

```
line 70: Type mismatch
  Supplied term: Compile error in your proof: (hff (φ n)).left
  Actual type:   DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1)
  Expected type: DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1) ∧
                 MapsTo (f (φ n)) (Metric.ball 0 1) {0, 1}ᶜ
```

`locally_bounded_holomorphic_subseq_locally_uniform` (`9827712e`, **Proved**)
wants only the `DifferentiableOn` half; `either_limit_avoids_or_diverges`
(`da5d88b1`, **Proved**) and `not_locally_bounded_diverges` want the full
conjunction including `MapsTo`. Variant 11 projected all three sites "for
symmetry", which is the fault this report names.

This variant differs from variant 12 in the cause-linked part: rather than
projecting inline at each use site, it derives two named hypotheses once, right
after the `have hff`,

```
have hffD : ∀ n, DifferentiableOn ℂ (f n) (Metric.ball 0 1) := fun n => (hff n).1
have hffM : ∀ n, DifferentiableOn ℂ (f n) (Metric.ball 0 1) ∧
    MapsTo (f n) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) := hff
```

and passes `hffD` to the one lemma that wants the projection and `hffM` to the
two that want the conjunction. The asymmetry is then structural rather than a
fact to be remembered at each call site.

Full CE 6453 accounting: 1 declared group, 1 diagnostic, 0 cascades; the single
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
        (Metric.isOpen_ball) f hffD hbdd
    refine ⟨φ, hφ, ?_⟩
    --
    -- REPAIR of E01 (CE 6468 L93, `APPLICATION TYPE MISMATCH`).  The reported
    -- pair was
    --   Supplied term: hffM
    --   Actual type:   ∀ (n : ℕ), DifferentiableOn ℂ (f n) … ∧ MapsTo (f n) …
    --   Expected type: ∀ (n : ℕ), DifferentiableOn ℂ (f (φ n)) … ∧ MapsTo (f (φ n)) …
    --   Applied as:
    --     either_limit_avoids_or_diverges … (fun n => f (φ n)) hffM
    --
    -- `either_limit_avoids_or_diverges` is applied to the *reindexed* family
    -- `fun n => f (φ n)`, so it needs the conjunction restated for that family.
    -- `hffM` states it for `f n`.  Earlier variants kept passing `hffM`
    -- unchanged, which is exactly the mismatch reported here.
    --
    -- Repair: transport the conjunction through `φ` once and pass the
    -- transported form.  No `simpa` is needed — `hffM (φ n)` produces the
    -- expected type definitionally, because the statement is already about
    -- `f (φ n)` once `n` is instantiated with `φ n`.
    have hffMφ : ∀ n, DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1) ∧
        MapsTo (f (φ n)) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) :=
      fun n => hffM (φ n)
    rcases MilnorDynamics.either_limit_avoids_or_diverges (Metric.ball 0 1)
      (Metric.isOpen_ball)
      (Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1)) (fun n => f (φ n))
      hffMφ g hg hcv with hm | hd
    · exact Or.inl ⟨g, hg, hm, hcv⟩
    · exact Or.inr hd
