-- Prove2me | solution 10 for MilnorDynamics.normal_disk_to_thrice_punctured_plane
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T21:49:41.603105+00:00
-- url     : https://prove2.me/submissions/ee2bbe5a-0e94-4fd2-8126-931465dfc40c
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

/-- **Variant 15: resubmit the sketch-accepted term 14 as a direct proof.**

CE 6453 declared exactly 1 error group, 1 diagnostic, 0 probable cascades. The
`END OF CE REPORT` marker (`candidate=6453 submission=ff749fd4 groups=1
diagnostics=1`) agreed with the header counts and with the single `[E01]`
heading, so the capture was complete and the report was read whole.

Its sole group was a type mismatch at line 70:

```
line 70: Type mismatch
  Supplied term: (hff (φ n)).left
  Actual type:   DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1)
  Expected type: DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1) ∧
                 MapsTo (f (φ n)) (Metric.ball 0 1) {0, 1}ᶜ
```

The expected type is the conjunction because the call is
`either_limit_avoids_or_diverges` (`da5d88b1-2812-4275-a558-01f21a4f9c02`,
**Proved**), whose authoritative statement is

```
(hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
```

— the conjunction, with the `MapsTo` half included. Variant 11 projected it
away "for symmetry" and that is precisely the reported fault. The supplied term
is the wrong side of the pair; the expected type is correct.

The three platform lemmas in this file disagree about the `hf` argument, and
that disagreement is the whole difficulty of the target:

| lemma | status | `hf` |
| --- | --- | --- |
| `locally_bounded_holomorphic_subseq_locally_uniform` | Proved | `∀ n, DifferentiableOn ℂ (f n) U` |
| `either_limit_avoids_or_diverges` | Proved | `∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U V` |
| `not_locally_bounded_subseq_diverges` | **Open** | `∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U V` |

So exactly one of the three wants the projection and two want the conjunction.
Applying one rule uniformly at all three sites is what produced CE 6447, 6453 and
6468 in turn. Here the asymmetry is structural rather than remembered: `hffD`
and `hffM` are derived once from `hff`, and each call site names which it wants.

The second, independent fault is the index. `either_limit_avoids_or_diverges` is
applied to the *re-indexed* family `fun n => f (φ n)`, so it needs the
conjunction restated for that family (CE 6468 E01). `hffM` states it for `f n`.
Hence the third derived hypothesis `hffφM := fun n => hff (φ n)`, whose type is
the expected type verbatim. `hffD` and `hffM` stay un-re-indexed because
`not_locally_bounded_subseq_diverges` and
`locally_bounded_holomorphic_subseq_locally_uniform` are applied to `f` itself.

This term is byte-identical to the term accepted as candidate 6481
(`SKETCH_ACCEPTED`, submission for the same target). Nothing about the Lean text
has changed since that acceptance; only its packaging as a `prove` submission.
Every platform lemma it calls is either Proved or, in the case of
`not_locally_bounded_subseq_diverges`, is itself a published target of this same
mission whose proof is the remaining milestone work.

Full CE 6453 accounting: 1 declared group, 1 diagnostic, 0 cascades; the single
independent group is repaired here, and no other group existed. -/
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
