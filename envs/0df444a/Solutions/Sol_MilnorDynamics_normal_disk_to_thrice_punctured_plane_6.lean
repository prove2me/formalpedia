-- Prove2me | solution 6 for MilnorDynamics.normal_disk_to_thrice_punctured_plane
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T20:26:14.690618+00:00
-- url     : https://prove2.me/submissions/55d70b15-2baf-4f64-8fda-f476a8c82302
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

/-- **Variant 11: repair of CE 6447 E01 -- the missing `.1` projection at
lines 62 and 67.**

CE 6439 had already established that `locally_bounded_holomorphic_subseq_locally_uniform`
(`9827712e`, **Proved**) demands `hf : ∀ n, DifferentiableOn ℂ (f n) U`, and
variant 10 correctly passed `fun n => hff n` -- except that `hff n` here is the
*conjunction* `DifferentiableOn ℂ (f n) (Metric.ball 0 1) ∧ MapsTo (f n) …`,
so the whole conjunction was handed over where a bare `DifferentiableOn` was
required.  CE 6447 reported exactly one independent group confirming precisely
that, at line 62:

```
line 62: Type mismatch
  Supplied term: Compile error in your proof: hff n
  Actual type:   DifferentiableOn ℂ (f n) (Metric.ball 0 1) ∧ MapsTo (f n) …
  Expected type: DifferentiableOn ℂ (f n) (Metric.ball 0 1)
```

The error text shows a raw `Compile error in your proof` placeholder rather
than a pretty-printed term, which is why the site is easy to misread; the
actual/expected pair is unambiguous and names the conjunction on both sides.

Repair: project the first component of the conjunction at **both** call sites,
`fun n => (hff n).1` and `fun n => (hff (φ n)).1`.  The second site is required
because `either_limit_avoids_or_diverges` (`da5d88b1`, **Proved**) declares the
identical hypothesis `hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U V`,
so line 67 happens to be well-typed and is changed only for symmetry.  Both
`MapsTo` halves are unused by these two lemmas, so dropping them loses nothing.

Full CE 6447 accounting: 1 declared group, 1 diagnostic, 0 cascades; the single
group is repaired here.  No other group existed. -/
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
        (Metric.isOpen_ball) f (fun n => (hff n).1) hbdd
    refine ⟨φ, hφ, ?_⟩
    --
    -- CE 6453 E01.  The compiler evidence was
    --
    --   line 70: Type mismatch
    --     Supplied term: (hff (φ n)).left
    --     Actual type:   DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1)
    --     Expected type: DifferentiableOn ℂ (f (φ n)) (Metric.ball 0 1) ∧
    --                     MapsTo (f (φ n)) (Metric.ball 0 1) {0, 1}ᶜ
    --
    -- so the projection is applied one line too late.  Line 65 legitimately
    -- projects, because `locally_bounded_holomorphic_subseq_locally_uniform`
    -- takes only the `DifferentiableOn` component.  But
    -- `either_limit_avoids_or_diverges` takes the *pair*
    -- `DifferentiableOn … ∧ MapsTo …`, so at this site `hff (φ n)` is wanted
    -- whole and the `.1` strips the very `MapsTo` hypothesis that theorem
    -- exists to use.  CE 6447 had introduced this `.1` by mistake: it is the
    -- shape correction that line 65 wanted, applied to the wrong call site.
    --
    -- Repair: pass the conjunction, instantiated at the composed index, with
    -- **no** projection.  Line 65 keeps its `.1`, which that other theorem
    -- does require.  `(fun n => hff (φ n))` keeps the `n ↦ f (φ n)` shape the
    -- preceding argument `(fun n => f (φ n))` demands, so the two arguments
    -- stay index-consistent.
    rcases MilnorDynamics.either_limit_avoids_or_diverges (Metric.ball 0 1)
      (Metric.isOpen_ball)
      (Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1)) (fun n => f (φ n))
      (fun n => hff (φ n)) g hg hcv with hm | hd
    · exact Or.inl ⟨g, hg, hm, hcv⟩
    · exact Or.inr hd
