-- Prove2me | solution 1 for LusinNovikov.exists_measurable_uniformization_of_countable_sections
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T10:59:57.44031+00:00
-- url     : https://prove2.me/submissions/002d0283-2b9e-491f-9110-b19c3acac0e5

import Theorems.Thm_LusinNovikov_exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections
import Mathlib


section
section
section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
/-!
# Route to Lusin–Novikov and Feldman–Moore (lemma list, all `sorry`)

Each lemma's docstring gives the proof idea, the Mathlib API (every name checked with `#check`
against Mathlib `0df444a3`), and a size estimate in lines of Lean. See `PLAN.md` for the
narrative.

* §A: **Shinko's Lusin–Novikov theorem**, metric form (F. Shinko, *Lusin–Novikov via σ-ideals*,
  2024; local copy `sources/shinko-lusin-novikov-via-sigma-ideals.pdf`). A continuous map from a
  complete separable metric space with countable fibres is covered by countably many Borel
  partial sections. The proof uses no analytic sets, only closed sets, Borel sets, and Cantor's
  intersection theorem.
* §B: glue to standard Borel spaces, giving (LN-1)…(LN-5) of `Statements.lean`.
* §C: Feldman–Moore, giving (FM) and (FM-group) of `Statements.lean`.
* §D: the CFW-facing consequences: the counting measure `m`, CFW Lemma 3(a), CFW Lemma 3(b), and
  the left-to-right mean swap. These are downstream, not part of LN/FM.
-/
/-! ## §A. Shinko's theorem (metric form) -/

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
/-!
# §A of the Lusin–Novikov route: Shinko's theorem (metric form), proved

Proofs of every theorem in §A (`section Shinko`) of `Solutions.LN.Blueprint`, restated verbatim
in the namespace `CFWPlan.Route.PartA`. The definitions `IsBorelSection`, `InI` and `IsNullFam`
are the Blueprint's (`CFWPlan.Route.*`). The argument follows F. Shinko, *Lusin–Novikov via
σ-ideals* (2024).

Note on names: inside this namespace an unqualified `InI.mono` resolves to
`CFWPlan.Route.PartA.InI.mono` (innermost namespace first), but dot notation `h.mono` on
`h : InI f A` would resolve to the Blueprint's unproved stub `CFWPlan.Route.InI.mono`, so the proofs
below never use dot notation on `InI` / `IsNullFam` hypotheses.
-/
/-! ### A1. The σ-ideal `I` -/

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-! ### A2–A5. Null families -/

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
/-! ### A6–A7. Shinko's two observations -/

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
/-! ### A8. One level of the Cantor scheme -/

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
/-! ### A9–A11. The Cantor scheme and the theorem -/

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartB
/-!
# §B of the Lusin–Novikov route: glue to standard Borel spaces

Proofs of the four §B targets of `Solutions/LN/Blueprint.lean` (section `Glue`), from the metric
form `CFWPlan.Route.inI_univ_of_countable_fibers` (§A11), following the template of Mathlib's
proof of `MeasurableSet.image_of_measurable_injOn`.
-/

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartB
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
/-! ## §B. Glue to standard Borel spaces -/

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartB
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartB
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartB
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §C. Feldman–Moore -/

end CFWPlan.Route
end

section
open MeasureTheory Set Function
namespace CFWPlan.Route.PartC
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-!
# §C. Feldman–Moore (proofs of the Blueprint §C lemmas) and the CFW milestone

The §C lemmas of `Solutions.LN.Blueprint`, restated verbatim in `CFWPlan.Route.PartC` and proved
from the §B stub `CFWPlan.Route.lusinNovikov` (Lusin–Novikov) and Mathlib's Lusin–Souslin
theorem. The CFW milestone `exists_seq_measurableEquiv_of_countable_classes` (Feldman–Moore,
involution form) is then proved as `ConnesFeldmanWeiss.chk_exists_seq_measurableEquiv_of_countable_classes`.
-/

end CFWPlan.Route.PartC
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route
end

section
open MeasureTheory Set Function
namespace CFWPlan.Route.PartC
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route.PartC
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route
end

section
open MeasureTheory Set Function
namespace CFWPlan.Route.PartC
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route.PartC
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route
end

section
open MeasureTheory Set Function
namespace CFWPlan.Route.PartC
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route.PartC
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartD
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-!
# §D of the Lusin–Novikov route: the CFW-facing consequences

Proofs of the five §D targets of `Solutions/LN/Blueprint.lean` (section `Downstream`), from the
§B/§C statements of the Blueprint (`lusinNovikov`, `measurableSet_image_fst`,
`exists_biInjOn_cover`, `exists_partialTransformation_of_biInjOn`) and Mathlib's
Lusin–Souslin theorem `MeasurableSet.image_of_measurable_injOn`.

* D1 `exists_leftCountingMeasure`: `m = ∑ₙ (μ.comap (fst ∘ val)).map val` over the B2 pieces.
* D2 `relNull_iff`: B3 makes `fst '' (S ∩ R)` Borel.
* D3 `cfw_lemma3a`: C1 pieces, an everywhere positive finite Radon–Nikodym density of
  `A ↦ μ (snd '' (G ∩ fst⁻¹' A))` on each piece, the level sets of the density, C2.
* D4 `cfw_lemma3b`: C1 pieces `Gₙ`; the point `(x, y) ∈ Gₙ` gets the pair of ranks
  `(#{m < n | x ∈ fst '' Gₘ}, #{m < n | y ∈ snd '' Gₘ}) ∈ Fin N × Fin N`; each rank class is
  bi-injective, then C2.
* D5 `relNull_swap`: direct from symmetry and `hqi`.
-/
/-! ### Graphs of partial transformations -/

/-! ### D1 -/

end CFWPlan.Route.PartD
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §D. CFW-facing consequences (downstream of FM; statements only)

These are where FM's output is consumed. They are listed so that the FM form is checked against
its users. They are **not** part of the LN/FM work. -/

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartD
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ### D2 -/

end CFWPlan.Route.PartD
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartD
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ### D3 -/

end CFWPlan.Route.PartD
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartD
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ### D4 -/

end CFWPlan.Route.PartD
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartD
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ### D5 -/

end CFWPlan.Route.PartD
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route
end

section
open MeasureTheory Set Function
namespace ConnesFeldmanWeiss

end ConnesFeldmanWeiss
end

end
end

section
section
/-!
# Lusin–Novikov, standalone forms

Each theorem is proved from its published sibling, so that a solution imports the sibling rather
than inlining it: the injective cover (Shinko's theorem, from `Solutions/LN`) is the root; the
graph form and Borel images use it; the projection and the uniformization use the graph form.
-/

open MeasureTheory Set Function

namespace LusinNovikov

variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]

theorem exists_measurable_uniformization_of_countable_sections [Nonempty Y]
    {P : Set (X × Y)} (hP : MeasurableSet P) (hcount : ∀ x, {y | (x, y) ∈ P}.Countable) :
    ∃ g : X → Y, Measurable g ∧ ∀ x ∈ Prod.fst '' P, (x, g x) ∈ P := by
  classical
  obtain ⟨G, hGm, hGi, -, hGu⟩ := exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections hP hcount
  -- the graph pieces as Borel functions `gs n` on the Borel domains `D n = fst '' G n`
  have he : ∀ n, MeasurableEmbedding (fun p : G n => p.1.1) := fun n => by
    have := (hGm n).standardBorel
    exact (measurable_fst.comp measurable_subtype_coe).measurableEmbedding
      (fun p q hpq => Subtype.ext (hGi n p.2 q.2 hpq))
  have hGP : ∀ n, G n ⊆ P := fun n => hGu ▸ subset_iUnion G n
  let D : ℕ → Set X := fun n => range (fun p : G n => p.1.1)
  let gs : ℕ → X → Y := fun n =>
    extend (fun p : G n => p.1.1) (fun p => p.1.2) (fun _ => Classical.arbitrary Y)
  have hD : ∀ n, MeasurableSet (D n) := fun n => (he n).measurableSet_range
  have hg : ∀ n, Measurable (gs n) := fun n =>
    (he n).measurable_extend (measurable_snd.comp measurable_subtype_coe) measurable_const
  have hDP : ∀ n, ∀ x ∈ D n, (x, gs n x) ∈ P := by
    rintro n _ ⟨p, rfl⟩
    show ((p : X × Y).1, gs n (p : X × Y).1) ∈ P
    simp only [gs]
    rw [(he n).injective.extend_apply (fun p : G n => p.1.2)]
    exact hGP n p.2
  have hcov : ∀ p ∈ P, ∃ n, p.1 ∈ D n := by
    intro p hp
    rw [← hGu, mem_iUnion] at hp
    obtain ⟨n, hn⟩ := hp
    exact ⟨n, ⟨p, hn⟩, rfl⟩
  -- the least piece containing `x`, and a default value off the projection
  let y0 : Y := Classical.arbitrary Y
  let f : ℕ → X → Y := fun n => if n = 0 then fun _ => y0 else gs (n - 1)
  let p : ℕ → X → Prop := fun n x => if n = 0 then x ∉ ⋃ k, D k else x ∈ D (n - 1)
  have hex : ∀ x, ∃ n, p n x := by
    intro x
    by_cases hx : x ∈ ⋃ k, D k
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hx
      exact ⟨k + 1, by simpa [p] using hk⟩
    · exact ⟨0, by simpa [p] using hx⟩
  have hf : ∀ n, Measurable (f n) := by
    intro n
    by_cases hn : n = 0
    · simp only [f, hn, if_true]; exact measurable_const
    · simp only [f, hn, if_false]; exact hg _
  have hp : ∀ n, MeasurableSet {x | p n x} := by
    intro n
    by_cases hn : n = 0
    · simp only [p, hn, if_true]; exact (MeasurableSet.iUnion hD).compl
    · simp only [p, hn, if_false]; exact hD _
  have : ∀ n, DecidablePred (p n) := fun _ _ => Classical.propDecidable _
  have : ∀ x, DecidablePred fun n => p n x := fun _ _ => Classical.propDecidable _
  refine ⟨fun x => f (Nat.find (hex x)) x, Measurable.find hf hp hex, ?_⟩
  rintro x ⟨⟨x', y⟩, hxy, rfl⟩
  obtain ⟨k, hk⟩ := hcov ⟨x', y⟩ hxy
  have hspec := Nat.find_spec (hex x')
  have hmem : x' ∈ ⋃ k, D k := mem_iUnion.2 ⟨k, hk⟩
  by_cases hn : Nat.find (hex x') = 0
  · simp only [p, hn, if_true] at hspec; exact absurd hmem hspec
  · simp only [p, hn, if_false] at hspec
    simp only [f, hn, if_false]
    exact hDP _ x' hspec

end LusinNovikov

end
end

section
open LusinNovikov

theorem solution {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    {P : Set (X × Y)} (hP : MeasurableSet P) (hcount : ∀ x, {y | (x, y) ∈ P}.Countable) :
    ∃ g : X → Y, Measurable g ∧ ∀ x ∈ Prod.fst '' P, (x, g x) ∈ P := by
  apply LusinNovikov.exists_measurable_uniformization_of_countable_sections <;> assumption

end
