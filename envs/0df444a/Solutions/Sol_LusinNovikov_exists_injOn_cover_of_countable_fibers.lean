-- Prove2me | solution 1 for LusinNovikov.exists_injOn_cover_of_countable_fibers
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T10:39:55.975542+00:00
-- url     : https://prove2.me/submissions/b7756c7d-c36e-441e-b816-2bf0dc5300bd

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
/-- A Borel partial section of `f`: a Borel set on which `f` is injective. -/
def IsBorelSection (f : X → Y) (A : Set X) : Prop :=
  MeasurableSet A ∧ InjOn f A

/-- Shinko's σ-ideal `I`: sets covered by countably many Borel partial sections. -/
def InI (f : X → Y) (A : Set X) : Prop :=
  ∃ S : ℕ → Set X, (∀ n, IsBorelSection f (S n)) ∧ A ⊆ ⋃ n, S n

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
/-- **A1a.** `I` is hereditary. -/
theorem InI.mono {f : X → Y} {A B : Set X} (hB : InI f B) (hAB : A ⊆ B) : InI f A := by
  obtain ⟨S, hS, hBS⟩ := hB
  exact ⟨S, hS, hAB.trans hBS⟩

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
/-- **A1b.** Borel partial sections are in `I`. -/
theorem inI_of_isBorelSection {f : X → Y} {A : Set X} (hA : IsBorelSection f A) : InI f A :=
  ⟨fun _ => A, fun _ => hA, subset_iUnion (fun _ : ℕ => A) 0⟩

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
/-- The empty set is a Borel partial section. -/
theorem isBorelSection_empty (f : X → Y) : IsBorelSection f ∅ :=
  ⟨MeasurableSet.empty, injOn_empty f⟩

/-- The empty set is in `I`. -/
theorem inI_empty (f : X → Y) : InI f ∅ :=
  inI_of_isBorelSection (isBorelSection_empty f)

/-- **A1c.** `I` is closed under countable unions. -/
theorem InI.iUnion {ι : Type*} [Countable ι] {f : X → Y} {A : ι → Set X}
    (hA : ∀ i, InI f (A i)) : InI f (⋃ i, A i) := by
  choose S hS hAS using hA
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine InI.mono (inI_empty f) ?_
    intro x hx
    obtain ⟨i, _⟩ := mem_iUnion.1 hx
    exact (IsEmpty.false i).elim
  · obtain ⟨e, he⟩ := exists_surjective_nat (ι × ℕ)
    refine ⟨fun m => S (e m).1 (e m).2, fun m => hS _ _, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hAS i hi)
    obtain ⟨m, hm⟩ := he (i, n)
    exact mem_iUnion.2 ⟨m, by rw [hm]; exact hn⟩

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Shinko's "null" finite family: a Borel cover `(B i)` of `Y`, indexed like the family,
with each `G i ∩ f⁻¹(B i)` in `I`. A singleton family `{A}` is null iff `A ∈ I`. -/
def IsNullFam {τ : Type*} (f : X → Y) (G : τ → Set X) : Prop :=
  ∃ B : τ → Set Y, (∀ i, MeasurableSet (B i)) ∧ (∀ y, ∃ i, y ∈ B i) ∧
    ∀ i, InI f (G i ∩ f ⁻¹' B i)

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
/-- `I` is closed under binary unions. -/
theorem InI.union {f : X → Y} {A B : Set X} (hA : InI f A) (hB : InI f B) : InI f (A ∪ B) := by
  rw [union_eq_iUnion]
  exact InI.iUnion fun b => by cases b <;> assumption

/-! ### A2–A5. Null families -/
/-- **A2a.** A family with an empty member is null. -/
theorem isNullFam_of_eq_empty {τ : Type*} {f : X → Y} {G : τ → Set X} {i₀ : τ}
    (h : G i₀ = ∅) : IsNullFam f G := by
  classical
  refine ⟨fun i => if i = i₀ then univ else ∅, fun i => ?_, fun y => ⟨i₀, by simp⟩,
    fun i => ?_⟩
  · dsimp only
    split_ifs
    · exact MeasurableSet.univ
    · exact MeasurableSet.empty
  · by_cases hi : i = i₀
    · subst hi
      rw [h, empty_inter]
      exact inI_empty f
    · simp only [hi, if_false, preimage_empty, inter_empty]
      exact inI_empty f

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
/-- **A2b.** A one-member family is null iff its member is in `I`. -/
theorem isNullFam_unique_iff {τ : Type*} [Unique τ] {f : X → Y} {G : τ → Set X} :
    IsNullFam f G ↔ InI f (G default) := by
  constructor
  · rintro ⟨B, -, hcov, hI⟩
    have hB : B default = univ := eq_univ_of_forall fun y => by
      obtain ⟨i, hi⟩ := hcov y
      rwa [Unique.eq_default i] at hi
    have h := hI default
    rwa [hB, preimage_univ, inter_univ] at h
  · intro h
    refine ⟨fun _ => univ, fun _ => MeasurableSet.univ, fun y => ⟨default, mem_univ y⟩,
      fun i => ?_⟩
    rw [Unique.eq_default i, preimage_univ, inter_univ]
    exact h

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
/-- **A3.** If `G ∘ p` is null for some `p` from a countable type, then `G` is null. -/
theorem IsNullFam.of_comp {σ τ : Type*} [Countable σ] {f : X → Y}
    {G : τ → Set X} (p : σ → τ) (h : IsNullFam f (G ∘ p)) : IsNullFam f G := by
  obtain ⟨B, hBm, hcov, hI⟩ := h
  refine ⟨fun s => ⋃ (t : σ) (_ : p t = s), B t,
    fun s => MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun _ => hBm t,
    fun y => ?_, fun s => ?_⟩
  · obtain ⟨t, ht⟩ := hcov y
    exact ⟨p t, mem_iUnion₂.2 ⟨t, rfl, ht⟩⟩
  · refine InI.mono (InI.iUnion hI) ?_
    rintro x ⟨hx, hx'⟩
    simp only [mem_preimage, mem_iUnion] at hx'
    obtain ⟨t, rfl, ht⟩ := hx'
    exact mem_iUnion.2 ⟨t, hx, ht⟩

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
/-- **A4. Shinko's Lemma 1** (duplicate-member form). -/
theorem IsNullFam.of_split {τ : Type*} [Countable τ] [DecidableEq τ] {f : X → Y}
    (hf : Measurable f) {G : τ → Set X} {j k : τ} (hjk : j ≠ k) (hGjk : G j = G k)
    (hU : MeasurableSet (G j)) {ι : Type*} [Countable ι] {V W : ι → Set X}
    (hV : ∀ n, MeasurableSet (V n)) (hW : ∀ n, MeasurableSet (W n))
    (hcov : ∀ x ∈ G j, ∀ x' ∈ G j, x ≠ x' → ∃ n, x ∈ V n ∧ x' ∈ W n)
    (h : ∀ n, IsNullFam f (update (update G j (V n)) k (W n))) : IsNullFam f G := by
  choose B hBm hBcov hBI using h
  have hj : ∀ n, update (update G j (V n)) k (W n) j = V n := fun n => by
    rw [update_of_ne hjk, update_self]
  have hk : ∀ n, update (update G j (V n)) k (W n) k = W n := fun n => update_self _ _ _
  have ho : ∀ n i, i ≠ j → i ≠ k → update (update G j (V n)) k (W n) i = G i :=
    fun n i hij hik => by rw [update_of_ne hik, update_of_ne hij]
  -- the part of `Y` claimed by the other members
  set O : Set Y := ⋃ (i : τ) (_ : i ≠ j ∧ i ≠ k), ⋃ n, B n i with hO
  have hOm : MeasurableSet O :=
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun n => hBm n i
  -- the removed part of `G j`
  set R : Set X := (⋃ n, V n ∩ f ⁻¹' B n j) ∪ ⋃ n, W n ∩ f ⁻¹' B n k with hR
  have hRm : MeasurableSet R :=
    (MeasurableSet.iUnion fun n => (hV n).inter (hf (hBm n j))).union
      (MeasurableSet.iUnion fun n => (hW n).inter (hf (hBm n k)))
  have hRI : InI f R := by
    refine InI.union (InI.iUnion fun n => ?_) (InI.iUnion fun n => ?_)
    · have := hBI n j
      rwa [hj] at this
    · have := hBI n k
      rwa [hk] at this
  have hZ : IsBorelSection f ((G j ∩ f ⁻¹' Oᶜ) \ R) := by
    refine ⟨(hU.inter (hf hOm.compl)).diff hRm, ?_⟩
    rintro x ⟨⟨hxU, hxO⟩, hxR⟩ x' ⟨⟨hx'U, -⟩, hx'R⟩ hxx'
    by_contra hne
    obtain ⟨n, hxV, hx'W⟩ := hcov x hxU x' hx'U hne
    obtain ⟨i, hi⟩ := hBcov n (f x)
    by_cases hij : i = j
    · subst hij
      exact hxR (Or.inl (mem_iUnion.2 ⟨n, hxV, hi⟩))
    by_cases hik : i = k
    · subst hik
      refine hx'R (Or.inr (mem_iUnion.2 ⟨n, hx'W, ?_⟩))
      show f x' ∈ B n i
      rw [← hxx']
      exact hi
    · exact hxO (mem_iUnion₂.2 ⟨i, ⟨hij, hik⟩, mem_iUnion.2 ⟨n, hi⟩⟩)
  refine ⟨fun i => if i = j then Oᶜ else if i = k then ∅ else ⋃ n, B n i, fun i => ?_,
    fun y => ?_, fun i => ?_⟩
  · dsimp only
    split_ifs
    · exact hOm.compl
    · exact MeasurableSet.empty
    · exact MeasurableSet.iUnion fun n => hBm n i
  · by_cases hy : y ∈ O
    · obtain ⟨i, ⟨hij, hik⟩, hyi⟩ := mem_iUnion₂.1 hy
      exact ⟨i, by simp only [hij, hik, if_false]; exact hyi⟩
    · exact ⟨j, by simp only [if_true]; exact hy⟩
  · by_cases hij : i = j
    · subst hij
      simp only [if_true]
      refine InI.mono (InI.union (inI_of_isBorelSection hZ) hRI) ?_
      intro x hx
      by_cases hxR : x ∈ R
      · exact Or.inr hxR
      · exact Or.inl ⟨hx, hxR⟩
    by_cases hik : i = k
    · subst hik
      simp only [hij, if_false, if_true, preimage_empty, inter_empty]
      exact inI_empty f
    · simp only [hij, hik, if_false]
      refine InI.mono (InI.iUnion fun n => hBI n i) ?_
      rintro x ⟨hx, hx'⟩
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx'
      refine mem_iUnion.2 ⟨n, ?_, hn⟩
      rw [ho n i hij hik]
      exact hx

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
/-- **A5. Shinko's Lemma 2.** Refine by a countable Borel cover `(A m)` of `Y`. -/
theorem IsNullFam.of_cover {τ : Type*} {f : X → Y} {G : τ → Set X} {ι : Type*} [Countable ι]
    {A : ι → Set Y} (hA : ∀ m, MeasurableSet (A m)) (hAcov : ⋃ m, A m = univ)
    (h : ∀ m, IsNullFam f fun i => G i ∩ f ⁻¹' A m) : IsNullFam f G := by
  choose B hBm hBcov hBI using h
  refine ⟨fun i => ⋃ m, A m ∩ B m i,
    fun i => MeasurableSet.iUnion fun m => (hA m).inter (hBm m i), fun y => ?_, fun i => ?_⟩
  · have hy : y ∈ ⋃ m, A m := hAcov.symm ▸ mem_univ y
    obtain ⟨m, hm⟩ := mem_iUnion.1 hy
    obtain ⟨i, hi⟩ := hBcov m y
    exact ⟨i, mem_iUnion.2 ⟨m, hm, hi⟩⟩
  · refine InI.mono (InI.iUnion fun m => hBI m i) ?_
    rintro x ⟨hx, hx'⟩
    obtain ⟨m, hm, hm'⟩ := mem_iUnion.1 hx'
    exact mem_iUnion.2 ⟨m, ⟨hx, hm⟩, hm'⟩

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
/-- **A6. Observation 1.** The off-diagonal of a closed `U` is covered by countably many
products `V n × W n` of disjoint closed subsets of `U` of diameter `≤ ε`. -/
theorem exists_split_cover [SeparableSpace X] {U : Set X} (hU : IsClosed U) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ V W : ℕ → Set X, (∀ n, IsClosed (V n)) ∧ (∀ n, IsClosed (W n)) ∧ (∀ n, V n ⊆ U) ∧
      (∀ n, W n ⊆ U) ∧ (∀ n, Disjoint (V n) (W n)) ∧
      (∀ n, Bornology.IsBounded (V n) ∧ diam (V n) ≤ ε) ∧
      (∀ n, Bornology.IsBounded (W n) ∧ diam (W n) ≤ ε) ∧
      ∀ x ∈ U, ∀ x' ∈ U, x ≠ x' → ∃ n, x ∈ V n ∧ x' ∈ W n := by
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨fun _ => ∅, fun _ => ∅, fun _ => isClosed_empty, fun _ => isClosed_empty,
      fun _ => empty_subset _, fun _ => empty_subset _, fun _ => disjoint_empty _,
      fun _ => ⟨Bornology.isBounded_empty, by simp [hε.le]⟩,
      fun _ => ⟨Bornology.isBounded_empty, by simp [hε.le]⟩, fun x => ?_⟩
    exact (IsEmpty.false x).elim
  obtain ⟨d, hd⟩ := exists_dense_seq X
  -- radii
  set ρ : ℕ → ℝ := fun r => ε / (2 * ((r : ℝ) + 1)) with hρ
  have hρpos : ∀ r, 0 < ρ r := fun r => by positivity
  have hρle : ∀ r, 2 * ρ r ≤ ε := fun r => by
    have h1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith [r.cast_nonneg (α := ℝ)]
    simp only [hρ]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  -- the cover indexed by `ℕ × ℕ × ℕ`
  let V' : ℕ × ℕ × ℕ → Set X := fun i =>
    if 2 * ρ i.2.2 < dist (d i.1) (d i.2.1) then U ∩ closedBall (d i.1) (ρ i.2.2) else ∅
  let W' : ℕ × ℕ × ℕ → Set X := fun i =>
    if 2 * ρ i.2.2 < dist (d i.1) (d i.2.1) then U ∩ closedBall (d i.2.1) (ρ i.2.2) else ∅
  have hsmall : ∀ (c : X) (r : ℕ), Bornology.IsBounded (U ∩ closedBall c (ρ r)) ∧
      diam (U ∩ closedBall c (ρ r)) ≤ ε := fun c r =>
    ⟨isBounded_closedBall.subset inter_subset_right,
      ((diam_mono inter_subset_right isBounded_closedBall).trans
        (diam_closedBall (hρpos r).le)).trans (hρle r)⟩
  have hemp : Bornology.IsBounded (∅ : Set X) ∧ diam (∅ : Set X) ≤ ε :=
    ⟨Bornology.isBounded_empty, by simp [hε.le]⟩
  let e := Denumerable.eqv (ℕ × ℕ × ℕ)
  refine ⟨fun n => V' (e.symm n), fun n => W' (e.symm n), fun n => ?_, fun n => ?_,
    fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · simp only [V']; split_ifs
    · exact hU.inter isClosed_closedBall
    · exact isClosed_empty
  · simp only [W']; split_ifs
    · exact hU.inter isClosed_closedBall
    · exact isClosed_empty
  · simp only [V']; split_ifs
    · exact inter_subset_left
    · exact empty_subset _
  · simp only [W']; split_ifs
    · exact inter_subset_left
    · exact empty_subset _
  · simp only [V', W']; split_ifs with h
    · refine (closedBall_disjoint_closedBall ?_).mono inter_subset_right inter_subset_right
      linarith
    · exact disjoint_empty _
  · simp only [V']; split_ifs
    · exact hsmall _ _
    · exact hemp
  · simp only [W']; split_ifs
    · exact hsmall _ _
    · exact hemp
  · intro x hx x' hx' hxx'
    have hδ : 0 < dist x x' := dist_pos.2 hxx'
    obtain ⟨r, hr⟩ := exists_nat_one_div_lt (show 0 < dist x x' / (2 * ε) by positivity)
    have hρr : 4 * ρ r < dist x x' := by
      have : ρ r = ε / 2 * (1 / ((r : ℝ) + 1)) := by
        simp only [hρ]; field_simp
      rw [this]
      have h2 : ε / 2 * (1 / ((r : ℝ) + 1)) < ε / 2 * (dist x x' / (2 * ε)) :=
        mul_lt_mul_of_pos_left hr (by positivity)
      have h3 : ε / 2 * (dist x x' / (2 * ε)) = dist x x' / 4 := by
        field_simp; ring
      linarith
    obtain ⟨p, hp⟩ := hd.exists_dist_lt x (hρpos r)
    obtain ⟨q, hq⟩ := hd.exists_dist_lt x' (hρpos r)
    have hpq : 2 * ρ r < dist (d p) (d q) := by
      have := dist_triangle4 x (d p) (d q) x'
      rw [dist_comm (d q) x'] at this
      linarith
    refine ⟨e (p, q, r), ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply, V', hpq, if_true]
      exact ⟨hx, mem_closedBall.2 hp.le⟩
    · simp only [Equiv.symm_apply_apply, W', hpq, if_true]
      exact ⟨hx', mem_closedBall.2 hq.le⟩

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
/-- **A7. Observation 2.** `Y` is a countable union of closed sets of diameter `≤ ε`. -/
theorem exists_small_closed_cover [SeparableSpace Y] {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℕ → Set Y, (∀ m, IsClosed (A m)) ∧
      (∀ m, Bornology.IsBounded (A m) ∧ diam (A m) ≤ ε) ∧ ⋃ m, A m = univ := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ⟨fun _ => ∅, fun _ => isClosed_empty,
      fun _ => ⟨Bornology.isBounded_empty, by simp [hε.le]⟩,
      eq_univ_of_forall fun y => (IsEmpty.false y).elim⟩
  · obtain ⟨d, hd⟩ := exists_dense_seq Y
    refine ⟨fun m => closedBall (d m) (ε / 2), fun m => isClosed_closedBall,
      fun m => ⟨isBounded_closedBall, (diam_closedBall (by positivity)).trans (by linarith)⟩,
      eq_univ_of_forall fun y => ?_⟩
    obtain ⟨m, hm⟩ := hd.exists_dist_lt y (half_pos hε)
    exact mem_iUnion.2 ⟨m, mem_closedBall.2 hm.le⟩

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
/-- `Fin.snoc s b` determines `s`. -/
theorem snoc_ne_snoc_of_ne {n : ℕ} {s s' : Fin n → Bool} (h : s ≠ s') (b b' : Bool) :
    (Fin.snoc s b : Fin (n + 1) → Bool) ≠ Fin.snoc s' b' := by
  intro hss
  apply h
  have := congrArg Fin.init hss
  rwa [Fin.init_snoc, Fin.init_snoc] at this

/-- The two children of a node are distinct. -/
theorem snoc_false_ne_snoc_true {n : ℕ} (s : Fin n → Bool) :
    (Fin.snoc s false : Fin (n + 1) → Bool) ≠ Fin.snoc s true := by
  intro hss
  have := congrFun hss (Fin.last n)
  simp only [Fin.snoc_last] at this
  exact Bool.false_ne_true this

/-- The splitting half of **A8**, by induction over the finite set `S` of parents already
split: the parents in `S` have been split into two disjoint small closed children by Shinko's
Lemma 1 (A4 + A6), the others still have both children equal to the parent. -/
theorem exists_split_level [SeparableSpace X] {f : X → Y} (hf : Continuous f) {n : ℕ}
    {F : (Fin n → Bool) → Set X} (hFc : ∀ s, IsClosed (F s)) (hF : ¬ IsNullFam f F)
    {ε : ℝ} (hε : 0 < ε) (S : Finset (Fin n → Bool)) :
    ∃ G : (Fin (n + 1) → Bool) → Set X, (∀ t, IsClosed (G t)) ∧ ¬ IsNullFam f G ∧
      (∀ t, G t ⊆ F (Fin.init t)) ∧
      (∀ s ∈ S, Disjoint (G (Fin.snoc s false)) (G (Fin.snoc s true))) ∧
      (∀ s ∈ S, ∀ b, Bornology.IsBounded (G (Fin.snoc s b)) ∧ diam (G (Fin.snoc s b)) ≤ ε) ∧
      (∀ s ∉ S, ∀ b, G (Fin.snoc s b) = F s) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨F ∘ Fin.init, fun t => hFc _, fun h => hF (IsNullFam.of_comp (Fin.init : (Fin (n + 1) → Bool) → Fin n → Bool) h),
      fun t => subset_rfl, fun s hs => absurd hs (Finset.notMem_empty s),
      fun s hs => absurd hs (Finset.notMem_empty s), fun s _ b => ?_⟩
    simp only [comp_apply, Fin.init_snoc]
  | @insert s S hs ih =>
    obtain ⟨G, hGc, hGn, hGsub, hGdisj, hGsmall, hGeq⟩ := ih
    set j : Fin (n + 1) → Bool := Fin.snoc s false with hj
    set k : Fin (n + 1) → Bool := Fin.snoc s true with hk
    have hjk : j ≠ k := snoc_false_ne_snoc_true s
    have hGj : G j = F s := hGeq s hs false
    have hGk : G k = F s := hGeq s hs true
    obtain ⟨V, W, hVc, hWc, hVU, hWU, hVW, hVs, hWs, hcov⟩ := exists_split_cover (hFc s) hε
    have : ∃ m, ¬ IsNullFam f (update (update G j (V m)) k (W m)) := by
      by_contra hcon
      push Not at hcon
      refine hGn (IsNullFam.of_split hf.measurable hjk (hGj.trans hGk.symm)
        (hGj ▸ (hFc s).measurableSet) (fun m => (hVc m).measurableSet)
        (fun m => (hWc m).measurableSet) ?_ hcon)
      rw [hGj]
      exact hcov
    obtain ⟨m, hm⟩ := this
    have hj' : update (update G j (V m)) k (W m) j = V m := by
      rw [update_of_ne hjk, update_self]
    have hk' : update (update G j (V m)) k (W m) k = W m := update_self _ _ _
    have ho : ∀ t, t ≠ j → t ≠ k → update (update G j (V m)) k (W m) t = G t :=
      fun t htj htk => by rw [update_of_ne htk, update_of_ne htj]
    have hos : ∀ s', s' ≠ s → ∀ b,
        update (update G j (V m)) k (W m) (Fin.snoc s' b) = G (Fin.snoc s' b) :=
      fun s' hs' b => ho _ (snoc_ne_snoc_of_ne hs' b false) (snoc_ne_snoc_of_ne hs' b true)
    refine ⟨update (update G j (V m)) k (W m), fun t => ?_, hm, fun t => ?_, fun s' hs' => ?_,
      fun s' hs' b => ?_, fun s' hs' b => ?_⟩
    · by_cases htk : t = k
      · rw [htk, hk']; exact hWc m
      by_cases htj : t = j
      · rw [htj, hj']; exact hVc m
      rw [ho t htj htk]; exact hGc t
    · by_cases htk : t = k
      · rw [htk, hk', hk, Fin.init_snoc]; exact hWU m
      by_cases htj : t = j
      · rw [htj, hj', hj, Fin.init_snoc]; exact hVU m
      rw [ho t htj htk]; exact hGsub t
    · by_cases hss : s' = s
      · subst hss
        rw [← hj, ← hk, hj', hk']
        exact hVW m
      · rw [hos s' hss, hos s' hss]
        exact hGdisj s' (Finset.mem_of_mem_insert_of_ne hs' hss)
    · by_cases hss : s' = s
      · subst hss
        cases b
        · rw [← hj, hj']; exact hVs m
        · rw [← hk, hk']; exact hWs m
      · rw [hos s' hss]
        exact hGsmall s' (Finset.mem_of_mem_insert_of_ne hs' hss) b
    · have hss : s' ≠ s := fun h => hs' (h ▸ Finset.mem_insert_self s S)
      rw [hos s' hss]
      exact hGeq s' (fun h => hs' (Finset.mem_insert_of_mem h)) b

/-- **A8. One level of the Cantor scheme.** -/
theorem exists_next_level [SeparableSpace X] [SeparableSpace Y] {f : X → Y}
    (hf : Continuous f) {n : ℕ} {F : (Fin n → Bool) → Set X} (hFc : ∀ s, IsClosed (F s))
    (hF : ¬ IsNullFam f F) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : (Fin (n + 1) → Bool) → Set X, (∀ t, IsClosed (G t)) ∧ ¬ IsNullFam f G ∧
      (∀ t, G t ⊆ F (Fin.init t)) ∧
      (∀ s : Fin n → Bool, Disjoint (G (Fin.snoc s false)) (G (Fin.snoc s true))) ∧
      (∀ t, Bornology.IsBounded (G t) ∧ diam (G t) ≤ ε) ∧
      ∃ A : Set Y, Bornology.IsBounded A ∧ diam A ≤ ε ∧ ∀ t, G t ⊆ f ⁻¹' A := by
  obtain ⟨G, hGc, hGn, hGsub, hGdisj, hGsmall, -⟩ :=
    exists_split_level hf hFc hF hε Finset.univ
  obtain ⟨A, hAc, hAs, hAcov⟩ := exists_small_closed_cover (Y := Y) hε
  have : ∃ m, ¬ IsNullFam f fun t => G t ∩ f ⁻¹' A m := by
    by_contra hcon
    push Not at hcon
    exact hGn (IsNullFam.of_cover (fun m => (hAc m).measurableSet) hAcov hcon)
  obtain ⟨m, hm⟩ := this
  refine ⟨fun t => G t ∩ f ⁻¹' A m, fun t => (hGc t).inter ((hAc m).preimage hf), hm,
    fun t => inter_subset_left.trans (hGsub t),
    fun s => (hGdisj s (Finset.mem_univ s)).mono inter_subset_left inter_subset_left,
    fun t => ?_, A m, (hAs m).1, (hAs m).2, fun t => inter_subset_right⟩
  have := hGsmall (Fin.init t) (Finset.mem_univ _) (t (Fin.last n))
  rw [Fin.snoc_init_self] at this
  exact ⟨this.1.subset inter_subset_left, (diam_mono inter_subset_left this.1).trans this.2⟩

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
/-- **A9. The Cantor scheme.** -/
theorem exists_cantorScheme [SeparableSpace X] [SeparableSpace Y] {f : X → Y}
    (hf : Continuous f) (h : ¬ InI f univ) :
    ∃ F : (n : ℕ) → (Fin n → Bool) → Set X,
      (∀ n s, IsClosed (F n s)) ∧ (∀ n s, (F n s).Nonempty) ∧
      (∀ n (t : Fin (n + 1) → Bool), F (n + 1) t ⊆ F n (Fin.init t)) ∧
      (∀ n s s', s ≠ s' → Disjoint (F n s) (F n s')) ∧
      (∀ (n : ℕ) s, Bornology.IsBounded (F (n + 1) s) ∧
        diam (F (n + 1) s) ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, ∃ A : Set Y, Bornology.IsBounded A ∧ diam A ≤ 1 / ((n : ℝ) + 1) ∧
        ∀ s, F (n + 1) s ⊆ f ⁻¹' A) := by
  have step : ∀ n (F : {F : (Fin n → Bool) → Set X // (∀ s, IsClosed (F s)) ∧
      ¬ IsNullFam f F}),
      ∃ G : {G : (Fin (n + 1) → Bool) → Set X // (∀ t, IsClosed (G t)) ∧ ¬ IsNullFam f G},
        (∀ t, G.1 t ⊆ F.1 (Fin.init t)) ∧
        (∀ s : Fin n → Bool, Disjoint (G.1 (Fin.snoc s false)) (G.1 (Fin.snoc s true))) ∧
        (∀ t, Bornology.IsBounded (G.1 t) ∧ diam (G.1 t) ≤ 1 / ((n : ℝ) + 1)) ∧
        ∃ A : Set Y, Bornology.IsBounded A ∧ diam A ≤ 1 / ((n : ℝ) + 1) ∧
          ∀ t, G.1 t ⊆ f ⁻¹' A := by
    intro n F
    obtain ⟨G, hGc, hGn, h1, h2, h3, h4⟩ :=
      exists_next_level hf F.2.1 F.2.2 (ε := 1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨⟨G, hGc, hGn⟩, h1, h2, h3, h4⟩
  choose next hnext using step
  have h0 : ¬ IsNullFam f (fun _ : Fin 0 → Bool => (univ : Set X)) := fun hn =>
    h (isNullFam_unique_iff.1 hn)
  let L : (n : ℕ) → {F : (Fin n → Bool) → Set X // (∀ s, IsClosed (F s)) ∧
      ¬ IsNullFam f F} := fun n =>
    Nat.rec (motive := fun n => {F : (Fin n → Bool) → Set X // (∀ s, IsClosed (F s)) ∧
      ¬ IsNullFam f F}) ⟨fun _ => univ, fun _ => isClosed_univ, h0⟩ (fun n F => next n F) n
  have hL : ∀ n, L (n + 1) = next n (L n) := fun n => rfl
  have hdisj : ∀ n (s s' : Fin n → Bool), s ≠ s' → Disjoint ((L n).1 s) ((L n).1 s') := by
    intro n
    induction n with
    | zero => intro s s' hss; exact absurd (Subsingleton.elim s s') hss
    | succ n ih =>
      intro t t' htt
      by_cases hinit : Fin.init t = Fin.init t'
      · obtain ⟨s, a, rfl⟩ : ∃ s a, t = Fin.snoc s a := ⟨_, _, (Fin.snoc_init_self t).symm⟩
        obtain ⟨s', a', rfl⟩ : ∃ s a, t' = Fin.snoc s a :=
          ⟨_, _, (Fin.snoc_init_self t').symm⟩
        rw [Fin.init_snoc, Fin.init_snoc] at hinit
        subst hinit
        rw [hL]
        have key := (hnext n (L n)).2.1 s
        cases a <;> cases a'
        · exact absurd rfl htt
        · exact key
        · exact key.symm
        · exact absurd rfl htt
      · rw [hL]
        exact (ih _ _ hinit).mono ((hnext n (L n)).1 t) ((hnext n (L n)).1 t')
  refine ⟨fun n => (L n).1, fun n s => (L n).2.1 s, fun n s => ?_, fun n t => ?_, hdisj,
    fun n s => ?_, fun n => ?_⟩
  · by_contra hne
    exact (L n).2.2 (isNullFam_of_eq_empty (not_nonempty_iff_eq_empty.1 hne))
  · exact (hnext n (L n)).1 t
  · exact (hnext n (L n)).2.2.1 s
  · exact (hnext n (L n)).2.2.2

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
/-- **A10. A fibre contains a copy of Cantor space.** -/
theorem exists_injective_cantor_in_fiber [CompleteSpace X] [SeparableSpace X]
    [SeparableSpace Y] {f : X → Y} (hf : Continuous f) (h : ¬ InI f univ) :
    ∃ y : Y, ∃ c : (ℕ → Bool) → X, Injective c ∧ ∀ b, f (c b) = y := by
  obtain ⟨F, hFc, hFne, hFsub, hFdisj, hFdiam, hFimg⟩ := exists_cantorScheme hf h
  -- the prefixes of a branch
  let pre : (ℕ → Bool) → (n : ℕ) → Fin n → Bool := fun b n i => b i
  have hnest : ∀ b n, F (n + 1) (pre b (n + 1)) ⊆ F n (pre b n) := fun b n =>
    hFsub n (pre b (n + 1))
  have hanti : ∀ b, Antitone fun n => F (n + 1) (pre b (n + 1)) := fun b =>
    antitone_nat_of_succ_le fun n => hnest b (n + 1)
  have hne : ∀ b, (⋂ n, F (n + 1) (pre b (n + 1))).Nonempty := fun b =>
    Metric.nonempty_iInter_of_nonempty_biInter (fun n => hFc _ _) (fun n => (hFdiam n _).1)
      (fun N => (hFne _ _).mono (subset_iInter₂ fun n hn => hanti b hn))
      (squeeze_zero (fun n => diam_nonneg) (fun n => (hFdiam n _).2)
        tendsto_one_div_add_atTop_nhds_zero_nat)
  choose c hc using hne
  have hcmem : ∀ b n, c b ∈ F (n + 1) (pre b (n + 1)) := fun b n => mem_iInter.1 (hc b) n
  refine ⟨f (c fun _ => false), c, fun b b' hbb => ?_, fun b => ?_⟩
  · by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hpre : pre b (i + 1) ≠ pre b' (i + 1) := fun hp => hi (congrFun hp (Fin.last i))
    have h1 := hcmem b i
    have h2 := hcmem b' i
    rw [← hbb] at h2
    exact disjoint_left.1 (hFdisj (i + 1) _ _ hpre) h1 h2
  · apply dist_le_zero.1
    refine ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat fun n => ?_
    obtain ⟨A, hAb, hAd, hAsub⟩ := hFimg n
    exact (dist_le_diam_of_mem hAb (hAsub _ (hcmem b n)) (hAsub _ (hcmem _ n))).trans hAd

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
/-- `ℕ → Bool` is uncountable (Cantor's diagonal argument). -/
theorem not_countable_nat_bool : ¬ Countable (ℕ → Bool) := by
  intro h
  obtain ⟨g, hg⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨m, hm⟩ := hg fun i => !(g i i)
  have := congrFun hm m
  cases hgm : g m m <;> simp [hgm] at this

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
/-- **A11. Shinko's Lusin–Novikov theorem, metric form.** -/
theorem inI_univ_of_countable_fibers [CompleteSpace X] [SeparableSpace X] [SeparableSpace Y]
    {f : X → Y} (hf : Continuous f) (hfib : ∀ y, (f ⁻¹' {y}).Countable) : InI f univ := by
  by_contra h
  obtain ⟨y, c, hc, hcy⟩ := exists_injective_cantor_in_fiber hf h
  have := (hfib y).to_subtype
  apply not_countable_nat_bool
  exact Injective.countable (f := fun b => (⟨c b, hcy b⟩ : f ⁻¹' {y}))
    fun b b' hbb => hc (congrArg Subtype.val hbb)

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
alias inI_univ_of_countable_fibers := CFWPlan.Route.PartA.inI_univ_of_countable_fibers

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
/-- §A11 for Polish spaces with their Borel σ-algebras: endow both spaces with complete metrics
(`upgradeIsCompletelyMetrizable`, whose topology is the given one by `replaceTopology`) and
apply the metric form. -/
theorem exists_injOn_cover_of_continuous {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} (hf : Continuous f)
    (hfib : ∀ y, (f ⁻¹' {y}).Countable) :
    ∃ S : ℕ → Set X, (∀ n, MeasurableSet (S n)) ∧ (∀ n, InjOn f (S n)) ∧ ⋃ n, S n = univ := by
  let := upgradeIsCompletelyMetrizable X
  let := upgradeIsCompletelyMetrizable Y
  obtain ⟨S, hS, hcov⟩ := CFWPlan.Route.inI_univ_of_countable_fibers (X := X) (Y := Y) hf hfib
  exact ⟨S, fun n => (hS n).1, fun n => (hS n).2, univ_subset_iff.1 hcov⟩

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartB
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
/-- **B1 = (LN-1).** -/
theorem exists_injOn_cover_of_countable_fibers {f : X → Y} (hf : Measurable f)
    (hfib : ∀ y, (f ⁻¹' {y}).Countable) :
    ∃ S : ℕ → Set X, (∀ n, MeasurableSet (S n)) ∧ (∀ n, InjOn f (S n)) ∧ ⋃ n, S n = univ := by
  obtain ⟨tX, hbX, hpX⟩ := ‹StandardBorelSpace X›.polish
  obtain ⟨tY, hbY, hpY⟩ := ‹StandardBorelSpace Y›.polish
  obtain ⟨t', ht'X, hf', hp'⟩ := hf.exists_continuous
  have hb' : @BorelSpace X t' _ :=
    ⟨by rw [hbX.measurable_eq, borel_eq_borel_of_le hp' hpX ht'X]⟩
  exact @exists_injOn_cover_of_continuous X Y t' hp' _ hb' tY hpY _ hbY f hf' hfib

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

theorem exists_injOn_cover_of_countable_fibers
    {f : X → Y} (hf : Measurable f) (hfib : ∀ y, (f ⁻¹' {y}).Countable) :
    ∃ S : ℕ → Set X, (∀ n, MeasurableSet (S n)) ∧ (∀ n, Set.InjOn f (S n)) ∧
      ⋃ n, S n = Set.univ :=
  CFWPlan.Route.PartB.exists_injOn_cover_of_countable_fibers hf hfib

end LusinNovikov

end
end

section
open LusinNovikov

theorem solution {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {f : X → Y} (hf : Measurable f) (hfib : ∀ y, (f ⁻¹' {y}).Countable) :
    ∃ S : ℕ → Set X, (∀ n, MeasurableSet (S n)) ∧ (∀ n, Set.InjOn f (S n)) ∧
      ⋃ n, S n = Set.univ := by
  apply LusinNovikov.exists_injOn_cover_of_countable_fibers <;> assumption

end
