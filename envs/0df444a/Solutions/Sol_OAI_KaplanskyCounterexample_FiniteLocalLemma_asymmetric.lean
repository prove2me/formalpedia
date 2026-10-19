-- Prove2me | solution 1 for OAI.KaplanskyCounterexample.FiniteLocalLemma.asymmetric
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:37:36.961766+00:00
-- url     : https://prove2.me/submissions/18ce3535-5b79-4dea-9df9-e9a15114fd26

import Mathlib

section
-- module Solutions.OAIQW_Kaplansky.SlabAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace KaplanskyCounterexample.FiniteLocalLemma

variable {Ω : Type u_1} {ι : Type u_2}

/-- Avoid a finite list of bad events. -/
def avoid (E : ι → Set Ω) (s : Finset ι) : Set Ω := ⋂ i ∈ s, (E i)ᶜ

@[simp] lemma mem_avoid {E : ι → Set Ω} {s : Finset ι} {ω : Ω} :
    ω ∈ avoid E s ↔ ∀ i ∈ s, ω ∉ E i := by simp [avoid]

@[simp] lemma avoid_empty (E : ι → Set Ω) : avoid E ∅ = Set.univ := by
  simp [avoid]

variable [DecidableEq ι]

lemma avoid_insert (E : ι → Set Ω) (s : Finset ι) (i : ι) :
    avoid E (insert i s) = avoid E s \ E i := by
  ext ω
  simp only [mem_avoid, Finset.mem_insert, forall_eq_or_imp, mem_sdiff]
  tauto

omit [DecidableEq ι] in
lemma avoid_anti (E : ι → Set Ω) {s t : Finset ι} (h : s ⊆ t) :
    avoid E t ⊆ avoid E s := by
  intro ω hω
  exact mem_avoid.mpr fun i hi => mem_avoid.mp hω i (h hi)

variable [MeasurableSpace Ω]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : ι → Set Ω}

lemma prob_avoid_insert (hE : ∀ i, MeasurableSet (E i)) (s : Finset ι) (i : ι) :
    μ.real (avoid E (insert i s)) =
      μ.real (avoid E s) - μ.real (E i ∩ avoid E s) := by
  rw [avoid_insert]
  have h := measureReal_inter_add_sdiff (μ := μ) (s := avoid E s) (hE i)
  rw [Set.inter_comm (avoid E s) (E i)] at h
  linarith

/-- Successive avoidance bounds, in multiplication form (no conditional measure
or division by a possibly zero probability). -/
lemma avoid_union_lower {x : ι → ℝ} (hE : ∀ i, MeasurableSet (E i))
    (hx : ∀ i, 0 ≤ 1 - x i) (s t : Finset ι) (hd : Disjoint s t)
    (hc : ∀ (u : Finset ι), u ⊆ s ∪ t → ∀ i ∈ t, i ∉ u →
      μ.real (E i ∩ avoid E u) ≤ x i * μ.real (avoid E u)) :
    (∏ i ∈ t, (1 - x i)) * μ.real (avoid E s) ≤ μ.real (avoid E (s ∪ t)) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    have hdst : Disjoint s t := hd.mono_right (Finset.subset_insert _ _)
    have his : i ∉ s := fun his => Finset.disjoint_left.mp hd his (Finset.mem_insert_self _ _)
    have hit : i ∉ s ∪ t := by simp [his, hi]
    have hsub : s ∪ t ⊆ s ∪ insert i t :=
      Finset.union_subset_union_right (Finset.subset_insert _ _)
    have hct : ∀ u : Finset ι, u ⊆ s ∪ t → ∀ j ∈ t, j ∉ u →
        μ.real (E j ∩ avoid E u) ≤ x j * μ.real (avoid E u) := by
      intro u hu j hj hju
      exact hc u (hu.trans hsub) j (Finset.mem_insert_of_mem hj) hju
    have hlower := ih hdst hct
    have hlast := hc (s ∪ t) hsub i (Finset.mem_insert_self _ _) hit
    rw [Finset.prod_insert hi, mul_assoc]
    calc
      (1 - x i) * ((∏ j ∈ t, (1 - x j)) * μ.real (avoid E s))
          ≤ (1 - x i) * μ.real (avoid E (s ∪ t)) :=
        mul_le_mul_of_nonneg_left hlower (hx i)
      _ ≤ μ.real (avoid E (s ∪ insert i t)) := by
        rw [Finset.union_insert, prob_avoid_insert hE]
        nlinarith

omit [DecidableEq ι] in
/-- Product-form asymmetric Lovász local lemma on a finite event list.
The independence hypothesis is the usual independence from all non-neighbors
jointly, written directly as an equality of real probabilities. -/
theorem asymmetric_oai {x : ι → ℝ} (hE : ∀ i, MeasurableSet (E i))
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (Γ : ι → Finset ι)
    (hind : ∀ i (s : Finset ι), i ∉ s → Disjoint s (Γ i) →
      μ.real (E i ∩ ⋂ j ∈ s, (E j)ᶜ) = μ.real (E i) * μ.real (⋂ j ∈ s, (E j)ᶜ))
    (hprob : ∀ i, μ.real (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∀ s : Finset ι, 0 < μ.real (⋂ j ∈ s, (E j)ᶜ) ∧
      ∀ i ∉ s, μ.real (E i ∩ ⋂ j ∈ s, (E j)ᶜ) ≤ x i * μ.real (⋂ j ∈ s, (E j)ᶜ) := by
  classical
  change ∀ i (s : Finset ι), i ∉ s → Disjoint s (Γ i) →
      μ.real (E i ∩ avoid E s) = μ.real (E i) * μ.real (avoid E s) at hind
  show ∀ s : Finset ι, 0 < μ.real (avoid E s) ∧
      ∀ i ∉ s, μ.real (E i ∩ avoid E s) ≤ x i * μ.real (avoid E s)
  intro s
  induction s using Finset.strongInductionOn with | _ s ih
  have hxp : ∀ i, 0 < 1 - x i := fun i => sub_pos.mpr (hx1 i)
  have hxn : ∀ i, 0 ≤ 1 - x i := fun i => (hxp i).le
  have hpos : 0 < μ.real (avoid E s) := by
    by_cases hs : s = ∅
    · simp [hs, probReal_univ]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have ht : s.erase i ⊂ s := Finset.erase_ssubset hi
      obtain ⟨hprev, hcond⟩ := ih (s.erase i) ht
      have hc := hcond i (Finset.notMem_erase i s)
      have hins : insert i (s.erase i) = s := Finset.insert_erase hi
      rw [← hins, prob_avoid_insert hE]
      have hm := mul_pos (hxp i) hprev
      nlinarith
  refine ⟨hpos, ?_⟩
  intro i his
  let t := s \ Γ i
  let u := s ∩ Γ i
  have hts : t ⊆ s := Finset.sdiff_subset
  have hus : u ⊆ s := Finset.inter_subset_left
  have htu : Disjoint t u := by
    apply Finset.disjoint_left.mpr
    intro j hjt hju
    exact (Finset.mem_sdiff.mp hjt).2 (Finset.mem_inter.mp hju).2
  have hsu : t ∪ u = s := by
    ext j
    simp only [t, u, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have htg : Disjoint t (Γ i) := by
    apply Finset.disjoint_left.mpr
    intro j hjt hjg
    exact (Finset.mem_sdiff.mp hjt).2 hjg
  have hit : i ∉ t := fun h => his (hts h)
  have heq := hind i t hit htg
  have hnum : μ.real (E i ∩ avoid E s) ≤ μ.real (E i) * μ.real (avoid E t) := by
    rw [← heq]
    exact measureReal_mono (Set.inter_subset_inter_right _ (avoid_anti E hts))
  have hchain : (∏ j ∈ u, (1 - x j)) * μ.real (avoid E t) ≤ μ.real (avoid E s) := by
    rw [← hsu]
    apply avoid_union_lower hE hxn t u htu
    intro v hv j hju hjv
    have hvs : v ⊂ s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · simpa [hsu] using hv
      · intro he
        exact hjv (he.symm ▸ hus hju)
    exact (ih v hvs).2 j hjv
  have hprod : (∏ j ∈ Γ i, (1 - x j)) ≤ ∏ j ∈ u, (1 - x j) := by
    apply Finset.prod_le_prod_of_subset_of_le_one Finset.inter_subset_right
    · intro j _; exact hxn j
    · intro j _ _; linarith [hx0 j]
  calc
    μ.real (E i ∩ avoid E s) ≤ μ.real (E i) * μ.real (avoid E t) := hnum
    _ ≤ (x i * ∏ j ∈ u, (1 - x j)) * μ.real (avoid E t) := by
      apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
      exact (hprob i).trans (mul_le_mul_of_nonneg_left hprod (hx0 i))
    _ = x i * ((∏ j ∈ u, (1 - x j)) * μ.real (avoid E t)) := mul_assoc _ _ _
    _ ≤ x i * μ.real (avoid E s) := mul_le_mul_of_nonneg_left hchain (hx0 i)

end KaplanskyCounterexample.FiniteLocalLemma

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KaplanskyCounterexample.FiniteLocalLemma.asymmetric_oai.{u_1, u_2} := @OAI.KaplanskyCounterexample.FiniteLocalLemma.asymmetric_oai.{u_1, u_2}
