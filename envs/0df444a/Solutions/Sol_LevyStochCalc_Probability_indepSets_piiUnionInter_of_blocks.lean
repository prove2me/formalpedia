-- Prove2me | solution 1 for LevyStochCalc.Probability.indepSets_piiUnionInter_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:01:41.876846+00:00
-- url     : https://prove2.me/submissions/2bd42cab-b22e-4554-b14f-ef98ac7f7bd8

import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Independence of two joins from blockwise independence

An independent family of σ-algebras, each containing two independent sub-σ-algebras, has the two
joins of those sub-σ-algebras independent: a finite intersection from each join is a single
intersection over the union of the two index sets, which the family's independence factors
blockwise and the blockwise independence factors again.
-/

open MeasureTheory MeasurableSpace ProbabilityTheory

namespace LevyStochCalc.Probability

variable {Ω ι : Type*} [DecidableEq ι] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]


omit [DecidableEq ι] in
theorem _root_.solution {m a b : ι → MeasurableSpace Ω}
    (ha : ∀ i, a i ≤ m i) (hb : ∀ i, b i ≤ m i)
    (hm : iIndep m μ) (hab : ∀ i, Indep (a i) (b i) μ) :
    IndepSets (piiUnionInter (fun i => {t | MeasurableSet[a i] t}) Set.univ)
      (piiUnionInter (fun i => {t | MeasurableSet[b i] t}) Set.univ) μ := by
  classical
  rw [IndepSets_iff]
  rintro _ _ ⟨s, -, f, hf, rfl⟩ ⟨u, -, g, hg, rfl⟩
  set U := s ∪ u
  let A : ι → Set Ω := fun i => if i ∈ s then f i else Set.univ
  let B : ι → Set Ω := fun i => if i ∈ u then g i else Set.univ
  have hA : ∀ i, MeasurableSet[a i] (A i) := fun i => by
    by_cases h : i ∈ s
    · simp only [A, if_pos h]; exact hf i h
    · simp only [A, if_neg h]; exact MeasurableSet.univ
  have hB : ∀ i, MeasurableSet[b i] (B i) := fun i => by
    by_cases h : i ∈ u
    · simp only [B, if_pos h]; exact hg i h
    · simp only [B, if_neg h]; exact MeasurableSet.univ
  have e1 : (⋂ i ∈ s, f i) = ⋂ i ∈ U, A i := by
    ext x; simp only [Set.mem_iInter, A, U, Finset.mem_union]
    constructor
    · intro hx i hi; split_ifs with h; exact hx i h; trivial
    · intro hx i hi; have := hx i (Or.inl hi); rwa [if_pos hi] at this
  have e2 : (⋂ i ∈ u, g i) = ⋂ i ∈ U, B i := by
    ext x; simp only [Set.mem_iInter, B, U, Finset.mem_union]
    constructor
    · intro hx i hi; split_ifs with h; exact hx i h; trivial
    · intro hx i hi; have := hx i (Or.inr hi); rwa [if_pos hi] at this
  have e3 : (⋂ i ∈ U, A i) ∩ (⋂ i ∈ U, B i) = ⋂ i ∈ U, (A i ∩ B i) := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h i hi => ⟨h.1 i hi, h.2 i hi⟩, fun h => ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩⟩
  rw [e1, e2, e3, hm.meas_biInter (fun i _ => ((ha i) _ (hA i)).inter ((hb i) _ (hB i))),
    hm.meas_biInter (fun i _ => (ha i) _ (hA i)), hm.meas_biInter (fun i _ => (hb i) _ (hB i)),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (Indep_iff _ _ _).1 (hab i) _ _ (hA i) (hB i)
