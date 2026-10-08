-- Prove2me | solution 1 for KleywegtSAA.ExpRate.union_bound
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:13:22.882021+00:00
-- url     : https://prove2.me/submissions/b72d9c45-90a1-4933-977d-d9a6675fb26c

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology KleywegtSAA.ExpRate

private theorem finite_inclusion {X : Type*} (S : Finset X) (hS : S.Nonempty)
    (g f : X → ℝ) (ε : ℝ) (hne : (nonOptSet S hS g ε).Nonempty)
    (hdev : ∀ x ∈ S, |f x - g x| < alpha S hS g ε hne / 2) :
    epsSet S hS f ε ⊆ epsSet S hS g ε := by
  classical
  intro x hx
  change x ∈ S ∧ f x ≤ minVal S hS f + ε at hx
  change x ∈ S ∧ g x ≤ minVal S hS g + ε
  refine ⟨hx.1, ?_⟩
  by_contra hbad
  have hxn : x ∈ nonOptSet S hS g ε := Finset.mem_filter.mpr ⟨hx.1, lt_of_not_ge hbad⟩
  have hgap := Finset.inf'_le g hxn
  obtain ⟨y, hy, heq⟩ := Finset.exists_mem_eq_inf' hS g
  have hmin : minVal S hS f ≤ f y := Finset.inf'_le f hy
  have hdx := (abs_lt.mp (hdev x hx.1)).1
  have hdy := (abs_lt.mp (hdev y hy)).2
  unfold alpha minVal at *
  rw [heq] at hdy
  linarith

theorem solution {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} (G : X → 𝒲 → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (W : ℕ → Ω → 𝒲)
    (ε : ℝ) (hε : 0 ≤ ε) (hne : (nonOptSet S hS (trueObj G P W) ε).Nonempty) :
    ∀ N : ℕ,
      1 - P {ω | epsSet S hS (sampleObj G W N ω) ε ⊆ epsSet S hS (trueObj G P W) ε} ≤
        ∑ x ∈ S, P {ω | alpha S hS (trueObj G P W) ε hne / 2 ≤
          |sampleObj G W N ω x - trueObj G P W x|} := by
  classical
  intro N
  let A : Set Ω := {ω | epsSet S hS (sampleObj G W N ω) ε ⊆ epsSet S hS (trueObj G P W) ε}
  let B : X → Set Ω := fun x => {ω | alpha S hS (trueObj G P W) ε hne / 2 ≤
    |sampleObj G W N ω x - trueObj G P W x|}
  have hcover : Aᶜ ⊆ ⋃ x ∈ S, B x := by
    intro ω hω
    by_contra hb
    have hd : ∀ x ∈ S, |sampleObj G W N ω x - trueObj G P W x| <
        alpha S hS (trueObj G P W) ε hne / 2 := by
      intro x hx
      by_contra h
      apply hb
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, le_of_not_gt h⟩⟩
    exact hω (finite_inclusion S hS _ _ ε hne hd)
  have hc : (1 : ENNReal) - P A ≤ P Aᶜ := by
    apply tsub_le_iff_right.mpr
    simpa [add_comm] using (measure_univ_le_add_compl (μ := P) A)
  exact hc.trans ((measure_mono hcover).trans (measure_biUnion_finset_le S B))

#print axioms solution
