-- Prove2me | solution 1 for KleywegtSAA.ExpRate.subset_of_devMax_lt
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:11:10.470444+00:00
-- url     : https://prove2.me/submissions/911adaf5-13d6-44d4-8558-ca376550aef4

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
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℕ → Ω → 𝒲)
    (ε : ℝ) (hε : 0 ≤ ε) (hne : (nonOptSet S hS (trueObj G P W) ε).Nonempty) :
    ∀ (N : ℕ) (ω : Ω), devMax S hS G P W N ω < alpha S hS (trueObj G P W) ε hne / 2 →
      epsSet S hS (sampleObj G W N ω) ε ⊆ epsSet S hS (trueObj G P W) ε := by
  intro N ω h
  apply finite_inclusion S hS (trueObj G P W) (sampleObj G W N ω) ε hne
  intro x hx
  exact lt_of_le_of_lt (Finset.le_sup' (fun x => |sampleObj G W N ω x - trueObj G P W x|) hx) h

#print axioms solution
