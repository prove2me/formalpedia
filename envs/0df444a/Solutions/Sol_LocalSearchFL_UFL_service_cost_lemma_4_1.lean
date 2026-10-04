-- Prove2me | solution 1 for LocalSearchFL.UFL.service_cost_lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:59:19.444985+00:00
-- url     : https://prove2.me/submissions/f2216c9e-720b-4190-a3a9-f9b29e675f35

import Mathlib
import Definitions.Def_LocalSearchFL_UFL_captures

set_option autoImplicit false

open LocalSearchFL.UFL in
theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (O : Finset Fa) (hO : O.Nonempty) :
    costS I S hS ≤ costF f O + costS I O hO := by
  set g : Cl → Fa → ℝ := fun j o =>
    S.inf' hS (fun i => I.c j i) - I.c j o ⊓ S.inf' hS (fun i => I.c j i) with hg
  have hg0 : ∀ j o, 0 ≤ g j o := fun j o => by
    simp only [hg]
    linarith [inf_le_right (a := I.c j o) (b := S.inf' hS (fun i => I.c j i))]
  have hadd : ∀ o, ∑ j, g j o ≤ f o := by
    intro o
    have h := hloc.1 o
    unfold uflCost costS at h
    have hins : ∀ j, (insert o S).inf' (Finset.insert_nonempty o S) (fun i => I.c j i)
        = I.c j o ⊓ S.inf' hS (fun i => I.c j i) := fun j => Finset.inf'_insert _ _
    simp only [hins] at h
    have hF : costF f (insert o S) ≤ costF f S + f o := by
      unfold costF
      by_cases ho : o ∈ S
      · rw [Finset.insert_eq_of_mem ho]; linarith [hf o]
      · rw [Finset.sum_insert ho]; linarith
    simp only [hg, Finset.sum_sub_distrib]
    linarith
  have hpt : ∀ j, S.inf' hS (fun i => I.c j i) - O.inf' hO (fun i => I.c j i)
      ≤ ∑ o ∈ O, g j o := by
    intro j
    obtain ⟨o, hoO, hoeq⟩ := Finset.exists_mem_eq_inf' hO (fun i => I.c j i)
    have h1 : g j o ≤ ∑ o' ∈ O, g j o' :=
      Finset.single_le_sum (f := g j) (fun o' _ => hg0 j o') hoO
    have h2 : S.inf' hS (fun i => I.c j i) - O.inf' hO (fun i => I.c j i) ≤ g j o := by
      rw [hoeq]
      simp only [hg]
      linarith [inf_le_left (a := I.c j o) (b := S.inf' hS (fun i => I.c j i))]
    linarith
  have hsum : costS I S hS - costS I O hO ≤ ∑ j, ∑ o ∈ O, g j o := by
    unfold costS
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun j _ => hpt j)
  have hswap : ∑ j, ∑ o ∈ O, g j o = ∑ o ∈ O, ∑ j, g j o := Finset.sum_comm
  have hF : ∑ o ∈ O, ∑ j, g j o ≤ costF f O := by
    unfold costF
    exact Finset.sum_le_sum (fun o _ => hadd o)
  linarith
