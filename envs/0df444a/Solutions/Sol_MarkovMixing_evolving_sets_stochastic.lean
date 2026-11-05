-- Prove2me | solution 1 for MarkovMixing.evolving_sets_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @steven
-- created : 2026-08-22T22:33:02.223448+00:00
-- url     : https://prove2.me/submissions/cd2a8687-9cee-4238-b333-55d82f469d80

import Definitions.Def_mm_martingale
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open scoped BigOperators
open MarkovMixing

namespace EvolvingSetsStochastic

private noncomputable def lvlU {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℝ) (T : Finset V) : ℝ :=
  if h : T.Nonempty then T.inf' h f else 1

private noncomputable def lvlL {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℝ) (T : Finset V) : ℝ :=
  if h : Tᶜ.Nonempty then Tᶜ.sup' h f else 0

private lemma lvlU_le {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    {T : Finset V} {y : V} (hy : y ∈ T) : lvlU f T ≤ f y := by
  rw [lvlU, dif_pos ⟨y, hy⟩]
  exact Finset.inf'_le f hy

private lemma le_lvlL {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    {T : Finset V} {y : V} (hy : y ∈ Tᶜ) : f y ≤ lvlL f T := by
  rw [lvlL, dif_pos ⟨y, hy⟩]
  exact Finset.le_sup' f hy

private lemma lvlL_nonneg {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    (hf0 : ∀ z : V, 0 ≤ f z) (T : Finset V) : 0 ≤ lvlL f T := by
  rw [lvlL]
  split
  · rename_i h
    obtain ⟨z, hz⟩ := h
    exact le_trans (hf0 z) (Finset.le_sup' f hz)
  · rfl

private lemma lvlU_le_one {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    (hf1 : ∀ z : V, f z ≤ 1) (T : Finset V) : lvlU f T ≤ 1 := by
  rw [lvlU]
  split
  · rename_i h
    obtain ⟨z, hz⟩ := h
    exact le_trans (Finset.inf'_le f hz) (hf1 z)
  · rfl

private lemma lvl_union_all {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    (hf0 : ∀ z : V, 0 ≤ f z) (hf1 : ∀ z : V, f z ≤ 1) :
    (⋃ T ∈ (Finset.univ : Finset (Finset V)), Set.Ioc (lvlL f T) (lvlU f T)) =
      Set.Ioc 0 1 := by
  classical
  ext u
  simp only [Set.mem_iUnion, Set.mem_Ioc, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨T, -, hlo, hhi⟩
    exact ⟨lt_of_le_of_lt (lvlL_nonneg f hf0 T) hlo,
      le_trans hhi (lvlU_le_one f hf1 T)⟩
  · rintro ⟨hu0, hu1⟩
    let T := Finset.univ.filter (fun z : V => u ≤ f z)
    refine ⟨T, trivial, ?_, ?_⟩
    · rw [lvlL]
      split
      · rename_i h
        rw [Finset.sup'_lt_iff]
        intro z hz
        simp only [T, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
          not_le] at hz
        exact hz
      · exact hu0
    · rw [lvlU]
      split
      · rename_i h
        rw [Finset.le_inf'_iff]
        intro z hz
        simpa [T] using hz
      · exact hu1

private lemma lvl_disjoint_all {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ) :
    (Set.univ : Set (Finset V)).PairwiseDisjoint
      (fun T => Set.Ioc (lvlL f T) (lvlU f T)) := by
  classical
  have key : ∀ (R : Finset V) (u : ℝ), u ∈ Set.Ioc (lvlL f R) (lvlU f R) →
      R = Finset.univ.filter (fun z : V => u ≤ f z) := by
    intro R u hu
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz
      exact le_trans hu.2 (lvlU_le f hz)
    · intro hz
      by_contra hzR
      have hle : f z ≤ lvlL f R := le_lvlL f (Finset.mem_compl.mpr hzR)
      linarith [hu.1]
  intro T _ T' _ hne
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro u huT huT'
  exact hne ((key T u huT).trans (key T' u huT').symm)

private lemma lvl_row_sum {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    (hf0 : ∀ z : V, 0 ≤ f z) (hf1 : ∀ z : V, f z ≤ 1) :
    ∑ T : Finset V, max 0 (lvlU f T - lvlL f T) = 1 := by
  classical
  have hm := MeasureTheory.measure_biUnion_finset (μ := MeasureTheory.volume)
    (s := (Finset.univ : Finset (Finset V)))
    (by simpa using lvl_disjoint_all f) (fun T _ => measurableSet_Ioc)
  rw [lvl_union_all f hf0 hf1] at hm
  simp only [Real.volume_Ioc] at hm
  have hto := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_sum (fun T _ => ENNReal.ofReal_ne_top)] at hto
  simp only [ENNReal.toReal_ofReal'] at hto
  norm_num at hto
  calc
    ∑ T : Finset V, max 0 (lvlU f T - lvlL f T) =
        ∑ T : Finset V, max (lvlU f T - lvlL f T) 0 :=
      Finset.sum_congr rfl fun T _ => max_comm _ _
    _ = 1 := hto.symm

end EvolvingSetsStochastic

/-- The threshold construction defining the evolving-set process is a stochastic matrix. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (π : V → ℝ) : IsStochastic (evolvingSets P π) := by
  constructor
  · intro S T
    exact le_max_left 0 _
  · intro S
    let f : V → ℝ := fun z => min 1 (max 0 (esThresh P π S z))
    have hf0 : ∀ z : V, 0 ≤ f z := fun _ => le_min zero_le_one (le_max_left _ _)
    have hf1 : ∀ z : V, f z ≤ 1 := fun _ => min_le_left _ _
    change ∑ T : Finset V, max 0
      (EvolvingSetsStochastic.lvlU f T - EvolvingSetsStochastic.lvlL f T) = 1
    exact EvolvingSetsStochastic.lvl_row_sum f hf0 hf1
