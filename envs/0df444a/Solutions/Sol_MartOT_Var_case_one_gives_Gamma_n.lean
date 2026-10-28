-- Prove2me | solution 1 for MartOT.Var.case_one_gives_Gamma_n
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:18:38.463168+00:00
-- url     : https://prove2.me/submissions/09af6298-ae89-4c2d-b971-aaa07e926225

import Mathlib
import Definitions.Def_MartOT_Var_BadTuples

open MeasureTheory

open MartOT.Var in
theorem solution (c : ℝ → ℝ → ℝ) (π : Measure (ℝ × ℝ)) (n : ℕ)
    (Ms : Fin n → Set (Fin n → ℝ × ℝ))
    (hnull : ∀ i, π ((fun z : Fin n → ℝ × ℝ => z i) '' Ms i) = 0)
    (hcover : BadTuples c n ⊆ ⋃ i, Ms i) :
    ∃ Γn : Set (ℝ × ℝ), MeasurableSet Γn ∧ π Γnᶜ = 0 ∧
      Γn ⊆ (⋃ i, (fun z : Fin n → ℝ × ℝ => z i) '' Ms i)ᶜ ∧
      ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), S.card ≤ n →
        (↑S : Set (ℝ × ℝ)) ⊆ Γn → ∀ α' : Measure (ℝ × ℝ),
          IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ cost c α' := by
  set N := ⋃ i, (fun z : Fin n → ℝ × ℝ => z i) '' Ms i with hN
  have hN0 : π N = 0 := measure_iUnion_null hnull
  refine ⟨(toMeasurable π N)ᶜ, (measurableSet_toMeasurable π N).compl, ?_, ?_, ?_⟩
  · rw [compl_compl, measure_toMeasurable, hN0]
  · exact Set.compl_subset_compl.mpr (subset_toMeasurable π N)
  · intro S w hcard hSsub α' hcomp
    by_cases hS : S = ∅
    · subst hS
      have h0 : α' = 0 := by
        have h1 := hcomp.1
        rw [Finset.sum_empty, Measure.map_zero] at h1
        exact (Measure.map_eq_zero_iff measurable_fst.aemeasurable).mp h1.symm
      rw [h0, Finset.sum_empty]
    · have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      let p : Fin n → ℝ × ℝ := fun i => (S.equivFin.symm ⟨i.val % S.card, Nat.mod_lt _ hpos⟩ : S)
      have hrange : Set.range p = (↑S : Set (ℝ × ℝ)) := by
        ext q
        constructor
        · rintro ⟨i, rfl⟩
          exact (S.equivFin.symm ⟨i.val % S.card, Nat.mod_lt _ hpos⟩).2
        · intro hq
          set k := S.equivFin ⟨q, hq⟩ with hk
          refine ⟨⟨k.val, lt_of_lt_of_le k.2 hcard⟩, ?_⟩
          simp only [p]
          have : (⟨k.val % S.card, Nat.mod_lt _ hpos⟩ : Fin S.card) = k := by
            ext
            exact Nat.mod_eq_of_lt k.2
          rw [this, hk, Equiv.symm_apply_apply]
      by_contra hlt
      push_neg at hlt
      have hmeasS : MeasurableSet (↑S : Set (ℝ × ℝ))ᶜ := S.measurableSet.compl
      have hbad : p ∈ BadTuples c n := by
        refine ⟨∑ p ∈ S, (w p : ENNReal) • Measure.dirac p, ?_, ?_, α', hcomp, hlt⟩
        · refine ⟨?_⟩
          rw [Measure.finsetSum_apply]
          simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
          exact ENNReal.sum_lt_top.mpr (fun q _ => ENNReal.coe_lt_top)
        · rw [hrange, Measure.finsetSum_apply]
          apply Finset.sum_eq_zero
          intro q hq
          rw [Measure.smul_apply, Measure.dirac_apply' _ hmeasS,
            Set.indicator_of_notMem (by simpa using hq), smul_zero]
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hbad)
      have hpiN : p i ∈ N := Set.mem_iUnion.mpr ⟨i, ⟨p, hi, rfl⟩⟩
      have hpiS : p i ∈ (↑S : Set (ℝ × ℝ)) := hrange ▸ Set.mem_range_self i
      exact hSsub hpiS (subset_toMeasurable π N hpiN)
