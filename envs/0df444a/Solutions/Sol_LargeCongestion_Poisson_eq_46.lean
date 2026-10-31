-- Prove2me | solution 1 for LargeCongestion.Poisson.eq_46
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:26:19.736501+00:00
-- url     : https://prove2.me/submissions/06c695ff-e384-48a3-979f-418665a7ce9d

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LCPEq46Aux

lemma poisson_set_bound (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (A : Set ℕ) :
    |(poissonMeasure x.toNNReal A).toReal - (poissonMeasure y.toNNReal A).toReal| ≤
      1 - Real.exp (-(y - x)) := by
  set δ : ℝ := y - x with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hy : y.toNNReal = x.toNNReal + δ.toNNReal := by
    rw [← Real.toNNReal_add hx hδ0]; congr 1; rw [hδ]; ring
  set π : Measure (ℕ × ℕ) := (poissonMeasure x.toNNReal).prod (poissonMeasure δ.toNNReal) with hπ
  have hms : ∀ s : Set (ℕ × ℕ), MeasurableSet s := fun s => (Set.to_countable s).measurableSet
  have hmsN : ∀ s : Set ℕ, MeasurableSet s := fun s => (Set.to_countable s).measurableSet
  -- the two probabilities as probabilities of events under `π`
  have hY : (poissonMeasure y.toNNReal A).toReal = π.real ((fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' A) := by
    rw [hy, ← poissonMeasure_conv_poissonMeasure, Measure.conv, Measure.real,
      Measure.map_apply (by fun_prop) (hmsN A)]
  have hX : (poissonMeasure x.toNNReal A).toReal = π.real (A ×ˢ Set.univ) := by
    rw [Measure.real, hπ, Measure.prod_prod]
    simp
  have hZ : π.real (Set.univ ×ˢ ({0}ᶜ : Set ℕ)) = 1 - Real.exp (-δ) := by
    rw [Measure.real, hπ, Measure.prod_prod]
    simp only [measure_univ, one_mul]
    rw [← Measure.real, measureReal_compl (hmsN _), probReal_univ,
      poissonMeasure_real_singleton, Real.coe_toNNReal δ hδ0]
    simp
  set C : Set (ℕ × ℕ) := (fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' A
  set D : Set (ℕ × ℕ) := A ×ˢ Set.univ
  set Z : Set (ℕ × ℕ) := Set.univ ×ˢ ({0}ᶜ : Set ℕ)
  have hCD : C ⊆ D ∪ Z := by
    intro p hp
    by_cases h0 : p.2 = 0
    · left
      simp only [C, Set.mem_preimage, h0, add_zero] at hp
      exact ⟨hp, trivial⟩
    · right; exact ⟨trivial, h0⟩
  have hDC : D ⊆ C ∪ Z := by
    intro p hp
    by_cases h0 : p.2 = 0
    · left
      simp only [C, Set.mem_preimage, h0, add_zero]
      exact hp.1
    · right; exact ⟨trivial, h0⟩
  have h1 : π.real C ≤ π.real D + π.real Z :=
    (measureReal_mono hCD).trans (measureReal_union_le _ _)
  have h2 : π.real D ≤ π.real C + π.real Z :=
    (measureReal_mono hDC).trans (measureReal_union_le _ _)
  rw [hX, hY, abs_le]
  rw [hZ] at h1 h2
  constructor <;> linarith

end LCPEq46Aux

open LCPEq46Aux in
theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    MarkovChainCLT.tvDist (poissonMeasure x.toNNReal) (poissonMeasure y.toNNReal) ≤
        1 - Real.exp (-|x - y|) ∧
      1 - Real.exp (-|x - y|) ≤ |x - y| := by
  constructor
  · unfold MarkovChainCLT.tvDist
    apply csSup_le
    · exact ⟨_, ∅, MeasurableSet.empty, rfl⟩
    · rintro r ⟨A, -, rfl⟩
      rcases le_total x y with hxy | hxy
      · have := poisson_set_bound x y hx hxy A
        rwa [abs_sub_comm x y, abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]
      · have := poisson_set_bound y x hy hxy A
        rw [abs_sub_comm] at this
        rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)]
  · linarith [Real.add_one_le_exp (-|x - y|)]
