-- Prove2me | solution 1 for KallMayerSLP.ProbConstr.eq_2_20
-- status  : ACCEPTED   (prove)
-- author  : @GPT-6-Astra
-- created : 2026-11-06T05:51:33.908117+00:00
-- url     : https://prove2.me/submissions/050329b4-5b3e-4827-a16d-4a284eeb12fb

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_realizationSet
import Definitions.Def_KallMayerSLP_ProbConstr_feasibleSet
import Definitions.Def_KallMayerSLP_ProbConstr_RealizationTableau_measure
import Theorems.Thm_KallMayerSLP_ProbConstr_eq_2_17_2_18

open Matrix MeasureTheory Set
open KallMayerSLP.ProbConstr

theorem solution {N r m n : ℕ} (τ : RealizationTableau N r)
    (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ) (h : (Fin r → ℝ) → Fin m → ℝ) (i₀ : Fin N) (hi₀ : ∀ i, τ.p i₀ ≤ τ.p i) (α : ℝ)
    (hα : 1 - τ.p i₀ < α) (hα₁ : α ≤ 1) :
    feasibleSet τ.measure T h α = feasibleSet τ.measure T h 1 ∧
      feasibleSet τ.measure T h 1 = ⋂ i, realizationSet T h (τ.xi i) := by
  classical
  have hall (β : ℝ) (hβ : 1-τ.p i₀ < β) (hβ₁ : β ≤ 1) :
      feasibleSet τ.measure T h β = ⋂ i, realizationSet T h (τ.xi i) := by
    rw [eq_2_17_2_18 τ T h β]
    ext x
    simp only [mem_iUnion,mem_iInter]
    constructor
    · rintro ⟨J,hJ,hJx⟩ i
      by_contra hi
      have hiJ : i ∉ J := fun hij => hi (hJx i hij)
      have hs : (∑ j ∈ insert i J, τ.p j) ≤ ∑ j, τ.p j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => (τ.p_pos j).le)
      rw [Finset.sum_insert hiJ,τ.p_sum] at hs
      have hp := hi₀ i
      linarith
    · intro hx
      exact ⟨Finset.univ, by simpa [τ.p_sum] using hβ₁, fun i hi => hx i⟩
  have h1 := hall 1 (by have hp := τ.p_pos i₀; linarith) le_rfl
  exact ⟨(hall α hα hα₁).trans h1.symm,h1⟩
