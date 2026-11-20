-- Prove2me | solution 1 for LevyStochCalc.Poisson.ae_exists_nat_superposition
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:59:24.870931+00:00
-- url     : https://prove2.me/submissions/d6760d3a-ce75-45be-9e82-f703a139c684

import Definitions.Def_LevyStochCalc_Poisson_PoissonSuperposition_F000


open MeasureTheory ProbabilityTheory Complex Filter Function Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u

section Piece

variable {𝓧 : Type u} [MeasurableSpace 𝓧]

variable {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧) [∀ p, IsProbabilityMeasure (ρ p)]

variable {r ρ}

variable (r ρ)

variable {r ρ}

variable (r ρ)

variable [Countable ι]

end Piece

section Exhaustion

end Exhaustion

section Law

variable {𝓧 : Type u} [MeasurableSpace 𝓧] {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧)
  [∀ p, IsProbabilityMeasure (ρ p)]

variable {r ρ}

variable (r ρ)

variable [Countable ι]

theorem AuxSup.tsum_nat {ι : Type*} (k : ι → ℕ) (h : ∑' i, (k i : ℝ≥0∞) ≠ ⊤) :
    ∃ n : ℕ, ∑' i, (k i : ℝ≥0∞) = n := by
  have hfin : {i | k i ≠ 0}.Finite := by
    refine (ENNReal.finite_const_le_of_tsum_ne_top h one_ne_zero).subset fun i hi => ?_
    simp only [Set.mem_setOf_eq] at hi ⊢
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
  refine ⟨∑ i ∈ hfin.toFinset, k i, ?_⟩
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · push_cast; rfl
  · intro i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hi
    simp [hi]

theorem _root_.solution {B : Set 𝓧} (hB : MeasurableSet B)
    (hfin : superIntensity r ρ B ≠ ⊤) :
    ∀ᵐ ω ∂(superLaw r ρ), ∃ n : ℕ, superposition ω B = n := by
  filter_upwards [ae_lt_top_superposition r ρ hB hfin] with ω hω
  rw [superposition_apply ω hB] at hω ⊢
  exact AuxSup.tsum_nat _ hω.ne

end Law

end LevyStochCalc.Poisson
