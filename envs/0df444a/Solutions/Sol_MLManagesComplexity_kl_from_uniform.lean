-- Prove2me | solution 1 for MLManagesComplexity.kl_from_uniform
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-16T12:24:30.659452+00:00
-- url     : https://prove2.me/submissions/33a4d05d-ffa0-4be5-a037-e5f1537eb1f7

import Mathlib
import Lean
import Definitions.Def_MLManagesComplexity_lexCDF

set_option autoImplicit false

open AutoregressiveCompression.Main
namespace MLManagesComplexity

private theorem kl_eq_crossEntropy_sub_entropy {Ω : Type} [Fintype Ω]
    (τ μ : PMF Ω) :
    klBits τ μ = crossEntropy τ μ - (entropy τ : EReal) := by
  classical
  by_cases hbad : ∃ x, τ x ≠ 0 ∧ μ x = 0
  · simp [klBits, crossEntropy, AutoregressiveCompression.Main.entropy,
      FuchsVdGraaf.entropy, hbad]
  · have hsum :
        (∑ x, if τ x = 0 then 0 else mass τ x * Real.logb 2 (mass τ x / mass μ x)) =
          (∑ x, if τ x = 0 then 0 else mass τ x * Real.logb 2 (1 / mass μ x)) +
          (∑ x, mass τ x * Real.logb 2 (mass τ x)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hτ : τ x = 0
      · simp [hτ, mass]
      · have hμ : μ x ≠ 0 := by
          intro hμ0
          exact hbad ⟨x, hτ, hμ0⟩
        have hτmass : mass τ x ≠ 0 := by
          change (τ x).toReal ≠ 0
          exact (ENNReal.toReal_ne_zero).2 ⟨hτ, PMF.apply_ne_top τ x⟩
        have hμmass : mass μ x ≠ 0 := by
          change (μ x).toReal ≠ 0
          exact (ENNReal.toReal_ne_zero).2 ⟨hμ, PMF.apply_ne_top μ x⟩
        simp only [hτ, if_false]
        rw [Real.logb_div hτmass hμmass, one_div, Real.logb_inv]
        ring
    simp only [klBits, crossEntropy, hbad, if_false,
      AutoregressiveCompression.Main.entropy, FuchsVdGraaf.entropy]
    change ((∑ x, if τ x = 0 then 0 else mass τ x * Real.logb 2 (mass τ x / mass μ x) : ℝ) : EReal) =
      ((∑ x, if τ x = 0 then 0 else mass τ x * Real.logb 2 (1 / mass μ x) : ℝ) : EReal) -
      ((-∑ x, mass τ x * Real.logb 2 (mass τ x) : ℝ) : EReal)
    have h := congrArg (fun z : ℝ => (z : EReal)) hsum
    simpa only [EReal.coe_add, EReal.coe_neg, sub_eq_add_neg, neg_neg] using h

theorem kl_from_uniform_exact {n : ℕ} (μ : PMF (Fin n → Bool)) :
    klBits (uniformFamily n) μ =
      crossEntropy (uniformFamily n) μ - (n : EReal) := by
  rw [kl_eq_crossEntropy_sub_entropy]
  have hu : entropy (uniformFamily n) = (n : ℝ) := by
    classical
    simp [AutoregressiveCompression.Main.entropy, FuchsVdGraaf.entropy,
      uniformFamily, mass, PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Real.logb_pow]
  rw [hu]
  rfl

end MLManagesComplexity

theorem solution {n : ℕ} (μ : PMF (Fin n → Bool)) :
    AutoregressiveCompression.Main.klBits (MLManagesComplexity.uniformFamily n) μ =
      AutoregressiveCompression.Main.crossEntropy (MLManagesComplexity.uniformFamily n) μ - (n : EReal) :=
  MLManagesComplexity.kl_from_uniform_exact μ
