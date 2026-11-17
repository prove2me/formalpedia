-- Prove2me | solution 1 for MLManagesComplexity.kl_hypothesis_rearrangement
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-16T13:31:57.696188+00:00
-- url     : https://prove2.me/submissions/5c9779c3-dfe1-4393-a42f-cbbc3d55058d

import Mathlib
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

theorem solution {n : ℕ} (D μ : PMF (Fin n → Bool))
    (h : klBits D μ ≤ klBits D (uniformFamily n)) :
    crossEntropy D μ ≤ crossEntropy D (uniformFamily n) ∧
      crossEntropy D (uniformFamily n) = (n : EReal) := by
  have hD := kl_eq_crossEntropy_sub_entropy D μ
  have hU := kl_eq_crossEntropy_sub_entropy D (uniformFamily n)
  constructor
  · have hsub :
        crossEntropy D μ - (entropy D : EReal) ≤
          crossEntropy D (uniformFamily n) - (entropy D : EReal) := by
      simpa only [hD, hU] using h
    have hadd := add_le_add_left hsub (entropy D)
    simpa only [EReal.sub_add_cancel] using hadd
  · classical
    simp [AutoregressiveCompression.Main.crossEntropy, uniformFamily, mass,
      PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Real.logb_pow]
    have hmass : ∑ x, mass D x = 1 := by
      simp only [mass]
      calc
        _ = ∑' x, (D x).toReal := by simp
        _ = (∑' x, D x).toReal := (ENNReal.tsum_toReal_eq fun x => PMF.apply_ne_top D x).symm
        _ = 1 := by rw [PMF.tsum_coe]; norm_num
    have hterms :
        (∑ x, if D x = 0 then 0 else mass D x * (n : ℝ)) =
          (∑ x, mass D x) * n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hzero : D x = 0 <;> simp [hzero, mass]
    have hterms' :
        (∑ x, if D x = 0 then 0 else (D x).toReal * (n : ℝ)) =
          (∑ x, (D x).toReal) * n := by
      simpa only [mass] using hterms
    change (∑ x, (D x).toReal) = 1 at hmass
    rw [hterms', hmass]
    norm_num

end MLManagesComplexity

theorem solution {n : ℕ} (D μ : PMF (Fin n → Bool))
    (h : AutoregressiveCompression.Main.klBits D μ ≤
      AutoregressiveCompression.Main.klBits D (MLManagesComplexity.uniformFamily n)) :
    AutoregressiveCompression.Main.crossEntropy D μ ≤
        AutoregressiveCompression.Main.crossEntropy D (MLManagesComplexity.uniformFamily n) ∧
      AutoregressiveCompression.Main.crossEntropy D (MLManagesComplexity.uniformFamily n) =
        (n : EReal) :=
  MLManagesComplexity.solution D μ h
