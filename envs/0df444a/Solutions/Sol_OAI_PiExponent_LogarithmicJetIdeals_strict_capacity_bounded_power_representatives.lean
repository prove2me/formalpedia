-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_bounded_power_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:17:00.928555+00:00
-- url     : https://prove2.me/submissions/b488dd35-2828-43b9-aa33-f482b7a6055a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_weighted_monic_relations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_monic_relations_control_powers

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {nu : ℝ} (d : FixedData nu) (R S : ℝ)
    (e : Fin (d.m + 1) → ℕ) (T : Fin d.m → ℕ)
    (hR : 0 < R) (hRS : R < S)
    (he : ∀ i, 0 < e i)
    (hcommon : ∀ i, S = (e i : ℝ) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i)
    (hcapacity : 2 * R ^ (d.m + 1 : ℕ) > S ^ (d.m + 1 : ℕ))
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ <
      (T i : ℝ) * (d.v0 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
      ∃ A : ℕ, ∀ a : ℕ, A ≤ a →
        ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
          ∃ Q : MvPolynomial (Fin (d.m + 1)) ℂ,
            P - Q ∈ (simultaneousJetIdeal d.K
              (MatrixArithmetic.rationalCenters (finiteNumerators d)
                (finiteDenominators d)) T e) ^ a ∧
            ∀ b ∈ Q.support,
              ∑ i, InterpolationMatrix.columnWeights d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) i *
                  (b i : ℝ) ≤ (a : ℝ) * δ := by
  classical
  -- The new geometric child: weighted monic relations with slope below R.
  obtain ⟨k, hk, b, hb, F, a, ha_pos, haR, hmem, hbelow, hsize⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_weighted_monic_relations
      d R S e T hR hRS he hcommon hcapacity hT
  -- Positivity of the column weights.
  have hw : ∀ i : Fin (d.m + 1), 0 < InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp only [InterpolationMatrix.columnWeights, Fin.cases_zero]
      exact d.w0_pos
    · intro j
      simp only [InterpolationMatrix.columnWeights, Fin.cases_succ]
      have hq2 : (2 : ℕ) ≤ (finiteDenominators d) j := (d.approximations j.val).1
      have h1 : (1 : ℝ) < ((finiteDenominators d) j : ℝ) := by
        have h2 : (1 : ℕ) < (finiteDenominators d) j := by omega
        exact_mod_cast h2
      have h3 : (0 : ℕ) < ⌈Real.log ((finiteDenominators d) j)⌉₊ :=
        Nat.ceil_pos.mpr (Real.log_pos h1)
      unfold MatrixArithmetic.logWeights
      exact_mod_cast h3
  -- The generic normal-form theorem converts the relations into bounded representatives.
  have hmain := OAI.PiExponent.LogarithmicJetIdeals.weighted_monic_relations_control_powers
    (m := d.m) (d.w0 : ℝ) (MatrixArithmetic.logWeights (finiteDenominators d)) hw
    (simultaneousJetIdeal d.K
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T e)
    k hk b hb F hmem hbelow a ha_pos hsize
  -- Fixed additive overhead of the relation degree.
  set C0 : ℝ := ∑ i, InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) i * ((b i - 1 : ℕ) : ℝ) with hC0def
  have hC0nonneg : 0 ≤ C0 := by
    rw [hC0def]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hw i)) (Nat.cast_nonneg _))
  -- Absorb the overhead into the slack between a and R.
  set δ : ℝ := (a + R) / 2 with hδdef
  have hδa : a < δ := by rw [hδdef]; linarith
  have hδR : δ < R := by rw [hδdef]; linarith
  have hδpos : 0 < δ := lt_trans ha_pos hδa
  have hslack : 0 < δ - a := sub_pos.mpr hδa
  set A : ℕ := ⌈C0 / (δ - a)⌉₊ with hAdef
  refine ⟨δ, hδpos, hδR, A, ?_⟩
  intro n hn P
  obtain ⟨Q, hQI⟩ := hmain n P
  refine ⟨Q.val, hQI, ?_⟩
  have hQbound := Q.property
  intro u hu
  have h1 : ∑ i, InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) i * (u i : ℝ) ≤
      (n : ℝ) * a + C0 := by
    simpa using hQbound u hu
  have h2 : C0 ≤ (n : ℝ) * (δ - a) := by
    have h3 : C0 / (δ - a) ≤ (A : ℝ) := Nat.le_ceil _
    have h4 : C0 / (δ - a) ≤ (n : ℝ) := le_trans h3 (by exact_mod_cast hn)
    exact (div_le_iff₀ hslack).mp h4
  nlinarith [h1, h2]
