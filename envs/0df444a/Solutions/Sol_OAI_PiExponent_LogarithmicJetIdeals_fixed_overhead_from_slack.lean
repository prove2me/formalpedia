-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.fixed_overhead_from_slack
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T18:03:32.752928+00:00
-- url     : https://prove2.me/submissions/1aa479d5-cbfc-4ac2-8039-92bd49e8e4e1

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {nu : ℝ} (d : FixedData nu)
    (R S : ℝ) (T : Fin d.m → ℕ) (e : Fin (d.m + 1) → ℕ) (N : ℕ)
    (hR : 0 < R) (hRS : R < S)
    (hrep : ∀ n : ℕ, N ≤ n →
      ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
        ∃ Q : WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * R),
          P - Q.val ∈ (simultaneousJetIdeal d.K
            (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
            T e) ^ n) :
    ∀ B : ℕ, ∃ M : ℕ, ∀ k : ℕ, M ≤ k →
      ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
        ∃ Q : WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) ((k : ℝ) * S),
          P - Q.val ∈ (simultaneousJetIdeal d.K
            (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
            T e) ^ (k + B) := by
  intro B
  have hgap : 0 < S - R := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((B : ℝ) * R / (S - R))
  refine ⟨max N m, ?_⟩
  intro k hk P
  have hNk : N ≤ k := le_trans (le_trans (Nat.le_max_left N m) hk) (Nat.le_refl k)
  have hmk : m ≤ k := le_trans (Nat.le_max_right N m) hk
  have hmkR : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
  have hratio : (B : ℝ) * R < (m : ℝ) * (S - R) := by
    rw [div_lt_iff₀ hgap] at hm
    exact hm
  have hslack : (B : ℝ) * R ≤ (k : ℝ) * (S - R) := by
    have hmul : (m : ℝ) * (S - R) ≤ (k : ℝ) * (S - R) :=
      mul_le_mul_of_nonneg_right hmkR (le_of_lt hgap)
    linarith
  have hscale : ((k + B : ℕ) : ℝ) * R ≤ (k : ℝ) * S := by
    push_cast
    nlinarith [hslack]
  obtain ⟨Q, hQ⟩ := hrep (k + B) (by omega) P
  refine ⟨⟨Q.val, ?_⟩, hQ⟩
  intro a ha
  calc
    ∑ i, InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) i * (a i : ℝ)
      ≤ ((k + B : ℕ) : ℝ) * R := Q.property a ha
    _ ≤ (k : ℝ) * S := hscale
