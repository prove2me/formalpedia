-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.eventual_weighted_representatives_of_jet_powers
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T21:39:10.200327+00:00
-- url     : https://prove2.me/submissions/cf072d8b-4cd4-4fbf-9bb1-d1eeaa303c78
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_monic_relations_control_powers
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_produces_weighted_monic_relations

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
    ∃ A : ℝ, 0 < A ∧ A < R ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
          ∃ Q : WeightedPolynomial d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * A),
            P - Q.val ∈
              (simultaneousJetIdeal d.K
                (MatrixArithmetic.rationalCenters (finiteNumerators d)
                  (finiteDenominators d)) T e) ^ n := by
  classical
  obtain ⟨k, hk, a, ha, haR, b, hb, F, hF, hsize, hbelow⟩ :=
    strict_capacity_produces_weighted_monic_relations
      d R S e T hR hRS he hcommon hcapacity hT
  let w : Fin d.m → ℝ := MatrixArithmetic.logWeights (finiteDenominators d)
  let I : Ideal (MvPolynomial (Fin (d.m + 1)) ℂ) :=
    simultaneousJetIdeal d.K
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d)) T e
  have hw : ∀ i, 0 < InterpolationMatrix.columnWeights d.w0 w i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact d.w0_pos
    · change 0 < (Nat.ceil (Real.log (d.q j.val)) : ℝ)
      rw [← d.x_log j.val]
      exact lt_of_lt_of_le (by norm_num) (d.x_one_le (j.val + 1))
  let C : ℝ :=
    ∑ i, InterpolationMatrix.columnWeights d.w0 w i * ((b i - 1 : ℕ) : ℝ)
  have hrep (n : ℕ) (P : MvPolynomial (Fin (d.m + 1)) ℂ) :
      ∃ Q : WeightedPolynomial d.w0 w ((n : ℝ) * a + C),
        P - Q.val ∈ I ^ n := by
    exact weighted_monic_relations_control_powers
      d.w0 w hw I k hk b hb F hF hbelow a ha hsize n P
  let A : ℝ := (a + R) / 2
  have hA : 0 < A := by dsimp [A]; linarith
  have hAR : A < R := by dsimp [A]; linarith
  have hgap : 0 < A - a := by dsimp [A]; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (C / (A - a))
  have hCN : C < (N : ℝ) * (A - a) := (div_lt_iff₀ hgap).mp hN
  refine ⟨A, hA, hAR, N, ?_⟩
  intro n hn P
  obtain ⟨Q, hQ⟩ := hrep n P
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmul : (N : ℝ) * (A - a) ≤ (n : ℝ) * (A - a) :=
    mul_le_mul_of_nonneg_right hNn hgap.le
  have hbudget : (n : ℝ) * a + C ≤ (n : ℝ) * A := by
    nlinarith [hCN, hmul]
  refine ⟨⟨Q.val, ?_⟩, hQ⟩
  intro u hu
  exact (Q.property u hu).trans hbudget
