-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_degree_budget
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:41:33.269789+00:00
-- url     : https://prove2.me/submissions/467eabc8-23d9-4242-ae86-ebc5c7567ef0

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

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
    ∃ k : ℕ, 0 < k ∧ ∃ (b : Fin (d.m + 1) → ℕ), (∀ i, 0 < b i) ∧
      ∃ a : ℝ, 0 < a ∧ a < R ∧
        (∀ i, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i * (b i : ℝ) ≤
            (k : ℝ) * a) := by
  classical
  -- The column weights are fixed real numbers; the unit degree vector already
  -- works provided the power [k] is taken large enough.
  set w : Fin (d.m + 1) → ℝ := fun i =>
    InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) i with hw
  set C : ℝ := ∑ i, |w i| with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg (w i))
  have hwC : ∀ i, w i ≤ C := by
    intro i
    have h1 : w i ≤ |w i| := le_abs_self (w i)
    have h2 : |w i| ≤ C := by
      rw [hC]
      exact Finset.single_le_sum (f := fun j => |w j|)
        (fun j _ => abs_nonneg (w j)) (Finset.mem_univ i)
    linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * C / R)
  have hkpos : 0 < k := by
    have h0 : (0 : ℝ) ≤ 2 * C / R := by positivity
    have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_le_of_lt h0 hk
    exact_mod_cast hk0
  refine ⟨k, hkpos, fun _ => 1, ?_, R / 2, by linarith, by linarith, ?_⟩
  · intro i
    norm_num
  · intro i
    have hkR : C < (k : ℝ) * (R / 2) := by
      have h1 : (2 * C / R) * (R / 2) = C := by
        field_simp
      nlinarith [hk]
    have h1 : w i * ((1 : ℕ) : ℝ) = w i := by norm_num
    rw [h1]
    linarith [hwC i]
