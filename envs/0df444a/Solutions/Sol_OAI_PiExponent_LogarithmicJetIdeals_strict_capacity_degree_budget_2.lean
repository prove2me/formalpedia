-- Prove2me | solution 2 for OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_degree_budget
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:42:20.072413+00:00
-- url     : https://prove2.me/submissions/90bb2c1d-d085-439e-a4db-342742764b82

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

/-- The strict-capacity degree budget is satisfiable for purely arithmetic reasons: positive
integer degrees can always be paid for by a sufficiently large common multiple `k`, no matter
how small the strict scale `R` is relative to the column weights. -/
theorem solution {nu : ℝ} (d : FixedData nu) (R S : ℝ)
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
    ∃ k : ℕ, 0 < k ∧ ∃ b : Fin (d.m + 1) → ℕ, (∀ i, 0 < b i) ∧
      ∃ a : ℝ, 0 < a ∧ a < R ∧
        (∀ i, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i * (b i : ℝ) ≤
            (k : ℝ) * a) := by
  classical
  set W : Fin (d.m + 1) → ℝ := fun i =>
    InterpolationMatrix.columnWeights d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) i
  set M : ℝ := 1 + ∑ i, |W i|
  have hR2 : (0 : ℝ) < R / 2 := by linarith
  refine ⟨⌈2 * M / R⌉₊ + 1, by omega, fun _ => 1, fun i => one_pos, R / 2, hR2,
    by linarith, ?_⟩
  intro i
  have h1 : W i ≤ |W i| := le_abs_self _
  have h2 : |W i| ≤ ∑ j, |W j| :=
    Finset.single_le_sum (f := fun j => |W j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hsum : (0 : ℝ) ≤ ∑ j, |W j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hceil : 2 * M / R ≤ ((⌈2 * M / R⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hk : 2 * M / R ≤ ((⌈2 * M / R⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hmul : M ≤ ((⌈2 * M / R⌉₊ + 1 : ℕ) : ℝ) * (R / 2) := by
    have hstep := mul_le_mul_of_nonneg_right hk (le_of_lt hR2)
    have hsimp : 2 * M / R * (R / 2) = M := by
      field_simp
    linarith [hsimp ▸ hstep]
  calc W i * ((fun _ => 1 : Fin (d.m + 1) → ℕ) i : ℝ) = W i := by simp
    _ ≤ |W i| := h1
    _ ≤ ∑ j, |W j| := h2
    _ ≤ M := by linarith
    _ ≤ ((⌈2 * M / R⌉₊ + 1 : ℕ) : ℝ) * (R / 2) := hmul
