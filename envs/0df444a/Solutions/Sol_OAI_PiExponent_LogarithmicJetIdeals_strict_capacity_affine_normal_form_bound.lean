-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_affine_normal_form_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:16:47.948337+00:00
-- url     : https://prove2.me/submissions/bbf24a55-ccc5-426c-9067-9964be6aac63
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_affine_normal_forms_of_initial_powers
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_initial_power_certificate

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
    ∃ ρ B : ℝ, 0 < ρ ∧ ρ < R ∧ 0 ≤ B ∧
      ∀ k : ℕ, ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
        ∃ Q : MvPolynomial (Fin (d.m + 1)) ℂ,
          (∀ u ∈ Q.support,
            (∑ i, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i *
              (u i : ℝ)) ≤ (k : ℝ) * ρ + B) ∧
          P - Q ∈ (simultaneousJetIdeal d.K
            (MatrixArithmetic.rationalCenters (finiteNumerators d)
              (finiteDenominators d)) T e) ^ k := by
  obtain ⟨ρ, a, N, o, f, hρ, hρR, ha, hN, hmem, hlc, hdeg, hbudget⟩ :=
    strict_capacity_initial_power_certificate.{0} d R S e T
      hR hRS he hcommon hcapacity hT
  let w : Fin (d.m + 1) → ℝ :=
    InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d))
  let J : Ideal (MvPolynomial (Fin (d.m + 1)) ℂ) :=
    simultaneousJetIdeal d.K
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d)) T e
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 ≤ (d.w0 : ℝ)
      exact le_of_lt d.w0_pos
    · change 0 ≤ (⌈Real.log (finiteDenominators d j)⌉₊ : ℝ)
      exact Nat.cast_nonneg _
  let B : ℝ := ∑ i, w i * ((N i - 1 : ℕ) : ℝ)
  refine ⟨ρ, B, hρ, hρR, ?_, ?_⟩
  · dsimp only [B]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Nat.cast_nonneg _))
  · simpa only [w, J, B] using
      (affine_normal_forms_of_initial_powers J w ρ o (fun _ => a) N f
        hw (le_of_lt hρ) (fun _ => ha) hN hmem hlc hdeg hbudget)
