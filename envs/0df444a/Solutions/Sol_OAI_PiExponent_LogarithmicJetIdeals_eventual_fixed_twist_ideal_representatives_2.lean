-- Prove2me | solution 2 for OAI.PiExponent.LogarithmicJetIdeals.eventual_fixed_twist_ideal_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:25:58.628251+00:00
-- url     : https://prove2.me/submissions/95dce102-8db9-4dd4-8ece-83db75da336a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventual_slack_bounded_representatives

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

/-- Reduction of the padded fixed-twist representative statement to the slack representative
statement: the extra ideal power `B` in the modulus is paid for by the slack `S - R` between the
representative scale `R` and the twist scale `S`. -/
theorem solution
    {nu : ℝ} (d : FixedData nu) :
    ∃ S : ℝ, 0 < S ∧
      ∃ T : Fin d.m → ℕ, ∃ e : Fin (d.m + 1) → ℕ,
        (∀ i, 0 < e i) ∧
        (∀ i, S ≤ (e i : ℝ) *
          InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
        (∀ i : Fin d.m,
          InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
              (T i : ℝ) * (d.v0 : ℝ)) ∧
        ∀ B : ℕ, ∃ M : ℕ, ∀ k : ℕ, M ≤ k →
          ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
            ∃ Q : WeightedPolynomial d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) ((k : ℝ) * S),
              P - Q.val ∈ (simultaneousJetIdeal d.K
                (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
                T e) ^ (k + B) := by
  obtain ⟨R, S, hR, hRS, T, e, he, heS, hT, N, hN⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.eventual_slack_bounded_representatives d
  refine ⟨S, lt_trans hR hRS, T, e, he, heS, hT, ?_⟩
  intro B
  have hSR : (0 : ℝ) < S - R := sub_pos.mpr hRS
  obtain ⟨M, hM⟩ := exists_nat_ge (max (N : ℝ) ((B : ℝ) * R / (S - R)))
  refine ⟨M, ?_⟩
  intro k hk P
  have hMk : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkN : (N : ℝ) ≤ (k : ℝ) := (le_trans (le_max_left _ _) hM).trans hMk
  have hkB : N ≤ k + B := by
    have hNk : N ≤ k := by exact_mod_cast hkN
    omega
  have hle : (B : ℝ) * R / (S - R) ≤ (k : ℝ) :=
    (le_trans (le_max_right _ _) hM).trans hMk
  have hkbound : ((k + B : ℕ) : ℝ) * R ≤ (k : ℝ) * S := by
    have h1 : (B : ℝ) * R ≤ (k : ℝ) * (S - R) := by
      have hmul := mul_le_mul_of_nonneg_right hle hSR.le
      have hdiv : (B : ℝ) * R / (S - R) * (S - R) = (B : ℝ) * R :=
        div_mul_cancel₀ _ (ne_of_gt hSR)
      rwa [hdiv] at hmul
    have h2 : ((k + B : ℕ) : ℝ) = (k : ℝ) + (B : ℝ) := by push_cast; ring
    rw [h2]
    nlinarith
  obtain ⟨Q, hQ⟩ := hN (k + B) hkB P
  refine ⟨⟨Q.val, ?_⟩, ?_⟩
  · intro a ha
    exact (Q.property a ha).trans hkbound
  · exact hQ
