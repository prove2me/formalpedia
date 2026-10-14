-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.eventual_fixed_twist_ideal_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T17:41:06.636828+00:00
-- url     : https://prove2.me/submissions/ca0dc02b-0cf1-467c-8b08-8daae6cbd116
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventual_slack_bounded_representatives
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_fixed_overhead_from_slack

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution {nu : ℝ} (d : FixedData nu) :
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
  obtain ⟨R, S, hR, hRS, T, e, he, hscale, hT, N, hrep⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.eventual_slack_bounded_representatives d
  refine ⟨S, lt_trans hR hRS, T, e, he, hscale, hT, ?_⟩
  exact OAI.PiExponent.LogarithmicJetIdeals.fixed_overhead_from_slack
    d R S T e N hR hRS hrep
