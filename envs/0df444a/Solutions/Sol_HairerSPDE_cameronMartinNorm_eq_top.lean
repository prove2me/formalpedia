-- Prove2me | solution 1 for HairerSPDE.cameronMartinNorm_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T01:19:22.565165+00:00
-- url     : https://prove2.me/submissions/edff41f2-9a9a-4616-b1e8-0fe93b07476a

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

open HairerSPDE

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (hh : cameronMartinNorm μ h = ∞) :
    ∃ L : ℕ → StrongDual ℝ B,
      (∀ n, covarianceBilinDual μ (L n) (L n) ≤ 1) ∧ (∀ n, ((n : ℕ) : ℝ) ≤ (L n) h) := by
  have key : ∀ n : ℕ, ∃ L : StrongDual ℝ B,
      covarianceBilinDual μ L L ≤ 1 ∧ ((n : ℕ) : ℝ) ≤ L h := by
    intro n
    have hlt : ((n : ℝ≥0∞)) < ⨆ (L : {L : StrongDual ℝ B // covarianceBilinDual μ L L ≤ 1}),
        ENNReal.ofReal ((L : StrongDual ℝ B) h) := by
      rw [show (⨆ (L : {L : StrongDual ℝ B // covarianceBilinDual μ L L ≤ 1}),
            ENNReal.ofReal ((L : StrongDual ℝ B) h))
          = cameronMartinNorm μ h from rfl, hh]
      exact ENNReal.coe_lt_top
    obtain ⟨L, hL⟩ := lt_iSup_iff.mp hlt
    exact ⟨L.1, L.2, by
      have hlt' : ENNReal.ofReal ((n : ℝ)) < ENNReal.ofReal ((L.1 : StrongDual ℝ B) h) := by
        rwa [← ENNReal.ofReal_natCast n] at hL
      exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Nat.cast_nonneg n)).mp hlt')⟩
  choose L hL using key
  exact ⟨L, (fun n => (hL n).1), (fun n => (hL n).2)⟩
