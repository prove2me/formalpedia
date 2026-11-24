-- Prove2me | solution 1 for HodgeComputer.RankOneBiquartic.normalChart_residue_solvable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T12:03:21.761576+00:00
-- url     : https://prove2.me/submissions/02dad3c6-5a83-4a9b-9f3d-fcc8291ef4ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerRankOneBiquartic
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_DiamondCertificate
import Theorems.Thm_HodgeComputer_NormalChart_residue_eq_divergenceNumerator
import Theorems.Thm_HodgeComputer_NormalChart_directional_eq_source
import Theorems.Thm_HodgeComputer_RankOneBiquartic_F_ne_zero
import Theorems.Thm_HodgeComputer_RankOneBiquartic_certificate_defect
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable section

open HodgeComputer HodgeComputer.RankOneBiquartic MvPolynomial

-- The ambient dimension of the rank-one biquartic instance is the literal `5`.
-- Making `n` reducible lets the ambient polynomial type be handled uniformly
-- across the ambient dimension and the chart dimension.
set_option allowUnsafeReducibility true
attribute [reducible] HodgeComputer.RankOneBiquartic.n

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 1)) ∧
      NormalChart.residue F A S W = F * Q := by
  obtain ⟨S, W, Q, hSne, hShom, hFS, hWhom, hcert⟩ :=
    HodgeComputer.RankOneBiquartic.certificate_defect
  refine ⟨S, W, Q, hSne, hShom, hFS, hWhom, ?_⟩
  -- The first normalized equation of the chart is an identity: the directional
  -- derivative of the numerator is the source times the denominator.
  have hE1 : directional F (NormalChart.numerator F A S W)
      = A * (NormalChart.denominator F S) := by
    exact HodgeComputer.NormalChart.directional_eq_source F A S W
  -- Hence the cleared defect collapses to `F` times the cleared divergence defect.
  have hdef : defect F A (NormalChart.denominator F S) 1 (NormalChart.numerator F A S W)
      = F * divergenceNumerator (NormalChart.denominator F S)
          (NormalChart.numerator F A S W) := by
    unfold defect
    rw [hE1]
    ring
  -- The certificate gives `F * divergence = F * (F * Q)`.
  have h1 : F * divergenceNumerator (NormalChart.denominator F S)
          (NormalChart.numerator F A S W) = F * (F * Q) := by
    rw [← hdef]
    calc defect F A (NormalChart.denominator F S) 1 (NormalChart.numerator F A S W)
        = F ^ 2 * Q := hcert
      _ = F * (F * Q) := by rw [pow_two]; ring
  -- Cancelling the nonzero `F` yields the divergence identity.
  have hz : F * (divergenceNumerator (NormalChart.denominator F S)
          (NormalChart.numerator F A S W) - F * Q) = 0 := by
    calc F * (divergenceNumerator (NormalChart.denominator F S)
            (NormalChart.numerator F A S W) - F * Q)
        = F * divergenceNumerator (NormalChart.denominator F S)
              (NormalChart.numerator F A S W) - F * (F * Q) := by ring
      _ = 0 := sub_eq_zero.mpr h1
  have hdiv : divergenceNumerator (NormalChart.denominator F S)
          (NormalChart.numerator F A S W) = F * Q := by
    rcases mul_eq_zero.mp hz with hF0 | hrest
    · exact absurd hF0 HodgeComputer.RankOneBiquartic.F_ne_zero
    · exact sub_eq_zero.mp hrest
  -- Bridge back to the normal-chart residue.
  exact (HodgeComputer.NormalChart.residue_eq_divergenceNumerator F A S W).trans hdiv
