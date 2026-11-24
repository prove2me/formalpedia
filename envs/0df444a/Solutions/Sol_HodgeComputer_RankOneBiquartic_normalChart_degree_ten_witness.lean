-- Prove2me | solution 1 for HodgeComputer.RankOneBiquartic.normalChart_degree_ten_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T13:35:21.125018+00:00
-- url     : https://prove2.me/submissions/9672cd07-ed88-48bf-9bbc-5e393215fae8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerRankOneBiquartic
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_DiamondCertificate
import Theorems.Thm_HodgeComputer_NormalChart_residue_eq_divergenceNumerator
import Theorems.Thm_HodgeComputer_NormalChart_directional_eq_source
import Theorems.Thm_HodgeComputer_RankOneBiquartic_normalChart_degree_ten_e2
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
      S ≠ 0 ∧ S.IsHomogeneous 10 ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous 11) ∧
      defect F A (NormalChart.denominator F S) 1 (NormalChart.numerator F A S W) = F ^ 2 * Q := by
  obtain ⟨S, W, Q, hSne, hShom, hFS, hWhom, hres⟩ :=
    HodgeComputer.RankOneBiquartic.normalChart_degree_ten_e2
  -- The first normalized equation of the chart is an identity.
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
  -- The residue is the cleared divergence defect.
  have hres2 : NormalChart.residue F A S W
      = divergenceNumerator (NormalChart.denominator F S) (NormalChart.numerator F A S W) :=
    HodgeComputer.NormalChart.residue_eq_divergenceNumerator F A S W
  have hdiv : divergenceNumerator (NormalChart.denominator F S)
      (NormalChart.numerator F A S W) = F * Q := by
    rw [← hres2]
    exact hres
  refine ⟨S, W, Q, hSne, hShom, hFS, hWhom, ?_⟩
  calc defect F A (NormalChart.denominator F S) 1 (NormalChart.numerator F A S W)
      = F * divergenceNumerator (NormalChart.denominator F S)
          (NormalChart.numerator F A S W) := hdef
    _ = F * (F * Q) := by rw [hdiv]
    _ = F ^ 2 * Q := by rw [pow_two]; ring
