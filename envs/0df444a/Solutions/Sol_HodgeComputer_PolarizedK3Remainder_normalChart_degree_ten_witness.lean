-- Prove2me | solution 1 for HodgeComputer.PolarizedK3Remainder.normalChart_degree_ten_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T01:51:22.319875+00:00
-- url     : https://prove2.me/submissions/d5dc7814-52b2-4bbc-bb7f-2a0a1f4cdda4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerPolarizedK3Remainder
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_DiamondCertificate
import Theorems.Thm_HodgeComputer_NormalChart_residue_eq_divergenceNumerator
import Theorems.Thm_HodgeComputer_NormalChart_directional_eq_source
import Theorems.Thm_HodgeComputer_PolarizedK3Remainder_normalChart_degree_ten_e2
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable section

open HodgeComputer HodgeComputer.PolarizedK3Remainder MvPolynomial

set_option allowUnsafeReducibility true
attribute [reducible] HodgeComputer.PolarizedK3Remainder.n

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous 10 ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous 11) ∧
      defect F A (NormalChart.denominator F S) 1 (NormalChart.numerator F A S W) = F ^ 2 * Q := by
  obtain ⟨S, W, Q, hSne, hShom, hFS, hWhom, hres⟩ :=
    HodgeComputer.PolarizedK3Remainder.normalChart_degree_ten_e2
  have hE1 : directional F (NormalChart.numerator F A S W)
      = A * (NormalChart.denominator F S) := by
    exact HodgeComputer.NormalChart.directional_eq_source F A S W
  have hdef : defect F A (NormalChart.denominator F S) 1 (NormalChart.numerator F A S W)
      = F * divergenceNumerator (NormalChart.denominator F S)
          (NormalChart.numerator F A S W) := by
    unfold defect
    rw [hE1]
    ring
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
