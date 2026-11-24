-- Prove2me | solution 1 for HodgeComputer.RankOneBiquartic.certificate_defect
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T13:35:19.813277+00:00
-- url     : https://prove2.me/submissions/59949f9e-b7fc-47bf-b44a-860c7e83b9d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerRankOneBiquartic
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_DiamondCertificate
import Theorems.Thm_HodgeComputer_RankOneBiquartic_normalChart_degree_ten_witness
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false
noncomputable section

open HodgeComputer HodgeComputer.RankOneBiquartic MvPolynomial

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 1)) ∧
      defect F A (NormalChart.denominator F S) 1 (NormalChart.numerator F A S W) = F ^ 2 * Q := by
  obtain ⟨S, W, Q, hSne, hShom10, hFS, hWhom11, hcert⟩ :=
    HodgeComputer.RankOneBiquartic.normalChart_degree_ten_witness
  -- A nonzero homogeneous polynomial of degree ten has total degree ten.
  have hdeg : S.totalDegree = 10 := hShom10.totalDegree hSne
  refine ⟨S, W, Q, hSne, ?_, hFS, ?_, hcert⟩
  · rw [hdeg]
    exact hShom10
  · intro j
    rw [hdeg]
    simpa using hWhom11 j
