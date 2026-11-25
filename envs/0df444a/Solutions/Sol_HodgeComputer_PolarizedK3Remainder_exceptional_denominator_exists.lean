-- Prove2me | solution 1 for HodgeComputer.PolarizedK3Remainder.exceptional_denominator_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T01:51:25.090819+00:00
-- url     : https://prove2.me/submissions/1f813c1f-82ff-40d6-8c14-c36f6d05b977
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerPolarizedK3Remainder
import Definitions.Def_HodgeComputerNormalChart
import Theorems.Thm_HodgeComputer_PolarizedK3Remainder_normalChart_degree_ten_e2

set_option autoImplicit false
noncomputable section

open HodgeComputer HodgeComputer.PolarizedK3Remainder MvPolynomial

theorem solution :
    ∃ (e : ℕ) (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      0 < e ∧ S ≠ 0 ∧ S.IsHomogeneous e ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (e + 1)) ∧
      NormalChart.residue F A S W = F * Q := by
  obtain ⟨S, W, Q, hSne, hShom, hFS, hWhom, hres⟩ :=
    HodgeComputer.PolarizedK3Remainder.normalChart_degree_ten_e2
  refine ⟨10, S, W, Q, ?_, hSne, hShom, hFS, hWhom, hres⟩
  norm_num
