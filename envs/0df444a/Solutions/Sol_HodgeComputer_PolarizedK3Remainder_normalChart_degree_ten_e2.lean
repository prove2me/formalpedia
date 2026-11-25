-- Prove2me | solution 1 for HodgeComputer.PolarizedK3Remainder.normalChart_degree_ten_e2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T02:55:26.845815+00:00
-- url     : https://prove2.me/submissions/638b1722-e829-4126-bea8-5b2b8fd69086
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerPolarizedK3Remainder
import Definitions.Def_HodgeComputerNormalChart
import Theorems.Thm_HodgeComputer_PolarizedK3Remainder_normalChart_X0_pow_ten_legal
import Theorems.Thm_HodgeComputer_PolarizedK3Remainder_normalChart_X0_pow_ten_e2

set_option autoImplicit false
noncomputable section

open HodgeComputer HodgeComputer.PolarizedK3Remainder MvPolynomial

/-- CycleQ2-style wormhole: legality of \(S=X_0^{10}\) plus the Koszul/\(E_2\) linear system
at that fixed denominator. -/
theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous 10 ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous 11) ∧
      NormalChart.residue F A S W = F * Q := by
  let S : AmbientPoly n := (X (R := ℂ) (0 : Fin 6)) ^ (10 : ℕ)
  have hlegal := HodgeComputer.PolarizedK3Remainder.normalChart_X0_pow_ten_legal
  obtain ⟨W, Q, hWhom, hres⟩ :=
    HodgeComputer.PolarizedK3Remainder.normalChart_X0_pow_ten_e2
  exact ⟨S, W, Q, hlegal.1, hlegal.2.1, hlegal.2.2, hWhom, hres⟩
