-- Prove2me | solution 1 for N25.Endgame.coe_qExpFrobeniusModL_pow25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:48.299967+00:00
-- url     : https://prove2.me/submissions/b3310511-c97f-4c4d-a3b6-7ee03a2983ca

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence

/-! Iterates of the prime q-expansion Frobenius on functions and places. -/
noncomputable section

namespace N25.Endgame

/-- Iteration on the modular field agrees with iteration on its Laurent expansions. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    (n : ℕ) (x : ModularCurve.qExpFunctionFieldC K Γ25) :
    ((ModularCurve.qExpFrobeniusModL K Γ25 p ^ n) x : LaurentSeries K) =
      (ModularCurve.qExpand K p ^ n) (x : LaurentSeries K) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', AlgHom.mul_apply, RingHom.coe_mul, Function.comp_apply,
      ModularCurve.coe_qExpFrobeniusModL, ih]

end N25.Endgame
