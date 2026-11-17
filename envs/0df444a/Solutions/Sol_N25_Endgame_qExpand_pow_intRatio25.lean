-- Prove2me | solution 1 for N25.Endgame.qExpand_pow_intRatio25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:23.750137+00:00
-- url     : https://prove2.me/submissions/75db75b4-b7c3-42c1-b3f5-1820608d60dc

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

/-! The power law for iterated q-expansion Frobenius over a finite coefficient field. -/
noncomputable section

namespace N25.Endgame

/-- Integral-form ratios are sent to their prime-power powers by every Frobenius iterate. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    (n : ℕ) (a b : PowerSeries ℤ) :
    (ModularCurve.qExpand K p ^ n)
        (ModularCurve.intSeriesC K a / ModularCurve.intSeriesC K b) =
      (ModularCurve.intSeriesC K a / ModularCurve.intSeriesC K b) ^ (p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih, map_pow, map_div₀,
      ModularCurve.qExpand_intSeriesC_eq_pow, ModularCurve.qExpand_intSeriesC_eq_pow,
      ← div_pow, ← pow_mul, pow_succ']

end N25.Endgame
