-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.toricPts_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c4213652-ee77-5e1f-b61f-b2736a3dd5e8

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_toricPts_of_pos

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem solution
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (hm : 0 < m) :
    O.toricPts m = AddSubgroup.closure (Set.range (O.toricPoint m hm)) := by
  rw [toricPts, dif_pos hm]

end S_ModularCurve_JZeroNeronObjectAtP_toricPts_of_pos
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_toricPts_of_pos (solution)
