-- Prove2me | solution 1 for ModularCurve.FullLevel.qExpand_mem_laurentBaseChange_xHFunctionField_levelH_of_mem_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/28e73f69-2498-57bc-98a3-4521ef9684dc

import Theorems.Thm_ModularCurve_qExpand_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_qExpand_mem_xHFunctionField_of_mem_div
import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_qExpand_mem_laurentBaseChange_xHFunctionField_levelH_of_mem_gamma0

set_option autoImplicit false

set_option maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (x : LaurentSeries L)
    (hx : x ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) :
    ModularCurve.qExpand L q x ∈
      ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) := by
  haveI hqne : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  have hpM : q ∣ q ^ 2 * M' := ⟨q * M', by ring⟩
  have hdiv : q ^ 2 * M' / q = q * M' := by
    rw [show q ^ 2 * M' = q * (q * M') by ring, Nat.mul_div_cancel_left _ hqpos]

  have hle : CohCarrier.GammaH (q ^ 2 * M' / q) (ModularCurve.infSubgroup q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') hpM) ≤
      CongruenceSubgroup.Gamma0 M' := by
    refine (CohCarrier.GammaH_le_Gamma0 _).trans ?_
    intro γ hγ
    rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
    rw [hdiv] at hγ
    exact dvd_trans ⟨q, by push_cast; ring⟩ hγ
  refine ModularCurve.qExpand_mem_laurentBaseChange q (fun y hy => ?_) hx
  have hy' : y ∈ ModularCurve.xHFunctionField (q ^ 2 * M' / q)
      (ModularCurve.infSubgroup q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') hpM) := by
    show y ∈ ModularCurve.qExpFunctionFieldC ℚ _
    exact ModularCurve.qExpFunctionFieldC_mono ℚ hle hy
  exact ModularCurve.qExpand_mem_xHFunctionField_of_mem_div q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') hpM hy'

end S_ModularCurve_FullLevel_qExpand_mem_laurentBaseChange_xHFunctionField_levelH_of_mem_gamma0
end P2MW
export P2MW.S_ModularCurve_FullLevel_qExpand_mem_laurentBaseChange_xHFunctionField_levelH_of_mem_gamma0 (solution)
