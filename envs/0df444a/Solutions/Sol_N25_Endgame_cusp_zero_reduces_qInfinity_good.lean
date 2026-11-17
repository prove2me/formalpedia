-- Prove2me | solution 1 for N25.Endgame.cusp_zero_reduces_qInfinity_good
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:03.797356+00:00
-- url     : https://prove2.me/submissions/60f416ac-10f8-404d-be69-0f2bd8e8c6b9

import Mathlib
import Theorems.Thm_N25_U25C_eq_mk
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_CuspReduction
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_U25_orders_special_good
import Definitions.Def_N25_UnitOrders
import Theorems.Thm_N25_unitSeries25_order
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

namespace N25.Endgame

/-- The unique order-minus-one entry of the second unit identifies the reduced q-cusp. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) (D : RedDatum25 p) :
    redPlace25 D (pG25 0) =
      ModularCurve.qInftyPlaceMod (κ D.A) (jBase25 (κ D.A)).property := by
  classical
  let : Algebra (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
    (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25).algebra
  let Q : SpecialPlace D.A :=
    ModularCurve.qInftyPlaceMod (κ D.A) (jBase25 (κ D.A)).property
  have horder : Q.ord (N25.U25C (κ D.A) 1) = -1 := by
    dsimp only [Q, jBase25]
    rw [ModularCurve.ord_qInftyPlaceMod, N25.U25C_eq_mk]
    exact N25.unitSeries25_order (κ D.A) 1
  obtain ⟨htable, hother⟩ := U25_orders_special_good p hp D 1
  have hex : ∃ j : Fin 5, Q = redPlace25 D (pG25 j) := by
    by_contra h
    have hz := hother Q (fun j hj => h ⟨j, hj⟩)
    omega
  obtain ⟨j, hj⟩ := hex
  have hval := htable j
  rw [← hj, horder] at hval
  have hjzero : j = 0 := by
    fin_cases j <;> first | rfl | norm_num [N25.unitOrders25] at hval
  simpa only [hjzero] using hj.symm

end N25.Endgame
