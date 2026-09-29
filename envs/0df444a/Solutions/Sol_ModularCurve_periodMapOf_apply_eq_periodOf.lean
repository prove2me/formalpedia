-- Prove2me | solution 1 for ModularCurve.periodMapOf_apply_eq_periodOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7b55e655-acc1-5c11-92ed-d04fef14e499

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodMapOf_apply_eq_periodOf

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2) (γ : Γ) :
    ModularCurve.periodMapOf Γ f (Additive.ofMul γ) = ModularCurve.periodOf Γ γ f := by
  obtain ⟨F, hF⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf Γ f
  obtain ⟨F₀, h₀, hp⟩ := ModularCurve.periodMapOf_def Γ f hF
  rw [hp, ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply,
    ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf Γ f h₀ γ]
  rfl

end S_ModularCurve_periodMapOf_apply_eq_periodOf
end P2MW
export P2MW.S_ModularCurve_periodMapOf_apply_eq_periodOf (solution)
