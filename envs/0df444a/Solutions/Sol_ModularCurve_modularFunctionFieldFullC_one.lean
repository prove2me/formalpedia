-- Prove2me | solution 1 for ModularCurve.modularFunctionFieldFullC_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f9364338-e1fb-5df6-89d6-5cd85c30be5a

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularFunctionFieldFullC_one

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_modularFunctionFieldFullC_one.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "divisorExpansionsC modularFunctionFieldFullC jqModC modularFunctionFieldC modularFunctionFieldC_one qExpand_one_apply" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.solution_aux_divisorExpansionsC_one (K : Type*) [Field K] :
    divisorExpansionsC K 1 = {jqModC K} := by
  ext x
  simp only [divisorExpansionsC, Set.mem_setOf_eq, Set.mem_singleton_iff, Nat.dvd_one]
  constructor
  · rintro ⟨d, hd, rfl, rfl⟩
    exact qExpand_one_apply _
  · rintro rfl
    exact ⟨1, inferInstance, rfl, (qExpand_one_apply _).symm⟩

theorem solution (K : Type*) [Field K] :
    modularFunctionFieldFullC K 1 = modularFunctionFieldC K 1 := by
  rw [modularFunctionFieldFullC, ModularCurve.solution_aux_divisorExpansionsC_one, modularFunctionFieldC_one]

end S_ModularCurve_modularFunctionFieldFullC_one
end P2MW
export P2MW.S_ModularCurve_modularFunctionFieldFullC_one (solution)
