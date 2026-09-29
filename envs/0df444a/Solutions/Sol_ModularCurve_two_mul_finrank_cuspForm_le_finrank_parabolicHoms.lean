-- Prove2me | solution 1 for ModularCurve.two_mul_finrank_cuspForm_le_finrank_parabolicHoms
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/81213452-7ece-5ea5-83a4-f2d5a95af596

import Mathlib
import Definitions.Def_ModularCurve_PeriodHomPair
import Theorems.Thm_ModularCurve_periodHomPair_injective
import Theorems.Thm_ModularCurve_range_periodHomPair_le_parabolicHoms
import Theorems.Thm_ModularCurve_Period_moduleFinite_addMonoidHom_gamma0_complex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_two_mul_finrank_cuspForm_le_finrank_parabolicHoms

set_option autoImplicit false
open CongruenceSubgroup ModularCurve ModularCurve.Period
open scoped MatrixGroups

theorem solution (N : ℕ) [NeZero N] :
    2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)
      ≤ Module.finrank ℂ ↥(ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ) := by
  haveI := ModularCurve.Period.moduleFinite_addMonoidHom_gamma0_complex N
  haveI : Module.Finite ℂ (CuspForm (Gamma0 N) 2 × CuspForm (Gamma0 N) 2) :=
    Module.Finite.of_injective (periodHomPair N) (periodHomPair_injective N)
  haveI : Module.Finite ℂ (CuspForm (Gamma0 N) 2) :=
    Module.Finite.of_injective (LinearMap.inl ℂ (CuspForm (Gamma0 N) 2) (CuspForm (Gamma0 N) 2)) LinearMap.inl_injective
  have hle := ModularCurve.range_periodHomPair_le_parabolicHoms N
  have hφ : Function.Injective ((periodHomPair N).codRestrict (parabolicHoms ℂ (Gamma0 N) ℂ)
      (fun x => hle ⟨x, rfl⟩)) := by
    intro x y h
    exact periodHomPair_injective N (congrArg Subtype.val h)
  calc 2 * Module.finrank ℂ (CuspForm (Gamma0 N) 2)
      = Module.finrank ℂ (CuspForm (Gamma0 N) 2 × CuspForm (Gamma0 N) 2) := by
        rw [Module.finrank_prod, two_mul]
    _ ≤ Module.finrank ℂ ↥(parabolicHoms ℂ (Gamma0 N) ℂ) := LinearMap.finrank_le_finrank_of_injective hφ

end S_ModularCurve_two_mul_finrank_cuspForm_le_finrank_parabolicHoms
end P2MW
export P2MW.S_ModularCurve_two_mul_finrank_cuspForm_le_finrank_parabolicHoms (solution)
