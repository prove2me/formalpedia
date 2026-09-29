-- Prove2me | solution 1 for ModularForm.exists_coe_eq_of_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e3fefdb9-2f2f-5591-a384-7435bef2e8cf

import Mathlib
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_coe_eq_of_levelOne

open UpperHalfPlane
open scoped MatrixGroups

theorem solution (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ∃ G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := by
  have hle : ((Γ : Subgroup (GL (Fin 2) ℝ))) ≤ 𝒮ℒ := by
    rintro _ ⟨γ, -, rfl⟩
    exact ⟨γ, rfl⟩
  refine ⟨{ toFun := F
            slash_action_eq' := fun γ hγ => F.slash_action_eq' γ (hle hγ)
            holo' := F.holo'
            bdd_at_cusps' := fun hc => F.bdd_at_cusps' (hc.mono hle) }, rfl⟩

#print axioms solution

end S_ModularForm_exists_coe_eq_of_levelOne
end P2MW
export P2MW.S_ModularForm_exists_coe_eq_of_levelOne (solution)
