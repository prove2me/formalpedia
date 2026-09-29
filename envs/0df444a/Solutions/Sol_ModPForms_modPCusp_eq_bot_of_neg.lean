-- Prove2me | solution 1 for ModPForms.modPCusp_eq_bot_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1f605abb-3fa1-5624-bc4d-8a8a4a4d3432

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Theorems.Thm_CuspForm_qCoeffLinear_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_modPCusp_eq_bot_of_neg

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (N : ℕ) [NeZero N] (k : ℤ) (hk : k < 0) (F : Type) [Field F] :
    ModPForms.modPCusp N k F = ⊥ := by
  unfold ModPForms.modPCusp
  rw [Submodule.span_eq_bot]
  rintro φ ⟨f, a, ha, rfl⟩
  have hf : (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) = 0 := ModularForm.isZero_of_neg_weight hk _
  have hcoe : (f : UpperHalfPlane → ℂ) = 0 := by
    have := congrArg (fun g : ModularForm (CongruenceSubgroup.Gamma0 N) k => (g : UpperHalfPlane → ℂ)) hf
    simpa using this
  have h0 : ∀ n, ModularFormClass.qCoeff (f : UpperHalfPlane → ℂ) n = 0 := by
    intro n
    have e : (f : UpperHalfPlane → ℂ) = ((0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) : UpperHalfPlane → ℂ) := by
      rw [hcoe, CuspForm.coe_zero]
    rw [e, ← CuspForm.qCoeffLinear_apply, map_zero]
  have han : ∀ n, a n = 0 := fun n => by
    have h := ha n
    rw [h0 n] at h
    exact_mod_cast h.symm
  ext n
  simp [PowerSeries.coeff_mk, han]

end S_ModPForms_modPCusp_eq_bot_of_neg
end P2MW
export P2MW.S_ModPForms_modPCusp_eq_bot_of_neg (solution)
