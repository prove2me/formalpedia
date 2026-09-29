-- Prove2me | solution 1 for ModularCurve.Period.moduleFinite_addMonoidHom_gamma0_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/959174f7-9758-51df-a8b0-942030e2c7c9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_Period_moduleFinite_addMonoidHom_gamma0_complex

set_option autoImplicit false
open CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.Period.fg_gamma0 (N : ℕ) [NeZero N] : Group.FG (Gamma0 N) := by
  classical
  haveI : Group.FG SL(2, ℤ) := ⟨⟨{ModularGroup.S, ModularGroup.T}, by
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact SpecialLinearGroup.SL2Z_generators⟩⟩
  exact Subgroup.fg_of_index_ne_zero _

theorem solution (N : ℕ) [NeZero N] :
    Module.Finite ℂ (Additive (CongruenceSubgroup.Gamma0 N) →+ ℂ) := by
  classical
  obtain ⟨s, hs⟩ := (ModularCurve.Period.fg_gamma0 N).out
  let ev : (Additive (Gamma0 N) →+ ℂ) →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun φ i => φ (Additive.ofMul (i : Gamma0 N))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective ev ?_
  intro φ ψ h
  have key : ∀ γ : Gamma0 N, φ (Additive.ofMul γ) = ψ (Additive.ofMul γ) := by
    intro γ
    have hγ : γ ∈ Subgroup.closure (s : Set (Gamma0 N)) := by rw [hs]; exact Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem x hx => exact congrFun h ⟨x, hx⟩
    | one => rw [ofMul_one, map_zero, map_zero]
    | mul x y _ _ hx hy => rw [ofMul_mul, map_add, map_add, hx, hy]
    | inv x _ hx => rw [ofMul_inv, map_neg, map_neg, hx]
  exact AddMonoidHom.ext fun a => key (Additive.toMul a)

end S_ModularCurve_Period_moduleFinite_addMonoidHom_gamma0_complex
end P2MW
export P2MW.S_ModularCurve_Period_moduleFinite_addMonoidHom_gamma0_complex (solution)
