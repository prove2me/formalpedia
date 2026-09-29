-- Prove2me | solution 1 for IntermediateField.exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/19ece520-75bd-5119-99a4-f802de815a9f

import Mathlib
import Theorems.Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq

set_option autoImplicit false

universe u v

open IntermediateField

theorem solution
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Ωˣ) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ • x = x := by
  obtain ⟨E, hE, h⟩ := exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq (K := K) (x : Ω)
  exact ⟨E, hE, fun σ hσ => Units.ext (h σ hσ)⟩

end S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq
end P2MW
export P2MW.S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq (solution)
