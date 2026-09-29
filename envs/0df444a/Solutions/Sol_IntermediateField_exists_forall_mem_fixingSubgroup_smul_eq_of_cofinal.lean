-- Prove2me | solution 1 for IntermediateField.exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4da052ca-22dd-5437-af2c-fad9a6ded48c

import Mathlib
import Theorems.Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal

set_option autoImplicit false

universe u v

open IntermediateField

theorem solution
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hcof : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (x : Ωˣ) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ • x = x := by
  obtain ⟨E, hE, h⟩ := exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq (K := K) x
  obtain ⟨F, hF, hFE⟩ := hcof E hE
  exact ⟨F, hF, fun σ hσ => h σ (hFE σ hσ)⟩

end S_IntermediateField_exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal
end P2MW
export P2MW.S_IntermediateField_exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal (solution)
