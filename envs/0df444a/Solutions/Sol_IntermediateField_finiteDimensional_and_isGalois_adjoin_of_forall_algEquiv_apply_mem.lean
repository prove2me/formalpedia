-- Prove2me | solution 1 for IntermediateField.finiteDimensional_and_isGalois_adjoin_of_forall_algEquiv_apply_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/94e1b99f-5144-58fc-83ac-cc2739ea328a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_finiteDimensional_and_isGalois_adjoin_of_forall_algEquiv_apply_mem

set_option autoImplicit false

universe u v

theorem solution
    (K : Type u) [Field K] (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (S : Set Ω) (hS : S.Finite) (hsep : ∀ x ∈ S, IsSeparable K x)
    (hstab : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ S, σ x ∈ S) :
    FiniteDimensional K ↥(IntermediateField.adjoin K S) ∧ IsGalois K ↥(IntermediateField.adjoin K S) := by
  haveI : Finite ↑S := hS.to_subtype
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  have hfd : FiniteDimensional K ↥(IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (hsep x hx).isIntegral
  haveI : Algebra.IsSeparable K ↥(IntermediateField.adjoin K S) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable K Ω).mpr hsep
  haveI : Normal K ↥(IntermediateField.adjoin K S) := by
    rw [IntermediateField.normal_iff_forall_map_le']
    intro σ
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, hx, rfl⟩
    exact hstab σ x hx
  exact ⟨hfd, IsGalois.mk⟩

end S_IntermediateField_finiteDimensional_and_isGalois_adjoin_of_forall_algEquiv_apply_mem
end P2MW
export P2MW.S_IntermediateField_finiteDimensional_and_isGalois_adjoin_of_forall_algEquiv_apply_mem (solution)
