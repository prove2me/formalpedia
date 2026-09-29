-- Prove2me | solution 1 for IntermediateField.cofinal_comp_fixingSubgroupEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e04fa25e-1186-57d2-a815-dd6bfe704c3d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_cofinal_comp_fixingSubgroupEquiv_symm

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem solution
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup) :
    (∀ E : IntermediateField L Ω, FiniteDimensional L E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ τ : Ω ≃ₐ[L] Ω,
          (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom)) τ
            ∈ F.fixingSubgroup → τ ∈ E.fixingSubgroup) ∧
    (∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField L Ω, FiniteDimensional L E ∧
        ∀ τ : Ω ≃ₐ[L] Ω, τ ∈ E.fixingSubgroup →
          (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom)) τ
            ∈ F.fixingSubgroup) := by
  classical

  have hj : ∀ (τ : Ω ≃ₐ[L] Ω) (x : Ω),
      ((L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) τ) x = τ x :=
    fun _ _ => rfl
  refine ⟨fun E hE => ?_, fun F hF => ?_⟩
  ·
    haveI := hE
    haveI : FiniteDimensional K (E.restrictScalars K) := by
      show FiniteDimensional K E
      exact FiniteDimensional.trans K L E
    obtain ⟨F, hF, h⟩ := hlevel (E.restrictScalars K) inferInstance
    refine ⟨F, hF, fun τ hτ => ?_⟩
    have hσ := h _ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    rw [← hj τ x]
    exact hσ x (by rwa [IntermediateField.mem_restrictScalars])
  ·
    obtain ⟨E₀, hE₀, h⟩ := hopen F hF
    haveI := hE₀
    haveI : FiniteDimensional K (L ⊔ E₀ : IntermediateField K Ω) := IntermediateField.finiteDimensional_sup L E₀
    have hK : Module.Finite K (IntermediateField.extendScalars (le_sup_left : L ≤ L ⊔ E₀)) := by
      change Module.Finite K (L ⊔ E₀ : IntermediateField K Ω)
      infer_instance
    refine ⟨IntermediateField.extendScalars (le_sup_left : L ≤ L ⊔ E₀),
      Module.Finite.of_restrictScalars_finite K L _, fun τ hτ => ?_⟩
    apply h
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
    intro x hx
    rw [hj]
    exact hτ x ((IntermediateField.mem_extendScalars _).2 ((le_sup_right : E₀ ≤ L ⊔ E₀) hx))

end S_IntermediateField_cofinal_comp_fixingSubgroupEquiv_symm
end P2MW
export P2MW.S_IntermediateField_cofinal_comp_fixingSubgroupEquiv_symm (solution)
