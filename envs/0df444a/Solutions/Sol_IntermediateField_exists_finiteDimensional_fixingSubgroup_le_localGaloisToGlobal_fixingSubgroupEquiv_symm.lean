-- Prove2me | solution 1 for IntermediateField.exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d4bdf868-6b81-543f-8e92-cae26ace6e15

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_localGaloisToGlobal_mem_fixingSubgroup_iff
import Theorems.Thm_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm

set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory

open IntermediateField in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
      ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup →
        ((localGaloisToGlobal q).comp
        (K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)) σ ∈ F.fixingSubgroup := by
  classical
  let Ω := PadicAlgCl q
  let ι : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[ℚ_[q]] Ω) :=
    K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom
  have hι : ∀ (σ : Ω ≃ₐ[K] Ω) (x : Ω), ι σ x = σ x := fun _ _ => rfl
  let KF : IntermediateField ℚ_[q] Ω := IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ)))
  haveI : FiniteDimensional ℚ_[q] KF := IntermediateField.finiteDimensional_adjoin_padicEmbedding_image q F
  haveI : FiniteDimensional ℚ_[q] (K ⊔ KF : IntermediateField ℚ_[q] Ω) := IntermediateField.finiteDimensional_sup K KF
  let E : IntermediateField K Ω := IntermediateField.extendScalars (le_sup_left : K ≤ K ⊔ KF)
  haveI : FiniteDimensional K E := by
    haveI : FiniteDimensional ℚ_[q] E := ‹FiniteDimensional ℚ_[q] (K ⊔ KF : IntermediateField ℚ_[q] Ω)›
    exact Module.Finite.of_restrictScalars_finite ℚ_[q] K E
  refine ⟨E, inferInstance, fun σ hσ => ?_⟩
  show localGaloisToGlobal q (ι σ) ∈ F.fixingSubgroup
  rw [localGaloisToGlobal_mem_fixingSubgroup_iff]
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  rw [hι]
  exact hσ x ((IntermediateField.mem_extendScalars (le_sup_left : K ≤ K ⊔ KF)).2 (le_sup_right (a := K) hx))

end S_IntermediateField_exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm
end P2MW
export P2MW.S_IntermediateField_exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm (solution)
