-- Prove2me | solution 1 for MazurTransfer.galois_fixedField_decomposition_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T12:22:17.677369+00:00
-- url     : https://prove2.me/submissions/898132d6-ed85-4c16-8773-f25b6d936622

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: Gal(L/E) is the SAME original decomposition subgroup,
where E is its original fixed field, preserving literal field evaluations.
Named downstream consumer: the actual local Picard point group at13. -/
import Theorems.Thm_ValuationSubring_mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField
import Mathlib

theorem solution (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (P : ValuationSubring L) :
    ∃ e : (L ≃ₐ[IntermediateField.fixedField (P.decompositionSubgroup K)] L) ≃*
        P.decompositionSubgroup K,
      ∀ (σ : L ≃ₐ[IntermediateField.fixedField (P.decompositionSubgroup K)] L) (x : L),
        (e σ).val x = σ x := by
  let toD : (L ≃ₐ[IntermediateField.fixedField (P.decompositionSubgroup K)] L) →*
      P.decompositionSubgroup K :=
    { toFun := fun σ => ⟨σ.restrictScalars K,
        ValuationSubring.mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField P
          (σ.restrictScalars K) (fun x _ hx => σ.commutes ⟨x, hx⟩)⟩
      map_one' := Subtype.ext (AlgEquiv.ext (fun _ => rfl))
      map_mul' := fun _ _ => Subtype.ext (AlgEquiv.ext (fun _ => rfl)) }
  let fromD (σ : P.decompositionSubgroup K) :
      L ≃ₐ[IntermediateField.fixedField (P.decompositionSubgroup K)] L :=
    { σ.val.toRingEquiv with
      commutes' := fun x => (IntermediateField.mem_fixedField_iff _ _).mp x.property σ.val σ.property }
  refine ⟨{ toFun := toD
            invFun := fromD
            left_inv := fun _ => AlgEquiv.ext (fun _ => rfl)
            right_inv := fun _ => Subtype.ext (AlgEquiv.ext (fun _ => rfl))
            map_mul' := toD.map_mul }, fun _ _ => rfl⟩

#print axioms solution
