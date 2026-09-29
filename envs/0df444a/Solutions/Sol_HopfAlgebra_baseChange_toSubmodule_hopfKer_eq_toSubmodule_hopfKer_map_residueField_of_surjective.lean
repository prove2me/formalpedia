-- Prove2me | solution 1 for HopfAlgebra.baseChange_toSubmodule_hopfKer_eq_toSubmodule_hopfKer_map_residueField_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d12738ba-ef55-543d-9444-a3ee0ced1087

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_baseChange_toSubmodule_hopfKer_eq_toSubmodule_hopfKer_map_residueField_of_surjective

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open HopfAlgebra

namespace HOPFKERBC

section BaseChange

variable {R : Type} [CommRing R] [IsLocalRing R]
  {A C : Type} [CommRing A] [CommRing C]
  [HopfAlgebra R A] [HopfAlgebra R C]
  [Module.Finite R A] [Module.Free R A] [Module.Finite R C] [Module.Free R C]
  (π : A →ₐc[R] C) (hπ : Function.Surjective π)

local notation "k" => IsLocalRing.ResidueField R

def bc : k ⊗[R] A →ₐc[k] k ⊗[R] C := Bialgebra.TensorProduct.map (BialgHom.id k k) π

omit [Module.Finite R A] [Module.Free R A] [Module.Finite R C]
  [Module.Free R C] in
@[scoped simp] theorem bc_tmul (s : k) (a : A) : bc π (s ⊗ₜ[R] a) = s ⊗ₜ[R] π a := rfl

include hπ in
omit [Module.Finite R A] [Module.Free R A] [Module.Finite R C] [Module.Free R C] in
theorem bc_surjective : Function.Surjective (bc π) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s c =>
      obtain ⟨a, rfl⟩ := hπ c
      exact ⟨s ⊗ₜ[R] a, rfl⟩
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩

include hπ in

theorem finrank_hopfKer_mul [Module.Free R ↥(hopfKer π)] :
    Module.finrank R ↥(hopfKer π) * Module.finrank R C = Module.finrank R A := by
  obtain ⟨-, -, -, hrank⟩ := HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  have h := hrank (IsLocalRing.closedPoint R)
  rwa [Module.rankAtStalk_eq_finrank_of_free] at h

include hπ in

theorem finrank_hopfKer_bc_mul :
    Module.finrank k ↥(hopfKer (bc π)) * Module.finrank R C = Module.finrank R A := by
  obtain ⟨-, -, -, hrank⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective (bc π) (bc_surjective π hπ)
  have h := hrank ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_baseChange, Module.finrank_baseChange] at h
  exact h

omit [Module.Finite R A] [Module.Free R A] [Module.Finite R C] [Module.Free R C] in

theorem one_tmul_mem_hopfKer_bc {a : A} (ha : a ∈ hopfKer π) : (1 : k) ⊗ₜ[R] a ∈ hopfKer (bc π) := by
  rw [HopfAlgebra.mem_hopfKer_iff] at ha ⊢

  let θ : A ⊗[R] C →ₗ[R] (k ⊗[R] A) ⊗[k] (k ⊗[R] C) :=
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R k R k k k A C).toLinearMap.restrictScalars R ∘ₗ
      (TensorProduct.mk R (k ⊗[k] k) (A ⊗[R] C) ((1 : k) ⊗ₜ[k] (1 : k)))
  have hθ : ∀ (a' : A) (c : C), θ (a' ⊗ₜ[R] c) = ((1 : k) ⊗ₜ[R] a') ⊗ₜ[k] ((1 : k) ⊗ₜ[R] c) := fun a' c => by
    simp [θ]

  have hnat : ∀ y : A ⊗[R] A,
      Algebra.TensorProduct.map (AlgHom.id k (k ⊗[R] A)) (bc π : k ⊗[R] A →ₐ[k] k ⊗[R] C)
          (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R k R k k k A A
            (((1 : k) ⊗ₜ[k] (1 : k)) ⊗ₜ[R] y)) =
        θ (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] C) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero, map_zero, LinearMap.map_zero]
    | tmul a₁ a₂ =>
        rw [Algebra.TensorProduct.map_tmul, hθ]
        simp [bc]
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, map_add, map_add]
  have hcomul : Coalgebra.comul (R := k) ((1 : k) ⊗ₜ[R] a) =
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R k R k k k A A
        (((1 : k) ⊗ₜ[k] (1 : k)) ⊗ₜ[R] Coalgebra.comul (R := R) a) := by
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  rw [HopfAlgebra.coaction_apply, hcomul, hnat, ← HopfAlgebra.coaction_apply, ha, hθ]
  rfl

theorem baseChange_hopfKer_eq [Module.Free R ↥(hopfKer π)] (hπ : Function.Surjective π) :
    (Subalgebra.toSubmodule (hopfKer π)).baseChange k = Subalgebra.toSubmodule (hopfKer (bc π)) := by
  have hle : (Subalgebra.toSubmodule (hopfKer π)).baseChange k ≤ Subalgebra.toSubmodule (hopfKer (bc π)) := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact one_tmul_mem_hopfKer_bc π ha
  apply Submodule.eq_of_le_of_finrank_eq hle

  obtain ⟨⟨r, hr⟩, -, -, -⟩ := HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  have hinj : Function.Injective ((Subalgebra.toSubmodule (hopfKer π)).subtype.baseChange k) := by

    let r' : A →ₗ[R] ↥(hopfKer π) := r.restrictScalars R
    have hsplit : r' ∘ₗ (Subalgebra.toSubmodule (hopfKer π)).subtype = LinearMap.id := by
      ext c; exact congrArg Subtype.val (hr c)
    intro x y hxy
    have := congrArg (r'.baseChange k) hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hsplit,
      LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.id_apply] at this
  have h1 : Module.finrank k ↥((Subalgebra.toSubmodule (hopfKer π)).baseChange k) = Module.finrank R ↥(hopfKer π) := by
    rw [Submodule.baseChange, LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]
    rfl
  have hC : 0 < Module.finrank R C := by
    haveI : Nontrivial C := (Bialgebra.counitAlgHom R C).toRingHom.domain_nontrivial
    rw [Module.finrank_eq_card_chooseBasisIndex]
    exact Fintype.card_pos
  have h2 := finrank_hopfKer_mul π hπ
  have h3 := finrank_hopfKer_bc_mul π hπ
  rw [h1]
  exact Nat.eq_of_mul_eq_mul_right hC (h2.trans h3.symm)

end BaseChange

end HOPFKERBC
p2m_reactivate "P2MW.S_HopfAlgebra_baseChange_toSubmodule_hopfKer_eq_toSubmodule_hopfKer_map_residueField_of_surjective.HOPFKERBC"

end
p2m_reactivate "P2MW.S_HopfAlgebra_baseChange_toSubmodule_hopfKer_eq_toSubmodule_hopfKer_map_residueField_of_surjective.HOPFKERBC"

open scoped TensorProduct

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R]
    {A C : Type} [CommRing A] [CommRing C] [HopfAlgebra R A] [HopfAlgebra R C]
    [Module.Finite R A] [Module.Free R A] [Module.Finite R C] [Module.Free R C]
    (π : A →ₐc[R] C) (hπ : Function.Surjective π) :
    (Subalgebra.toSubmodule (HopfAlgebra.hopfKer π)).baseChange (IsLocalRing.ResidueField R) =
      Subalgebra.toSubmodule (HopfAlgebra.hopfKer
        (Bialgebra.TensorProduct.map
          (BialgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) π)) := by

  obtain ⟨-, hfin, hproj, -⟩ := HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R ↥(HopfAlgebra.hopfKer π) := Module.free_of_flat_of_isLocalRing
  exact HOPFKERBC.baseChange_hopfKer_eq π hπ

end S_HopfAlgebra_baseChange_toSubmodule_hopfKer_eq_toSubmodule_hopfKer_map_residueField_of_surjective
end P2MW
export P2MW.S_HopfAlgebra_baseChange_toSubmodule_hopfKer_eq_toSubmodule_hopfKer_map_residueField_of_surjective (solution)
