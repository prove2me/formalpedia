-- Prove2me | solution 1 for HopfAlgebra.exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/df8ff20e-2aad-574c-8637-65fe3350f492

import Mathlib
import Definitions.Def_HopfAlgebra_FVectStructure
import Theorems.Thm_HopfAlgebra_algHom_eq_of_forall_comp_eq_of_bijective_evalPoints
import Theorems.Thm_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints

set_option autoImplicit false
open scoped TensorProduct

namespace DescFV
variable (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]
set_option quotPrecheck false in
local notation "F′" => ↥(IntermediateField.fixedField D)
local notation "Qb" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "Pt" => WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)

theorem main
    [Module.Finite F′ A] [Finite Pt]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
        (Pi.algHom ↥(IntermediateField.fixedField D) _
          fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) =>
            (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A →ₐ[AlgebraicClosure ℚ]
          (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)))
    (F : Type*) [Field F]
    (act : F → (Pt →* Pt))
    (hact : ∀ a : F, ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
        (∀ x : A, WithConv.ofConv ν' x = σ (WithConv.ofConv ν x)) →
        ∀ x : A, WithConv.ofConv (act a ν') x = σ (WithConv.ofConv (act a ν) x))
    (hadd : ∀ (a b : F) (ν : Pt), act (a + b) ν = act a ν * act b ν)
    (hzero : ∀ ν : Pt, act 0 ν = 1)
    (hmul : ∀ (a b : F) (ν : Pt), act (a * b) ν = act a (act b ν))
    (hone : ∀ ν : Pt, act 1 ν = ν) :
    ∃ fv : HopfAlgebra.FVectStructure F F′ A,
      ∀ (a : F) (ν : Pt), WithConv.toConv ((WithConv.ofConv ν).comp (fv.act a : A →ₐ[F′] A)) = act a ν := by
  classical

  have hex : ∀ a : F, ∃ u : A →ₐc[F′] A, ∀ ν : Pt,
      WithConv.toConv ((WithConv.ofConv ν).comp (u : A →ₐ[F′] A)) = act a ν :=
    fun a => HopfAlgebra.exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints
      D A hev (act a) (hact a)
  choose u hu using hex

  have sep : ∀ v v' : A →ₐ[F′] A,
      (∀ ν : Pt, WithConv.toConv ((WithConv.ofConv ν).comp v) = WithConv.toConv ((WithConv.ofConv ν).comp v')) →
      v = v' := by
    intro v v' h
    apply HopfAlgebra.algHom_eq_of_forall_comp_eq_of_bijective_evalPoints D A hev
    intro ν
    have := h (WithConv.toConv ν)
    simpa using this
  have hu' : ∀ (a : F) (ν : Pt), (WithConv.ofConv ν).comp (u a : A →ₐ[F′] A) = WithConv.ofConv (act a ν) := by
    intro a ν
    have := congrArg WithConv.ofConv (hu a ν)
    simpa using this
  have sepB : ∀ v v' : A →ₐc[F′] A,
      (∀ ν : Pt, WithConv.toConv ((WithConv.ofConv ν).comp (v : A →ₐ[F′] A)) =
        WithConv.toConv ((WithConv.ofConv ν).comp (v' : A →ₐ[F′] A))) → v = v' :=
    fun v v' h => BialgHom.coe_algHom_injective (sep _ _ h)

  have hunit : ∀ ν : Pt, WithConv.toConv ((WithConv.ofConv ν).comp
      (WithConv.ofConv (1 : WithConv (A →ₐ[F′] A)))) = (1 : Pt) := by
    intro ν
    change WithConv.toConv ((WithConv.ofConv ν).comp
      ((Algebra.ofId F′ A).comp (Bialgebra.counitAlgHom F′ A))) =
      WithConv.toConv ((Algebra.ofId F′ Qb).comp (Bialgebra.counitAlgHom F′ A))
    congr 1
    apply AlgHom.ext
    intro x
    simp
  have h_one : u 1 = BialgHom.id F′ A := by
    apply sepB
    intro ν
    rw [hu, hone]
    simp
  have h_mul : ∀ a b : F, u (a * b) = (u a).comp (u b) := by
    intro a b
    apply sepB
    intro ν
    rw [hu, mul_comm, hmul]

    have e1 : ((u a).comp (u b) : A →ₐ[F′] A) = (u a : A →ₐ[F′] A).comp (u b : A →ₐ[F′] A) := rfl
    rw [e1, ← AlgHom.comp_assoc, hu' a ν, hu' b (act a ν)]
  have h_zero : WithConv.toConv (u 0 : A →ₐ[F′] A) = (1 : WithConv (A →ₐ[F′] A)) := by
    suffices h : (u 0 : A →ₐ[F′] A) = WithConv.ofConv (1 : WithConv (A →ₐ[F′] A)) by rw [h]
    apply sep
    intro ν
    rw [hu, hzero, hunit]
  have h_add : ∀ a b : F, WithConv.toConv (u (a + b) : A →ₐ[F′] A) =
      WithConv.toConv (u a : A →ₐ[F′] A) * WithConv.toConv (u b : A →ₐ[F′] A) := by
    intro a b
    suffices h : (u (a + b) : A →ₐ[F′] A) =
        WithConv.ofConv (WithConv.toConv (u a : A →ₐ[F′] A) * WithConv.toConv (u b : A →ₐ[F′] A)) by
      rw [h]
    apply sep
    intro ν
    rw [hu, hadd, AlgHom.comp_convMul_distrib, hu, hu]
  exact ⟨⟨u, h_one, h_mul, h_zero, h_add⟩, hu⟩

end DescFV

theorem solution
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]
    [Module.Finite ↥(IntermediateField.fixedField D) A]
    [Finite (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
        (Pi.algHom ↥(IntermediateField.fixedField D) _
          fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) =>
            (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A →ₐ[AlgebraicClosure ℚ]
          (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)))
    (F : Type*) [Field F]
    (act : F → (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) →* WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)))
    (hact : ∀ a : F, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ D →
      ∀ ν ν' : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ),
        (∀ x : A, WithConv.ofConv ν' x = σ (WithConv.ofConv ν x)) →
        ∀ x : A, WithConv.ofConv (act a ν') x = σ (WithConv.ofConv (act a ν) x))
    (hadd : ∀ (a b : F) (ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)), act (a + b) ν = act a ν * act b ν)
    (hzero : ∀ ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ), act 0 ν = 1)
    (hmul : ∀ (a b : F) (ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)), act (a * b) ν = act a (act b ν))
    (hone : ∀ ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ), act 1 ν = ν) :
    ∃ fv : HopfAlgebra.FVectStructure F ↥(IntermediateField.fixedField D) A,
      ∀ (a : F) (ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)),
        WithConv.toConv ((WithConv.ofConv ν).comp (fv.act a : A →ₐ[↥(IntermediateField.fixedField D)] A)) = act a ν :=
  DescFV.main D A hev F act hact hadd hzero hmul hone

end S_HopfAlgebra_exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints
end P2MW
export P2MW.S_HopfAlgebra_exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints (solution)
