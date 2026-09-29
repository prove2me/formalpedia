-- Prove2me | solution 1 for KaehlerDifferential.nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a45fe8d1-f8f4-5ece-8c5b-1e29aeb2eec2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

namespace Conormal29

section

variable (R C A R' : Type u) [CommRing R] [CommRing C] [CommRing A] [CommRing R']
    [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    [Algebra A R'] [Algebra C R'] [IsScalarTower C A R']

noncomputable def ψ : R' ⊗[C] Ω[C⁄R] →ₗ[R'] R' ⊗[A] Ω[A⁄R] :=
  ((KaehlerDifferential.mapBaseChange R C A).baseChange R') ∘ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange C A R' R' Ω[C⁄R]).symm.toLinearMap

noncomputable def N : Submodule R' (R' ⊗[C] Ω[C⁄R]) :=
  Submodule.span R' (Set.range fun f : RingHom.ker (algebraMap C A) => (1 : R') ⊗ₜ[C] D R C (f : C))

omit [Algebra R A] [IsScalarTower R C A] in
theorem cancelBaseChange_symm_tmul (r : R') (ω : Ω[C⁄R]) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange C A R' R' Ω[C⁄R]).symm (r ⊗ₜ[C] ω) =
      r ⊗ₜ[A] ((1 : A) ⊗ₜ[C] ω) := rfl

theorem ψ_tmul (r : R') (ω : Ω[C⁄R]) :
    ψ R C A R' (r ⊗ₜ[C] ω) = r ⊗ₜ[A] KaehlerDifferential.map R R C A ω := by
  simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, cancelBaseChange_symm_tmul,
    LinearMap.baseChange_tmul, mapBaseChange_tmul, one_smul]

variable {R C A R'}

theorem ψ_surjective (hsurj : Function.Surjective (algebraMap C A)) :
    Function.Surjective (ψ R C A R') := by
  have h1 : Function.Surjective ((KaehlerDifferential.mapBaseChange R C A).baseChange R') := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective R' (mapBaseChange_surjective R C A hsurj)
  exact h1.comp (TensorProduct.AlgebraTensorModule.cancelBaseChange C A R' R' Ω[C⁄R]).symm.surjective

variable (R C A R') in
theorem N_le_ker : N R C A R' ≤ LinearMap.ker (ψ R C A R') := by
  rw [N, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, ψ_tmul, map_D, RingHom.mem_ker.mp f.2, map_zero,
    TensorProduct.tmul_zero]

theorem ker_le_N (hsurj : Function.Surjective (algebraMap C A)) :
    LinearMap.ker (ψ R C A R') ≤ N R C A R' := by
  intro x hx
  have hgs : Function.Surjective (KaehlerDifferential.mapBaseChange R C A) :=
    mapBaseChange_surjective R C A hsurj

  have hy : LinearMap.lTensor R' (KaehlerDifferential.mapBaseChange R C A)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange C A R' R' Ω[C⁄R]).symm x) = 0 := by
    rw [← LinearMap.baseChange_eq_ltensor]
    exact hx

  have hex : Function.Exact
      (LinearMap.lTensor R' (LinearMap.ker (KaehlerDifferential.mapBaseChange R C A)).subtype)
      (LinearMap.lTensor R' (KaehlerDifferential.mapBaseChange R C A)) :=
    lTensor_exact R' (LinearMap.exact_subtype_ker_map _) hgs
  obtain ⟨t, ht⟩ := (hex _).1 hy
  have hxE : x = TensorProduct.AlgebraTensorModule.cancelBaseChange C A R' R' Ω[C⁄R]
      (LinearMap.lTensor R' (LinearMap.ker (KaehlerDifferential.mapBaseChange R C A)).subtype t) := by
    rw [ht, LinearEquiv.apply_symm_apply]
  rw [hxE]
  clear hxE ht hy hx

  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact (N R C A R').zero_mem
  | tmul r k =>
    obtain ⟨κ, hκ⟩ := ((exact_kerCotangentToTensor_mapBaseChange R C A hsurj) k.1).1 k.2
    obtain ⟨f, rfl⟩ := Ideal.toCotangent_surjective _ κ
    rw [kerCotangentToTensor_toCotangent] at hκ
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ← hκ]
    change TensorProduct.AlgebraTensorModule.cancelBaseChange C A R' R' Ω[C⁄R]
      (r ⊗ₜ[A] ((1 : A) ⊗ₜ[C] D R C (f : C))) ∈ N R C A R'
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    have : r ⊗ₜ[C] D R C (f : C) = r • ((1 : R') ⊗ₜ[C] D R C (f : C)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨f, rfl⟩)
  | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb

theorem ker_eq_N (hsurj : Function.Surjective (algebraMap C A)) :
    LinearMap.ker (ψ R C A R') = N R C A R' :=
  le_antisymm (ker_le_N hsurj) (N_le_ker R C A R')

end

end Conormal29

open Conormal29

theorem solution
    {R C A R' : Type u} [CommRing R] [CommRing C] [CommRing A] [CommRing R']
    [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (hsurj : Function.Surjective (algebraMap C A))
    [Algebra A R'] [Algebra C R'] [IsScalarTower C A R'] :
    Nonempty ((R' ⊗[A] Ω[A⁄R]) ≃ₗ[R']
      ((R' ⊗[C] Ω[C⁄R]) ⧸ Submodule.span R'
        (Set.range fun f : RingHom.ker (algebraMap C A) => (1 : R') ⊗ₜ[C] D R C (f : C)))) := by
  have e0 := Submodule.quotEquivOfEq _ _ (ker_eq_N (R := R) (C := C) (A := A) (R' := R') hsurj).symm
  have e1 := LinearMap.quotKerEquivOfSurjective _ (ψ_surjective (R := R) (C := C) (A := A) (R' := R') hsurj)
  exact ⟨(e0.trans e1).symm⟩

end S_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
end P2MW
export P2MW.S_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective (solution)
