-- Prove2me | solution 1 for HopfAlgebra.isCocomm_of_isReduced_baseChange_of_withConv_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3210ff6e-20da-5d9c-acfc-24f419cd4610

import Mathlib
import Theorems.Thm_Algebra_FormallyUnramified_of_isReduced_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isCocomm_of_isReduced_baseChange_of_withConv_equiv

open scoped TensorProduct

namespace E42

section sep
variable (Ω : Type*) [Field Ω] [IsAlgClosed Ω]

theorem eq_zero_of_forall_algHom_apply_eq_zero (C : Type*) [CommRing C] [Algebra Ω C]
    [Module.Finite Ω C] [IsReduced C] (c : C) (hc : ∀ φ : C →ₐ[Ω] Ω, φ c = 0) : c = 0 := by
  haveI : IsArtinianRing C := IsArtinianRing.of_finite Ω C
  have hmem : c ∈ Ideal.jacobson (⊥ : Ideal C) := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    letI : Field (C ⧸ m) := Ideal.Quotient.field m
    haveI : Module.Finite Ω (C ⧸ m) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ Ω m).toLinearMap
        (Ideal.Quotient.mkₐ_surjective Ω m)
    haveI : Algebra.IsIntegral Ω (C ⧸ m) := inferInstance
    let ψ : Ω ≃ₐ[Ω] (C ⧸ m) :=
      AlgEquiv.ofBijective (Algebra.ofId Ω (C ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
    let φ : C →ₐ[Ω] Ω := ψ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ Ω m)
    have h2 : Ideal.Quotient.mkₐ Ω m c = 0 :=
      ψ.symm.injective (by rw [map_zero]; exact hc φ)
    change Ideal.Quotient.mk m c = 0 at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
  have hcn : c ^ n ∈ (⊥ : Ideal C).jacobson ^ n := Ideal.pow_mem_pow hmem n
  rw [hn] at hcn
  exact IsReduced.eq_zero c ⟨n, by simpa using hcn⟩

variable (R : Type*) [CommRing R] [Algebra R Ω]

open Algebra.TensorProduct in

theorem baseChange_eq_zero_of_forall_lift_eq_zero (A : Type*) [CommRing A] [Algebra R A]
    [Module.Finite Ω (Ω ⊗[R] A)] [IsReduced (Ω ⊗[R] A)] (t : Ω ⊗[R] A)
    (ht : ∀ f : A →ₐ[R] Ω, lift (AlgHom.id Ω Ω) f (fun _ _ => .all _ _) t = 0) : t = 0 := by
  refine eq_zero_of_forall_algHom_apply_eq_zero Ω (Ω ⊗[R] A) t fun φ => ?_
  have hφ : φ = lift (AlgHom.id Ω Ω) ((φ.restrictScalars R).comp includeRight)
      (fun _ _ => .all _ _) := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · ext a
      simp
  rw [hφ]
  exact ht _

variable (H : Type*) [CommRing H] [Algebra R H]

noncomputable def baseChangeTensorEquiv :
    (Ω ⊗[R] H) ⊗[Ω] (Ω ⊗[R] H) ≃ₐ[Ω] Ω ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.cancelBaseChange R Ω Ω (Ω ⊗[R] H) H).trans
    (Algebra.TensorProduct.assoc R R Ω Ω H H)

omit [IsAlgClosed Ω] in
theorem finite_baseChange_tensor [Module.Finite Ω (Ω ⊗[R] H)] :
    Module.Finite Ω (Ω ⊗[R] (H ⊗[R] H)) :=
  Module.Finite.equiv (baseChangeTensorEquiv Ω R H).toLinearEquiv

theorem isReduced_baseChange_tensor [Module.Finite Ω (Ω ⊗[R] H)] [IsReduced (Ω ⊗[R] H)] :
    IsReduced (Ω ⊗[R] (H ⊗[R] H)) := by
  haveI : Algebra.FormallyUnramified Ω (Ω ⊗[R] H) :=
    Algebra.FormallyUnramified.of_isReduced_of_perfectField Ω (Ω ⊗[R] H)
  haveI : Algebra.FormallyUnramified (Ω ⊗[R] H) ((Ω ⊗[R] H) ⊗[Ω] (Ω ⊗[R] H)) := inferInstance
  haveI : Algebra.FormallyUnramified Ω ((Ω ⊗[R] H) ⊗[Ω] (Ω ⊗[R] H)) :=
    Algebra.FormallyUnramified.comp Ω (Ω ⊗[R] H) _
  haveI : Algebra.EssFiniteType Ω ((Ω ⊗[R] H) ⊗[Ω] (Ω ⊗[R] H)) := inferInstance
  haveI : IsReduced ((Ω ⊗[R] H) ⊗[Ω] (Ω ⊗[R] H)) :=
    Algebra.FormallyUnramified.isReduced_of_field Ω ((Ω ⊗[R] H) ⊗[Ω] (Ω ⊗[R] H))
  exact isReduced_of_injective (baseChangeTensorEquiv Ω R H).symm
    (baseChangeTensorEquiv Ω R H).symm.injective

open Algebra.TensorProduct in

theorem baseChange_tensor_eq_zero_of_forall [Module.Finite Ω (Ω ⊗[R] H)] [IsReduced (Ω ⊗[R] H)]
    (t : Ω ⊗[R] (H ⊗[R] H))
    (ht : ∀ f g : H →ₐ[R] Ω,
      lift (AlgHom.id Ω Ω) (lift f g (fun _ _ => .all _ _)) (fun _ _ => .all _ _) t = 0) :
    t = 0 := by
  haveI := finite_baseChange_tensor Ω R H
  haveI := isReduced_baseChange_tensor Ω R H
  refine baseChange_eq_zero_of_forall_lift_eq_zero Ω R (H ⊗[R] H) t fun F => ?_
  have hF : F = lift (F.comp includeLeft) (F.comp includeRight) (fun _ _ => .all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [← map_mul]
  rw [hF]
  exact ht _ _

end sep

open Algebra.TensorProduct in
theorem isCocomm_main (R : Type*) [CommRing R] (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (hinj : Function.Injective (algebraMap R Ω))
    (H : Type*) [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    [Module.Finite Ω (Ω ⊗[R] H)] [IsReduced (Ω ⊗[R] H)]
    {N : Type*} [AddCommGroup N] (e : WithConv (H →ₐ[R] Ω) ≃ N)
    (he : ∀ f g : WithConv (H →ₐ[R] Ω), e (f * g) = e f + e g) :
    Coalgebra.IsCocomm R H := by
  have hcomm : ∀ f g : WithConv (H →ₐ[R] Ω), f * g = g * f := fun f g =>
    e.injective (by rw [he, he, add_comm])
  have hj : Function.Injective (includeRight : H ⊗[R] H →ₐ[R] Ω ⊗[R] (H ⊗[R] H)) :=
    includeRight_injective hinj
  constructor
  ext h
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  apply hj
  rw [← sub_eq_zero, ← map_sub]
  apply baseChange_tensor_eq_zero_of_forall Ω R H
  intro f g
  rw [map_sub, map_sub, sub_eq_zero]
  simp only [includeRight_apply, lift_tmul, map_one, one_mul]
  have key : ∀ x : H ⊗[R] H, lift f g (fun _ _ => .all _ _) (TensorProduct.comm R H H x)
      = lift g f (fun _ _ => .all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [mul_comm]
    | add x y hx hy => simp [hx, hy]
  rw [key]
  have h1 := congrArg (fun φ : WithConv (H →ₐ[R] Ω) => φ h)
    (hcomm (WithConv.toConv g) (WithConv.toConv f))
  simpa [AlgHom.convMul_apply] using h1

end E42

theorem solution (R : Type*) [CommRing R] (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (hinj : Function.Injective (algebraMap R Ω))
    (H : Type*) [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    [Module.Finite Ω (Ω ⊗[R] H)] [IsReduced (Ω ⊗[R] H)]
    {N : Type*} [AddCommGroup N] (e : WithConv (H →ₐ[R] Ω) ≃ N)
    (he : ∀ f g : WithConv (H →ₐ[R] Ω), e (f * g) = e f + e g) :
    Coalgebra.IsCocomm R H :=
  E42.isCocomm_main R Ω hinj H e he

end S_HopfAlgebra_isCocomm_of_isReduced_baseChange_of_withConv_equiv
end P2MW
export P2MW.S_HopfAlgebra_isCocomm_of_isReduced_baseChange_of_withConv_equiv (solution)
