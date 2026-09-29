-- Prove2me | solution 1 for HopfAlgebra.isReduced_cartierDual_of_surjective_of_isLocalRing_of_bijective_tensorProduct_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4673d1ce-70df-520d-b3db-819061c55fce

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isReduced_cartierDual_of_surjective_of_isLocalRing_of_bijective_tensorProduct_isReduced

set_option autoImplicit false

open scoped TensorProduct

namespace ConnInOrd

theorem eq_zero_or_eq_one_of_isIdempotentElem_of_isLocalRing {L : Type*} [CommRing L] [IsLocalRing L]
    (x : L) (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  have h0 : x * (1 - x) = 0 := by rw [mul_sub, mul_one, hx.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with hu | hu
  · right
    have : (1 - x) = 0 := by
      obtain ⟨u, rfl⟩ := hu
      simpa using congrArg (fun y => (↑u⁻¹ : L) * y) h0
    exact (sub_eq_zero.mp this).symm
  · left
    obtain ⟨u, hu⟩ := hu
    have := congrArg (fun y => y * (↑u⁻¹ : L)) h0
    simpa [mul_assoc, hu.symm] using this

theorem algHom_apply_eq_algebraMap_counit
    {K : Type*} [Field K] {E : Type*} [CommRing E] [Bialgebra K E] [Module.Finite K E] [IsReduced E]
    {L : Type*} [Ring L] [Algebra K L]
    (hidem : ∀ y : L, IsIdempotentElem y → y = 0 ∨ y = 1)
    (f : E →ₐ[K] L) (g : L →+* K) (hg : ∀ x, g (f x) = Coalgebra.counit x) (x : E) :
    f x = algebraMap K L (Coalgebra.counit x) := by
  classical
  haveI : IsArtinianRing E := IsArtinianRing.of_finite K E
  haveI : IsSemisimpleRing E := IsArtinianRing.isSemisimpleRing_of_isReduced E

  set I : Ideal E := RingHom.ker (Bialgebra.counitAlgHom K E) with hI
  obtain ⟨J, hIJ⟩ := exists_isCompl (I : Submodule E E)
  have h1 : (1 : E) ∈ (I ⊔ J : Submodule E E) := by rw [hIJ.sup_eq_top]; trivial
  obtain ⟨e, he, e', he', hee'⟩ := Submodule.mem_sup.mp h1

  have hxe : ∀ y ∈ I, y = y * e := by
    intro y hy
    have hyJ : y * e' ∈ (J : Submodule E E) := by
      simpa [smul_eq_mul] using J.smul_mem y he'
    have hyI : y * e' ∈ I := I.mul_mem_right _ hy
    have h0 : y * e' = 0 := by
      have : y * e' ∈ (I ⊓ J : Submodule E E) := ⟨hyI, hyJ⟩
      rwa [hIJ.inf_eq_bot, Submodule.mem_bot] at this
    calc y = y * (e + e') := by rw [hee', mul_one]
      _ = y * e := by rw [mul_add, h0, add_zero]

  have heI : Coalgebra.counit (R := K) e = 0 := by simpa [hI, RingHom.mem_ker] using he
  have hfe : f e = 0 := by
    have hid : IsIdempotentElem (f e) := by
      change f e * f e = f e
      rw [← map_mul, ← hxe e he]
    rcases hidem _ hid with h | h
    · exact h
    · exfalso
      have := hg e
      rw [h, map_one, heI] at this
      exact one_ne_zero this
  have hfI : ∀ y ∈ I, f y = 0 := fun y hy => by rw [hxe y hy, map_mul, hfe, mul_zero]

  have hx : x - algebraMap K E (Coalgebra.counit x) ∈ I := by
    simp [hI, RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
  have := hfI _ hx
  rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this

section IncludeLeft

variable (R : Type*) [CommRing R] (A B : Type*) [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

theorem map_includeLeft_includeLeft_eq (z : A ⊗[R] A) :
    Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) z =
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R R R A A B B (z ⊗ₜ[R] ((1 : B) ⊗ₜ[R] (1 : B))) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, TensorProduct.zero_tmul, LinearEquiv.map_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    rfl
  | add x y hx hy => rw [map_add, TensorProduct.add_tmul, LinearEquiv.map_add, hx, hy]

noncomputable def includeLeftBialgHom : A →ₐc[R] A ⊗[R] B :=
  BialgHom.ofAlgHom (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)
    (by
      ext a
      simp [Algebra.TensorProduct.includeLeft_apply])
    (by
      ext a
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply,
        Algebra.TensorProduct.includeLeft_apply, TensorProduct.comul_tmul, Bialgebra.comul_one]
      exact map_includeLeft_includeLeft_eq R A B (Coalgebra.comul a))

@[scoped simp] theorem includeLeftBialgHom_apply (a : A) : includeLeftBialgHom R A B a = a ⊗ₜ[R] 1 := rfl

end IncludeLeft

end ConnInOrd
p2m_reactivate "P2MW.S_HopfAlgebra_isReduced_cartierDual_of_surjective_of_isLocalRing_of_bijective_tensorProduct_isReduced.ConnInOrd"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (C : Type) [CommRing C] [HopfAlgebra (ZMod p) C] [Coalgebra.IsCocomm (ZMod p) C]
    [Module.Finite (ZMod p) C] [Module.Free (ZMod p) C]
    (M : Type) [CommRing M] [HopfAlgebra (ZMod p) M] [Module.Finite (ZMod p) M] [Module.Free (ZMod p) M]
    (E : Type) [CommRing E] [HopfAlgebra (ZMod p) E]
    (Θ : C →ₐc[ZMod p] M ⊗[ZMod p] E) (hΘ : Function.Bijective Θ)
    (hE : IsReduced E) (hM : IsReduced (CartierDual (ZMod p) M))
    (L : Type) [CommRing L] [HopfAlgebra (ZMod p) L] [Coalgebra.IsCocomm (ZMod p) L]
    [Module.Finite (ZMod p) L] [Module.Free (ZMod p) L]
    (r : C →ₐc[ZMod p] L) (hr : Function.Surjective r) (hL : IsLocalRing L) :
    IsReduced (CartierDual (ZMod p) L) := by
  classical
  haveI := hE
  haveI := hL

  let Θ' : C ≃ₐc[ZMod p] M ⊗[ZMod p] E := BialgEquiv.ofBijective Θ hΘ
  let Θs : M ⊗[ZMod p] E →ₐc[ZMod p] C := (Θ'.symm : M ⊗[ZMod p] E →ₐc[ZMod p] C)
  have hΘs : Function.Surjective Θs := fun c => ⟨Θ' c, Θ'.symm_apply_apply c⟩
  let ι : M →ₐc[ZMod p] M ⊗[ZMod p] E := ConnInOrd.includeLeftBialgHom (ZMod p) M E
  let q : M →ₐc[ZMod p] L := r.comp (Θs.comp ι)
  let f : E →ₐ[ZMod p] L :=
    (r : C →ₐ[ZMod p] L).comp ((Θs : M ⊗[ZMod p] E →ₐ[ZMod p] C).comp
      (Algebra.TensorProduct.includeRight : E →ₐ[ZMod p] M ⊗[ZMod p] E))
  have hf_def : ∀ x : E, f x = r (Θs ((1 : M) ⊗ₜ[ZMod p] x)) := fun x => rfl
  have hq_def : ∀ m : M, q m = r (Θs (m ⊗ₜ[ZMod p] (1 : E))) := fun m => rfl

  haveI : Module.Finite (ZMod p) (M ⊗[ZMod p] E) :=
    Module.Finite.of_surjective (Θ : C →ₐc[ZMod p] M ⊗[ZMod p] E).toLinearMap hΘ.2
  haveI : Module.Finite (ZMod p) E :=
    Module.Finite.of_injective (Algebra.TensorProduct.includeRight (R := ZMod p) (A := M) (B := E)).toLinearMap
      (Algebra.TensorProduct.includeRight_injective (Bialgebra.algebraMap_injective (R := ZMod p) (A := M)))

  have hf : ∀ x : E, f x = algebraMap (ZMod p) L (Coalgebra.counit x) := by
    refine ConnInOrd.algHom_apply_eq_algebraMap_counit
      (fun y hy => ConnInOrd.eq_zero_or_eq_one_of_isIdempotentElem_of_isLocalRing y hy) f
      (Bialgebra.counitAlgHom (ZMod p) L).toRingHom (fun x => ?_)
    show Coalgebra.counit (R := ZMod p) (f x) = Coalgebra.counit x
    rw [hf_def, CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply, TensorProduct.counit_tmul,
      Bialgebra.counit_one, smul_eq_mul, mul_one]

  have hq : Function.Surjective q := by
    intro l
    obtain ⟨c, rfl⟩ := hr l
    obtain ⟨t, rfl⟩ := hΘs c
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero, map_zero]⟩
    | tmul m e =>
      refine ⟨Coalgebra.counit (R := ZMod p) e • m, ?_⟩
      have hsplit : m ⊗ₜ[ZMod p] e = (m ⊗ₜ[ZMod p] (1 : E)) * ((1 : M) ⊗ₜ[ZMod p] e) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hq_def, hsplit, map_mul, map_mul, ← hf_def, hf, ← Algebra.commutes, ← Algebra.smul_def,
        ← map_smul, ← map_smul, TensorProduct.smul_tmul']
    | add x y hx hy =>
      obtain ⟨m₁, h₁⟩ := hx
      obtain ⟨m₂, h₂⟩ := hy
      exact ⟨m₁ + m₂, by rw [map_add, h₁, h₂, map_add, map_add]⟩

  have hinj : Function.Injective (CartierDual.mapAlgHom q) := by
    intro φ ψ h
    apply CartierDual.ext
    intro l
    obtain ⟨m, rfl⟩ := hq l
    have := congrArg (fun χ : CartierDual (ZMod p) M => χ m) h
    simpa only [CartierDual.mapAlgHom_apply] using this
  haveI := hM
  exact isReduced_of_injective (CartierDual.mapAlgHom q) hinj

#print axioms solution

end S_HopfAlgebra_isReduced_cartierDual_of_surjective_of_isLocalRing_of_bijective_tensorProduct_isReduced
end P2MW
export P2MW.S_HopfAlgebra_isReduced_cartierDual_of_surjective_of_isLocalRing_of_bijective_tensorProduct_isReduced (solution)
