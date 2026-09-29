-- Prove2me | solution 1 for HopfAlgebra.exists_bialgHom_comp_eq_of_injective_baseChange_of_finrank_eq_of_comp_eq_counit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/12a6221c-d0ed-56f5-b333-596ef640c059

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgHom_comp_eq_of_injective_baseChange_of_finrank_eq_of_comp_eq_counit

set_option autoImplicit false

open scoped TensorProduct

namespace G5Aux

open HopfAlgebra

variable {R : Type*} [CommRing R]
variable {X Y Z : Type*} [CommRing X] [CommRing Y] [CommRing Z] [Bialgebra R X] [Bialgebra R Y] [Bialgebra R Z]

theorem apply_mem_hopfKer_of_comp_eq (φ : X →ₐc[R] Y) (π : Y →ₐc[R] Z)
    (h : ((π : Y →ₐc[R] Z).comp φ : X →ₐ[R] Z) = (Algebra.ofId R Z).comp (Bialgebra.counitAlgHom R X)) (x : X) :
    φ x ∈ hopfKer π := by
  classical
  rw [mem_hopfKer_iff, coaction_apply]
  have hπφ : ∀ y : X, π (φ y) = algebraMap R Z (Coalgebra.counit y) := fun y => by
    have := DFunLike.congr_fun h y
    simpa using this

  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (Coalgebra.comul (R := R) x)
  have hΔ : Coalgebra.comul (R := R) (φ x) = ∑ t ∈ S, φ t.1 ⊗ₜ[R] φ t.2 := by
    rw [← CoalgHomClass.map_comp_comul_apply φ x, hS, map_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [TensorProduct.map_tmul]
    rfl

  have hε : ∑ t ∈ S, Coalgebra.counit (R := R) t.2 • t.1 = x := by
    have h1 := Coalgebra.lTensor_counit_comul (R := R) x
    rw [hS, map_sum] at h1
    simp only [LinearMap.lTensor_tmul] at h1
    have h2 := congrArg (TensorProduct.rid R X) h1
    rw [map_sum, TensorProduct.rid_tmul, one_smul] at h2
    simpa only [TensorProduct.rid_tmul] using h2
  rw [hΔ, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  conv_rhs => rw [← hε, map_sum, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [show (π : Y →ₐ[R] Z) (φ t.2) = π (φ t.2) from rfl, hπφ, map_smul, Algebra.algebraMap_eq_smul_one,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul']

end G5Aux

open G5Aux HopfAlgebra

set_option maxHeartbeats 6400000 in

theorem solution
    {O : Type} [CommRing O]
    {B C K : Type} [CommRing B] [CommRing C] [CommRing K] [HopfAlgebra O B] [HopfAlgebra O C] [HopfAlgebra O K]
    [Module.Finite O B] [Module.Free O B] [Module.Finite O C] [Module.Free O C] [Module.Finite O K] [Module.Free O K]
    (ψ : B →ₐc[O] C)
    (q : C →ₐc[O] K) (hq : Function.Surjective q)
    (hkerq : RingHom.ker (q : C →+* K) = Ideal.map (ψ : B →ₐ[O] C) (RingHom.ker (Bialgebra.counitAlgHom O B)))

    (hrk : Module.finrank O B * Module.finrank O K = Module.finrank O C)
    (k : Type) [Field k] [Algebra O k]
    {A : Type} [CommRing A] [Bialgebra k A]

    (hψk : Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id k k) ψ))
    (f : A →ₐc[k] k ⊗[O] C)
    (hf : ((Bialgebra.TensorProduct.map (BialgHom.id k k) q).comp f : A →ₐ[k] k ⊗[O] K) =
      (Algebra.ofId k (k ⊗[O] K)).comp (Bialgebra.counitAlgHom k A)) :
    ∃ g : A →ₐc[k] k ⊗[O] B, (Bialgebra.TensorProduct.map (BialgHom.id k k) ψ).comp g = f := by
  classical
  haveI : Nontrivial O := (algebraMap O k).domain_nontrivial
  set ψ' : k ⊗[O] B →ₐc[k] k ⊗[O] C := Bialgebra.TensorProduct.map (BialgHom.id k k) ψ with hψ'def
  set q' : k ⊗[O] C →ₐc[k] k ⊗[O] K := Bialgebra.TensorProduct.map (BialgHom.id k k) q with hq'def
  have hψ'fun : ∀ z, ψ' z = LinearMap.lTensor k ((ψ : B →ₐc[O] C) : B →ₗ[O] C) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rw [hψ'def, Bialgebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hinj : Function.Injective ψ' := hψk

  have hqψ : ∀ b : B, q (ψ b) = algebraMap O K (Coalgebra.counit b) := by
    intro b
    have hmem : ψ b - algebraMap O C (Coalgebra.counit b) ∈ RingHom.ker (q : C →+* K) := by
      rw [hkerq]
      have : ψ b - algebraMap O C (Coalgebra.counit b) = ψ (b - algebraMap O B (Coalgebra.counit b)) := by
        rw [map_sub, AlgHomClass.commutes]
      rw [this]
      apply Ideal.mem_map_of_mem
      rw [RingHom.mem_ker]
      show Coalgebra.counit (b - algebraMap O B (Coalgebra.counit b)) = 0
      rw [map_sub, Bialgebra.counit_algebraMap, sub_self]
    have h2 : q (ψ b - algebraMap O C (Coalgebra.counit b)) = 0 := hmem
    rw [map_sub, sub_eq_zero] at h2
    rw [h2]
    exact AlgHomClass.commutes q _
  have hq'ψ' : ((q' : k ⊗[O] C →ₐc[k] k ⊗[O] K).comp ψ' : k ⊗[O] B →ₐ[k] k ⊗[O] K) =
      (Algebra.ofId k (k ⊗[O] K)).comp (Bialgebra.counitAlgHom k (k ⊗[O] B)) := by
    apply AlgHom.ext
    intro z
    show q' (ψ' z) = algebraMap k (k ⊗[O] K) (Coalgebra.counit (R := k) z)
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      rw [hψ'def, Bialgebra.TensorProduct.map_tmul, hq'def, Bialgebra.TensorProduct.map_tmul, hqψ,
        TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self_apply]
      show a ⊗ₜ[O] algebraMap O K (Coalgebra.counit b) = (Coalgebra.counit b • a) ⊗ₜ[O] (1 : K)
      rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hψ'mem : ∀ z, ψ' z ∈ hopfKer q' := fun z => apply_mem_hopfKer_of_comp_eq ψ' q' hq'ψ' z
  have hfmem : ∀ x, f x ∈ hopfKer q' := fun x => apply_mem_hopfKer_of_comp_eq f q' hf x

  have hq'surj : Function.Surjective q' := by
    have : ∀ z, q' z = LinearMap.lTensor k ((q : C →ₐc[O] K) : C →ₗ[O] K) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a b => rw [hq'def, Bialgebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    intro w
    obtain ⟨z, hz⟩ := LinearMap.lTensor_surjective k hq w
    exact ⟨z, (this z).trans hz⟩
  obtain ⟨-, -, -, hst⟩ := HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective q' hq'surj
  have hdimK : Module.finrank k (k ⊗[O] K) = Module.finrank O K := Module.finrank_baseChange
  have hdimC : Module.finrank k (k ⊗[O] C) = Module.finrank O C := Module.finrank_baseChange
  have hdimB : Module.finrank k (k ⊗[O] B) = Module.finrank O B := Module.finrank_baseChange
  haveI : Nontrivial (k ⊗[O] K) := (Bialgebra.counitAlgHom k (k ⊗[O] K)).toRingHom.domain_nontrivial
  have hKpos : 0 < Module.finrank k (k ⊗[O] K) := Module.finrank_pos
  have hker : Module.finrank k ↥(hopfKer q') = Module.finrank O B := by
    have h1 := hst ⊥
    rw [Module.rankAtStalk_eq_finrank_of_free] at h1
    have h2 : Module.finrank k ↥(hopfKer q') * Module.finrank k (k ⊗[O] K) =
        Module.finrank O B * Module.finrank k (k ⊗[O] K) := by
      rw [show (Module.finrank k ↥(hopfKer q') : ℕ) * Module.finrank k (k ⊗[O] K) = Module.finrank k (k ⊗[O] C) from h1,
        hdimC, hdimK, hrk]
    exact Nat.eq_of_mul_eq_mul_right hKpos h2
  have hrange : Subalgebra.toSubmodule ((ψ' : k ⊗[O] B →ₐ[k] k ⊗[O] C).range) = Subalgebra.toSubmodule (hopfKer q') := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨z, rfl⟩; exact hψ'mem z
    · rw [Subalgebra.finrank_toSubmodule, Subalgebra.finrank_toSubmodule, hker, ← hdimB]
      exact LinearMap.finrank_range_of_inj (f := (ψ' : k ⊗[O] B →ₐ[k] k ⊗[O] C).toLinearMap) hinj
  have hfrange : ∀ x, f x ∈ (ψ' : k ⊗[O] B →ₐ[k] k ⊗[O] C).range := by
    intro x
    have : f x ∈ Subalgebra.toSubmodule (hopfKer q') := hfmem x
    rw [← hrange] at this
    exact this

  let eψ : (k ⊗[O] B) ≃ₐ[k] ↥((ψ' : k ⊗[O] B →ₐ[k] k ⊗[O] C).range) :=
    AlgEquiv.ofInjective (ψ' : k ⊗[O] B →ₐ[k] k ⊗[O] C) hinj
  let g₀ : A →ₐ[k] k ⊗[O] B :=
    (eψ.symm : ↥((ψ' : k ⊗[O] B →ₐ[k] k ⊗[O] C).range) →ₐ[k] k ⊗[O] B).comp
      ((f : A →ₐ[k] k ⊗[O] C).codRestrict ((ψ' : k ⊗[O] B →ₐ[k] k ⊗[O] C).range) hfrange)
  have hg₀ : ∀ x, ψ' (g₀ x) = f x := by
    intro x
    have e1 : eψ (g₀ x) = ((f : A →ₐ[k] k ⊗[O] C).codRestrict ((ψ' : k ⊗[O] B →ₐ[k] k ⊗[O] C).range) hfrange) x :=
      AlgEquiv.apply_symm_apply eψ _
    have e2 := congrArg Subtype.val e1
    rw [AlgEquiv.ofInjective_apply] at e2
    exact e2

  have hcounit : (Bialgebra.counitAlgHom k (k ⊗[O] B)).comp g₀ = Bialgebra.counitAlgHom k A := by
    apply AlgHom.ext
    intro x
    rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      ← CoalgHomClass.counit_comp_apply ψ' (g₀ x), hg₀, CoalgHomClass.counit_comp_apply]

  have hinj2 : Function.Injective (TensorProduct.map (ψ' : k ⊗[O] B →ₗ[k] k ⊗[O] C)
      (ψ' : k ⊗[O] B →ₗ[k] k ⊗[O] C)) :=
    TensorProduct.map_injective_of_flat_flat _ _ hinj hinj
  have hcomul : (Algebra.TensorProduct.map g₀ g₀).comp (Bialgebra.comulAlgHom k A) =
      (Bialgebra.comulAlgHom k (k ⊗[O] B)).comp g₀ := by
    apply AlgHom.ext
    intro x
    apply hinj2
    show TensorProduct.map (ψ' : k ⊗[O] B →ₗ[k] k ⊗[O] C) (ψ' : k ⊗[O] B →ₗ[k] k ⊗[O] C)
        (Algebra.TensorProduct.map g₀ g₀ (Coalgebra.comul x)) =
      TensorProduct.map (ψ' : k ⊗[O] B →ₗ[k] k ⊗[O] C) (ψ' : k ⊗[O] B →ₗ[k] k ⊗[O] C)
        (Coalgebra.comul (g₀ x))
    rw [CoalgHomClass.map_comp_comul_apply ψ' (g₀ x), hg₀, ← CoalgHomClass.map_comp_comul_apply f x]

    have : ∀ z : A ⊗[k] A,
        TensorProduct.map (ψ' : k ⊗[O] B →ₗ[k] k ⊗[O] C) (ψ' : k ⊗[O] B →ₗ[k] k ⊗[O] C)
          (Algebra.TensorProduct.map g₀ g₀ z) = TensorProduct.map (f : A →ₗ[k] k ⊗[O] C) (f : A →ₗ[k] k ⊗[O] C) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul]
        show ψ' (g₀ a) ⊗ₜ[k] ψ' (g₀ b) = f a ⊗ₜ[k] f b
        rw [hg₀, hg₀]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    rw [this]
  refine ⟨BialgHom.ofAlgHom g₀ hcounit hcomul, ?_⟩
  apply BialgHom.coe_algHom_injective
  apply AlgHom.ext
  intro x
  exact hg₀ x

end S_HopfAlgebra_exists_bialgHom_comp_eq_of_injective_baseChange_of_finrank_eq_of_comp_eq_counit
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgHom_comp_eq_of_injective_baseChange_of_finrank_eq_of_comp_eq_counit (solution)
