-- Prove2me | solution 1 for HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/90100871-ea89-539b-9ea0-51e199547536

import Mathlib
import Definitions.Def_HopfAlgebra_HopfTower
import Theorems.Thm_Algebra_exists_subalgebra_etale_forall_le_forall_baseChange_le_forall_tensorProduct_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_field

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace HopfAlgebra
p2m_export "HopfAlgebra" "ofAlgHom IsHopfTower IsHopfTower.toBialgHom IsHopfSubalgebra IsHopfSubalgebra.ι₂ IsHopfSubalgebra.range_ι₂ IsHopfSubalgebra.ι₂_injective HopfTower.antipodeAlgHom"
namespace F0Reduce
p2m_open "HopfAlgebra"

open Coalgebra Bialgebra

section EtaleImage

variable {K : Type*} [Field K] {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

theorem etale_range [Module.Finite K A] [Algebra.Etale K A] (f : A →ₐ[K] B) : Algebra.Etale K f.range := by
  have hsurj : Function.Surjective f.rangeRestrict := fun ⟨y, x, hx⟩ => ⟨x, Subtype.ext hx⟩
  haveI : Module.Finite K f.range := Module.Finite.of_surjective f.rangeRestrict.toLinearMap hsurj
  haveI : Algebra.FormallyUnramified K f.range := Algebra.FormallyUnramified.of_surjective f.rangeRestrict hsurj
  haveI : Algebra.FormallyEtale K f.range := Algebra.FormallyEtale.of_formallyUnramified_of_field K f.range
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end EtaleImage

section Inj

variable {K : Type*} [Field K]

theorem map_injective_of_injective {M N M' N' : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N']
    (f : M →ₗ[K] M') (g : N →ₗ[K] N') (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  rw [← LinearMap.rTensor_comp_lTensor]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ hf).comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ hg)

end Inj

section Main

variable (k : Type u) [Field k] (L : Type v) [CommRing L] [HopfAlgebra k L] [Coalgebra.IsCocomm k L]
  [Module.Finite k L]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main :
    ∃ (E : Type v) (_ : CommRing E) (_ : HopfAlgebra k E) (_ : Coalgebra.IsCocomm k E)
      (_ : Module.Finite k E) (ι : E →ₐc[k] L),
      Function.Injective ι ∧
      Algebra.Etale k E ∧
      (∀ (E' : Type v) [CommRing E'] [HopfAlgebra k E'] [Coalgebra.IsCocomm k E']
          [Module.Finite k E'] [Algebra.Etale k E']
          (f : E' →ₐc[k] L), ∃! g : E' →ₐc[k] E, ι.comp g = f) ∧
      (∀ (K : Type u) [Field K] [Algebra k K]
          (E' : Type v) [CommRing E'] [HopfAlgebra K E'] [Coalgebra.IsCocomm K E']
          [Module.Finite K E'] [Algebra.Etale K E']
          (f : E' →ₐc[K] K ⊗[k] L),
            ∃! g : E' →ₐc[K] K ⊗[k] E,
              (Bialgebra.TensorProduct.map (BialgHom.id K K) ι).comp g = f) := by
  classical
  obtain ⟨P, hPet, hmax, hbf, hprod⟩ :=
    Algebra.exists_subalgebra_etale_forall_le_forall_baseChange_le_forall_tensorProduct_le k L
  haveI : Algebra.Etale k P := hPet

  have hK : HopfAlgebra.IsHopfSubalgebra k P := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    ·
      have hle := hprod L P hPet hmax ((Bialgebra.comulAlgHom k L).comp P.val).range
        (etale_range ((Bialgebra.comulAlgHom k L).comp P.val))
      have hmem : comul (R := k) x ∈ (Algebra.TensorProduct.map P.val P.val).range :=
        hle ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨y, hy⟩ := hmem
      rw [← HopfAlgebra.IsHopfSubalgebra.range_ι₂]
      exact ⟨y, hy⟩
    ·
      have hle := hmax ((HopfAlgebra.HopfTower.antipodeAlgHom k L).comp P.val).range
        (etale_range ((HopfAlgebra.HopfTower.antipodeAlgHom k L).comp P.val))
      exact hle ⟨⟨x, hx⟩, rfl⟩
  letI : HopfAlgebra k P := hK.hopfAlgebra
  haveI : HopfAlgebra.IsHopfTower k P L := hK.isHopfTower
  let ι : P →ₐc[k] L := HopfAlgebra.IsHopfTower.toBialgHom k P L
  have hι : ∀ s : P, ι s = (s : L) := fun s => rfl
  have hιalg : (ι : P →ₐ[k] L) = P.val := by ext s; rfl

  haveI : Coalgebra.IsCocomm k P := by
    refine ⟨?_⟩
    ext s
    apply HopfAlgebra.IsHopfSubalgebra.ι₂_injective (K := P)
    change HopfAlgebra.IsHopfSubalgebra.ι₂ P (TensorProduct.comm k P P (comul (R := k) s)) =
      HopfAlgebra.IsHopfSubalgebra.ι₂ P (comul (R := k) s)
    rw [hK.ι₂_comul]
    have hnat : ∀ z : P ⊗[k] P, HopfAlgebra.IsHopfSubalgebra.ι₂ P (TensorProduct.comm k P P z) =
        TensorProduct.comm k L L (HopfAlgebra.IsHopfSubalgebra.ι₂ P z) := by
      intro z
      induction z with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y => simp
    rw [hnat, hK.ι₂_comul, Coalgebra.comm_comul]
  haveI : Module.Finite k P := Module.Finite.of_injective P.val.toLinearMap Subtype.val_injective
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, ι, Subtype.val_injective, hPet,
    ?_, ?_⟩
  ·
    intro E' _ _ _ _ _ f
    have hle : (f : E' →ₐ[k] L).range ≤ P := hmax _ (etale_range (f : E' →ₐ[k] L))
    have hmem : ∀ x, f x ∈ P := fun x => hle ⟨x, rfl⟩
    let g₀ : E' →ₐ[k] P := (f : E' →ₐ[k] L).codRestrict P hmem
    have hg₀ : ∀ x, ((g₀ x : P) : L) = f x := fun x => rfl
    have hcounit : (Bialgebra.counitAlgHom k P).comp g₀ = Bialgebra.counitAlgHom k E' := by
      ext x
      change counit (R := k) (g₀ x) = counit (R := k) x
      rw [hK.counit_coe, hg₀, CoalgHomClass.counit_comp_apply]
    have hcomul : (Algebra.TensorProduct.map g₀ g₀).comp (Bialgebra.comulAlgHom k E') =
        (Bialgebra.comulAlgHom k P).comp g₀ := by
      ext x
      apply HopfAlgebra.IsHopfSubalgebra.ι₂_injective (K := P)
      change HopfAlgebra.IsHopfSubalgebra.ι₂ P (Algebra.TensorProduct.map g₀ g₀ (comul (R := k) x)) =
        HopfAlgebra.IsHopfSubalgebra.ι₂ P (comul (R := k) (g₀ x))
      rw [hK.ι₂_comul, hg₀, ← CoalgHomClass.map_comp_comul_apply]
      change (Algebra.TensorProduct.map P.val P.val) (Algebra.TensorProduct.map g₀ g₀ (comul (R := k) x)) = _
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
      rfl
    let g : E' →ₐc[k] P := BialgHom.ofAlgHom g₀ hcounit hcomul
    have hg : ∀ x, ((g x : P) : L) = f x := fun x => rfl
    refine ⟨g, ?_, ?_⟩
    · ext x
      exact hg x
    · intro g' hg'
      ext x
      change ((g' x : P) : L) = ((g x : P) : L)
      rw [hg, ← hg']
      rfl
  ·
    intro K _ _ E' _ _ _ _ _ f
    let j : K ⊗[k] P →ₐ[K] K ⊗[k] L := Algebra.TensorProduct.map (AlgHom.id K K) P.val
    let jb : K ⊗[k] P →ₐc[K] K ⊗[k] L := Bialgebra.TensorProduct.map (BialgHom.id K K) ι
    have hjb : ∀ z, jb z = j z := by
      intro z
      change (jb : K ⊗[k] P →ₐ[K] K ⊗[k] L) z = j z
      rw [Bialgebra.TensorProduct.map_toAlgHom, hιalg]
      rfl
    have hjlin : ∀ z, j z = (P.val.toLinearMap.lTensor K) z := by
      intro z
      induction z with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y => rfl
    have hj : Function.Injective j := by
      intro a b h
      rw [hjlin, hjlin] at h
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective h

    have hle : (f : E' →ₐ[K] K ⊗[k] L).range ≤ j.range :=
      hbf K (f : E' →ₐ[K] K ⊗[k] L).range (etale_range (f : E' →ₐ[K] K ⊗[k] L))
    have hmem : ∀ x, f x ∈ j.range := fun x => hle ⟨x, rfl⟩
    let e : K ⊗[k] P ≃ₐ[K] j.range := AlgEquiv.ofInjective j hj
    let g₀ : E' →ₐ[K] K ⊗[k] P := e.symm.toAlgHom.comp ((f : E' →ₐ[K] K ⊗[k] L).codRestrict j.range hmem)
    have hjg : ∀ x, j (g₀ x) = f x := by
      intro x
      have h1 : (e (g₀ x) : K ⊗[k] L) = j (g₀ x) := rfl
      rw [← h1]
      change (e (e.symm ⟨f x, hmem x⟩) : K ⊗[k] L) = f x
      rw [AlgEquiv.apply_symm_apply]
    have hjcomp : j.comp g₀ = (f : E' →ₐ[K] K ⊗[k] L) := AlgHom.ext hjg

    let J : (K ⊗[k] P) ⊗[K] (K ⊗[k] P) →ₐ[K] (K ⊗[k] L) ⊗[K] (K ⊗[k] L) := Algebra.TensorProduct.map j j
    have hJ : Function.Injective J :=
      map_injective_of_injective j.toLinearMap j.toLinearMap hj hj
    have hJb : (Algebra.TensorProduct.map (jb : K ⊗[k] P →ₐ[K] K ⊗[k] L) (jb : K ⊗[k] P →ₐ[K] K ⊗[k] L)) = J := by
      have : (jb : K ⊗[k] P →ₐ[K] K ⊗[k] L) = j := AlgHom.ext hjb
      rw [this]
    have hcounit : (Bialgebra.counitAlgHom K (K ⊗[k] P)).comp g₀ = Bialgebra.counitAlgHom K E' := by
      ext x
      change counit (R := K) (g₀ x) = counit (R := K) x
      have h1 := CoalgHomClass.counit_comp_apply jb (g₀ x)
      rw [hjb, hjg, CoalgHomClass.counit_comp_apply] at h1
      exact h1.symm
    have hcomul : (Algebra.TensorProduct.map g₀ g₀).comp (Bialgebra.comulAlgHom K E') =
        (Bialgebra.comulAlgHom K (K ⊗[k] P)).comp g₀ := by
      ext x
      apply hJ
      change J (Algebra.TensorProduct.map g₀ g₀ (comul (R := K) x)) = J (comul (R := K) (g₀ x))
      conv_rhs => rw [← hJb]
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, hjcomp]
      change Algebra.TensorProduct.map (f : E' →ₐ[K] K ⊗[k] L) (f : E' →ₐ[K] K ⊗[k] L) (comul (R := K) x) =
        Algebra.TensorProduct.map (jb : K ⊗[k] P →ₐ[K] K ⊗[k] L) (jb : K ⊗[k] P →ₐ[K] K ⊗[k] L)
          (comul (R := K) (g₀ x))
      have h1 := CoalgHomClass.map_comp_comul_apply f x
      have h2 := CoalgHomClass.map_comp_comul_apply jb (g₀ x)
      rw [hjb, hjg] at h2
      exact (h1.trans h2.symm)
    let g : E' →ₐc[K] K ⊗[k] P := BialgHom.ofAlgHom g₀ hcounit hcomul
    have hg : ∀ x, jb (g x) = f x := fun x => (hjb _).trans (hjg x)
    refine ⟨g, ?_, ?_⟩
    · ext x
      exact hg x
    · intro g' hg'
      ext x
      apply hj
      rw [← hjb, ← hjb]
      change jb (g' x) = jb (g x)
      rw [hg, ← hg']
      rfl

end Main

end HopfAlgebra.F0Reduce

theorem solution
    (k : Type u) [Field k]
    (L : Type v) [CommRing L] [HopfAlgebra k L] [Coalgebra.IsCocomm k L] [Module.Finite k L] :
    ∃ (E : Type v) (_ : CommRing E) (_ : HopfAlgebra k E) (_ : Coalgebra.IsCocomm k E)
      (_ : Module.Finite k E) (ι : E →ₐc[k] L),
      Function.Injective ι ∧

      Algebra.Etale k E ∧

      (∀ (E' : Type v) [CommRing E'] [HopfAlgebra k E'] [Coalgebra.IsCocomm k E']
          [Module.Finite k E'] [Algebra.Etale k E']
          (f : E' →ₐc[k] L), ∃! g : E' →ₐc[k] E, ι.comp g = f) ∧

      (∀ (K : Type u) [Field K] [Algebra k K]
          (E' : Type v) [CommRing E'] [HopfAlgebra K E'] [Coalgebra.IsCocomm K E']
          [Module.Finite K E'] [Algebra.Etale K E']
          (f : E' →ₐc[K] K ⊗[k] L),
            ∃! g : E' →ₐc[K] K ⊗[k] E,
              (Bialgebra.TensorProduct.map (BialgHom.id K K) ι).comp g = f) :=
  HopfAlgebra.F0Reduce.main k L

end S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_field
end P2MW
export P2MW.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_field (solution)
