-- Prove2me | solution 1 for HopfAlgebra.characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a86907f0-4d9b-55f2-a142-2da0679dfb64

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_FiniteFlat_SchematicClosure
import Definitions.Def_FiniteFlat_ClosureHopf
import Definitions.Def_HopfAlgebra_CharacterClosure
import Theorems.Thm_CartierDual_dualBaseChangeLin_bijective
import Theorems.Thm_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace P2MMultT4

open scoped TensorProduct

section Generic

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]
variable {G : Type*} [CommRing G] [Bialgebra R G]

theorem tensorToGenericFibre_comul (g : G) :
    tensorToGenericFibre R F (Coalgebra.comul (R := R) g)
      = Coalgebra.comul (R := F) ((1 : F) ⊗ₜ[R] g) := by
  rw [TensorProduct.comul_tmul]
  have h1 : Coalgebra.comul (R := F) (1 : F) = (1 : F) ⊗ₜ[F] (1 : F) := by simp
  rw [h1]
  induction (Coalgebra.comul (R := R) g) using TensorProduct.induction_on with
  | zero => rw [tensorToGenericFibre_zero, TensorProduct.tmul_zero, map_zero]
  | tmul g₁ g₂ =>
    rw [tensorToGenericFibre_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  | add x y hx hy => rw [tensorToGenericFibre_add, TensorProduct.tmul_add, map_add, hx, hy]

end Generic

section AntipodeVanishing

variable {F : Type*} [Field F] {X : Type*} [CommRing X] [HopfAlgebra F X]
variable {L : Type*} [CommRing L] [Algebra F L]

theorem antipode_mem_vanishingIdealOfPoints {S : Set (X →ₐ[F] L)}
    (hS : ∀ ν, ν ∈ S → ∃ ν' ∈ S, ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
    {a : X} (ha : a ∈ HopfAlgebra.vanishingIdealOfPoints S) :
    HopfAlgebraStruct.antipode (R := F) a ∈ HopfAlgebra.vanishingIdealOfPoints S := by
  intro ν hν
  obtain ⟨ν', hν', h⟩ := hS ν hν
  have := LinearMap.congr_fun h a
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply] at this
  rw [← this]
  exact ha ν' hν'

end AntipodeVanishing

section BC

variable {O : Type*} [CommRing O] {F : Type*} [Field F] [Algebra O F]
variable {A : Type*} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]

variable (hone : CartierDual.dualBaseChangeLin O F A 1 = 1)
  (hmul : ∀ x y : F ⊗[O] CartierDual O A,
      CartierDual.dualBaseChangeLin O F A (x * y)
        = CartierDual.dualBaseChangeLin O F A x * CartierDual.dualBaseChangeLin O F A y)

noncomputable def bcAlgHom : F ⊗[O] CartierDual O A →ₐ[F] CartierDual F (F ⊗[O] A) :=
  AlgHom.ofLinearMap (CartierDual.dualBaseChangeLin O F A) hone hmul

theorem bcAlgHom_apply (x : F ⊗[O] CartierDual O A) :
    bcAlgHom hone hmul x = CartierDual.dualBaseChangeLin O F A x := rfl

end BC

section Main

variable {O : Type*} [CommRing O] {F : Type*} [Field F] [Algebra O F]
variable {A : Type*} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type*} [Field L] [Algebra F L]
variable (hone : CartierDual.dualBaseChangeLin O F A 1 = 1)
  (hmul : ∀ x y : F ⊗[O] CartierDual O A,
      CartierDual.dualBaseChangeLin O F A (x * y)
        = CartierDual.dualBaseChangeLin O F A x * CartierDual.dualBaseChangeLin O F A y)

noncomputable def BS (B : Subalgebra F (CartierDual F (F ⊗[O] A))) :
    Subalgebra F (F ⊗[O] CartierDual O A) :=
  B.comap (bcAlgHom hone hmul)

theorem mem_BS_iff (B : Subalgebra F (CartierDual F (F ⊗[O] A))) (w : F ⊗[O] CartierDual O A) :
    w ∈ BS hone hmul B ↔ CartierDual.dualBaseChangeLin O F A w ∈ B := Iff.rfl

theorem image_BS (hbij : Function.Bijective (CartierDual.dualBaseChangeLin O F A))
    (B : Subalgebra F (CartierDual F (F ⊗[O] A))) :
    (CartierDual.dualBaseChangeLin O F A) '' (BS hone hmul B : Set (F ⊗[O] CartierDual O A))
      = (B : Set (CartierDual F (F ⊗[O] A))) := by
  ext θ
  constructor
  · rintro ⟨w, hw, rfl⟩; exact hw
  · intro hθ
    obtain ⟨w, rfl⟩ := hbij.2 θ
    exact ⟨w, hθ, rfl⟩

end Main

end P2MMultT4

theorem solution
    (O : Type) [CommRing O] (F : Type) [Field F] [Algebra O F]
    (A : Type) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
    [Coalgebra.IsCocomm O A]
    (L : Type) [Field L] [Algebra F L]
    (S : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L)))
    (hsep : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
      (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) :
    ((HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S) :
        Set (TensorProduct O F (CartierDual O A)))
        = {w | ∀ x ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S),
            CartierDual.dualBaseChangeLin O F A w x = 0}) ∧
    IsComulStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)) ∧
    IsAntipodeStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)) := by
  obtain ⟨hbij, hone, hmul, hcomul, hanti⟩ := CartierDual.dualBaseChangeLin_bijective O F A
  obtain ⟨B, hBC, hBcomul, hBanti⟩ :=
    CartierDual.exists_subalgebra_eq_annihilator_vanishingIdealOfPoints F (TensorProduct O F A) L S hsep hinv
  have hmemB : ∀ θ : CartierDual F (TensorProduct O F A),
      θ ∈ B ↔ ∀ a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S), θ a = 0 := by
    intro θ
    rw [← SetLike.mem_coe, hBC]
    rfl

  have hcarrier : {w : TensorProduct O F (CartierDual O A) |
        ∀ x ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S), CartierDual.dualBaseChangeLin O F A w x = 0}
      = (P2MMultT4.BS hone hmul B : Set (TensorProduct O F (CartierDual O A))) := by
    ext w
    rw [Set.mem_setOf_eq, SetLike.mem_coe, P2MMultT4.mem_BS_iff, hmemB]
  have heq : HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S) = P2MMultT4.BS hone hmul B := by
    show Algebra.adjoin F _ = _
    rw [hcarrier, Algebra.adjoin_eq]
  refine ⟨by rw [heq, hcarrier], ?_, ?_⟩
  ·
    rw [heq]
    intro g hg
    have hTinj : Function.Injective
        (TensorProduct.map (CartierDual.dualBaseChangeLin O F A) (CartierDual.dualBaseChangeLin O F A)) :=
      TensorProduct.map_injective_of_flat_flat _ _ hbij.1 hbij.1
    have hmem := hBcomul _ hg
    change Coalgebra.comul (R := F) (CartierDual.dualBaseChangeLin O F A ((1 : F) ⊗ₜ[O] g)) ∈ _ at hmem
    rw [← hcomul g] at hmem
    have himage : (TensorProduct.map (CartierDual.dualBaseChangeLin O F A) (CartierDual.dualBaseChangeLin O F A)) ''
          (Set.image2 (fun φ ψ => φ ⊗ₜ[F] ψ) (P2MMultT4.BS hone hmul B : Set (TensorProduct O F (CartierDual O A)))
            (P2MMultT4.BS hone hmul B : Set (TensorProduct O F (CartierDual O A))))
        = Set.image2 (fun φ ψ => φ ⊗ₜ[F] ψ) (B : Set (CartierDual F (TensorProduct O F A)))
            (B : Set (CartierDual F (TensorProduct O F A))) := by
      rw [← P2MMultT4.image_BS hone hmul hbij B, Set.image2_image_left, Set.image2_image_right, Set.image_image2]
      rfl
    have hspan : Submodule.span F (Set.image2 (fun φ ψ => φ ⊗ₜ[F] ψ) (B : Set (CartierDual F (TensorProduct O F A)))
          (B : Set (CartierDual F (TensorProduct O F A))))
        = (Submodule.span F (Set.image2 (fun φ ψ => φ ⊗ₜ[F] ψ)
            (P2MMultT4.BS hone hmul B : Set (TensorProduct O F (CartierDual O A)))
            (P2MMultT4.BS hone hmul B : Set (TensorProduct O F (CartierDual O A))))).map
            (TensorProduct.map (CartierDual.dualBaseChangeLin O F A) (CartierDual.dualBaseChangeLin O F A)) := by
      rw [Submodule.map_span, himage]
    rw [hspan, Submodule.mem_map] at hmem
    obtain ⟨y, hy, hyeq⟩ := hmem
    rw [← hTinj hyeq]
    exact hy
  ·
    rw [heq]
    intro g hg
    rw [mem_flatClosure_iff, P2MMultT4.mem_BS_iff, hmemB]
    intro x hx
    rw [hanti]
    exact (hmemB _).mp hg _ (P2MMultT4.antipode_mem_vanishingIdealOfPoints hinv hx)

end S_HopfAlgebra_characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable
end P2MW
export P2MW.S_HopfAlgebra_characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable (solution)
