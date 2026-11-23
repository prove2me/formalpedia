-- Prove2me | solution 1 for GlobalTheory.exists_lift_of_smooth_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:54.369903+00:00
-- url     : https://prove2.me/submissions/6bf6543a-aebb-4098-90f4-3d2e298e32fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S)
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution [Smooth f] {U : S.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) {B C : CommRingCat.{u}}
    (π : B ⟶ C) (s : Spec B ⟶ S) (x₀ : Spec C ⟶ X) (h : x₀ ≫ f = Spec.map π ≫ s)
    (hs : Set.range s ⊆ U) (hx : Set.range x₀ ⊆ V)
    (H : ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A]
      [Algebra R B] [Algebra R C] (π' : B →ₐ[R] C), (∀ b, π' b = π b) →
      ∀ φ : A →ₐ[R] C, ∃ ψ : A →ₐ[R] B, π'.comp ψ = φ) :
    ∃ x : Spec B ⟶ X, Spec.map π ≫ x = x₀ ∧ x ≫ f = s := by
  have hsm : (f.appLE U V hVU).hom.Smooth := HasRingHomProperty.appLE @Smooth f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  have hxV : Set.range x₀.base ⊆ Set.range hV.fromSpec.base := by rw [hV.range_fromSpec]; exact hx
  have hsU : Set.range s.base ⊆ Set.range hU.fromSpec.base := by rw [hU.range_fromSpec]; exact hs
  set a : Γ(X, V) ⟶ C := Spec.preimage (IsOpenImmersion.lift hV.fromSpec x₀ hxV) with ha_def
  set b : Γ(S, U) ⟶ B := Spec.preimage (IsOpenImmersion.lift hU.fromSpec s hsU) with hb_def
  have ha : Spec.map a ≫ hV.fromSpec = x₀ := by
    rw [ha_def, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hb : Spec.map b ≫ hU.fromSpec = s := by
    rw [hb_def, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hab : f.appLE U V hVU ≫ a = b ≫ π := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, hb, reassoc_of% ha, h]
  letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  letI : Algebra Γ(S, U) B := b.hom.toAlgebra
  letI : Algebra Γ(S, U) C := (b ≫ π).hom.toAlgebra
  haveI : Algebra.Smooth Γ(S, U) Γ(X, V) := hsm
  let π' : B →ₐ[Γ(S, U)] C := { π.hom with commutes' := fun _ => rfl }
  let φ : Γ(X, V) →ₐ[Γ(S, U)] C :=
    { a.hom with commutes' := fun r => congrArg (fun k => k.hom r) hab }
  obtain ⟨ψ, hψ⟩ := H Γ(S, U) Γ(X, V) π' (fun _ => rfl) φ
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← ha]
    congr 2
    ext y
    exact congrArg (fun k => k y) hψ
  · rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, ← Category.assoc,
      ← Spec.map_comp, ← hb]
    congr 2
    ext r
    exact ψ.commutes r
end _root_.GlobalTheory
end GlobalTheory
