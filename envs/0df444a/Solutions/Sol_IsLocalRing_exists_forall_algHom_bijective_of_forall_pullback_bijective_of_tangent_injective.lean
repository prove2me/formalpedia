-- Prove2me | solution 1 for IsLocalRing.exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6c060bba-0ec8-5d95-9420-ab83aa364cef

import Mathlib
import Theorems.Thm_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective
import Theorems.Thm_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective

set_option autoImplicit false

universe u

open IsLocalRing in
theorem solution
    (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O]
    (F : ∀ (A : Type u) [CommRing A] [Algebra O A], (A →+* ResidueField O) → Type u)
    (Frel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O},
      F A resA → F A resA → Prop)
    (hrefl : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x : F A resA), Frel x x)
    (hsymm : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x y : F A resA), Frel x y → Frel y x)
    (htrans : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x y z : F A resA), Frel x y → Frel y z → Frel x z)
    (Fmap : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA → F A resA → F A' resA')
    (Fmap_rel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (x y : F A resA),
      Frel x y → Frel (Fmap f hf x) (Fmap f hf y))
    (Fmap_id : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (h : resA.comp (AlgHom.id O A).toRingHom = resA) (x : F A resA), Frel (Fmap (AlgHom.id O A) h x) x)
    (Fmap_comp : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      {A'' : Type u} [CommRing A''] [Algebra O A''] {resA'' : A'' →+* ResidueField O}
      (f : A →ₐ[O] A') (g : A' →ₐ[O] A'') (hf : resA'.comp f.toRingHom = resA)
      (hg : resA''.comp g.toRingHom = resA') (hgf : resA''.comp (g.comp f).toRingHom = resA)
      (x : F A resA), Frel (Fmap (g.comp f) hgf x) (Fmap g hg (Fmap f hf x)))

    (x₀ : F (ResidueField O) (RingHom.id (ResidueField O)))
    (hx₀ : ∀ x : F (ResidueField O) (RingHom.id (ResidueField O)), Frel x x₀)

    (hglue : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
        (resB : B →+* ResidueField O), Function.Surjective resB →
        resB.comp (algebraMap O B) = residue O →
      ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
        (resA' : A' →+* ResidueField O), Function.Surjective resA' →
        resA'.comp (algebraMap O A') = residue O →
      ∀ (A'' : Type u) [CommRing A''] [IsLocalRing A''] [IsArtinianRing A''] [Algebra O A'']
        (resA'' : A'' →+* ResidueField O), Function.Surjective resA'' →
        resA''.comp (algebraMap O A'') = residue O →
      ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
      ∀ (p' : B →ₐ[O] A') (hp' : resA'.comp p'.toRingHom = resB)
        (p'' : B →ₐ[O] A'') (hp'' : resA''.comp p''.toRingHom = resB)
        (q' : A' →ₐ[O] A) (hq' : resA.comp q'.toRingHom = resA')
        (q'' : A'' →ₐ[O] A) (hq'' : resA.comp q''.toRingHom = resA''),
        q'.comp p' = q''.comp p'' →
        (∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'') →
        Function.Surjective q'' →
        (∀ (x' : F A' resA') (x'' : F A'' resA''), Frel (Fmap q' hq' x') (Fmap q'' hq'' x'') →
            ∃ y : F B resB, Frel (Fmap p' hp' y) x' ∧ Frel (Fmap p'' hp'' y) x'') ∧
        (∀ (y₁ y₂ : F B resB), Frel (Fmap p' hp' y₁) (Fmap p' hp' y₂) →
            Frel (Fmap p'' hp'' y₁) (Fmap p'' hp'' y₂) → Frel y₁ y₂))

    (r : ℕ)
    (e : F (DualNumber (ResidueField O))
        (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom → (Fin r → ResidueField O))
    (he_rel : ∀ x y, Frel x y → e x = e y)
    (he_inj : ∀ x y, e x = e y → Frel x y)
    (he_smul : ∀ (c : ResidueField O)
        (μ : DualNumber (ResidueField O) →ₐ[O] DualNumber (ResidueField O))
        (hμ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp μ.toRingHom =
          (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom),
        (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
        ∀ x, e (Fmap μ hμ x) = c • e x)
    (he_add : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
        (resB : B →+* ResidueField O), Function.Surjective resB →
        resB.comp (algebraMap O B) = residue O →
        ∀ (p₁ p₂ σ : B →ₐ[O] DualNumber (ResidueField O))
          (hp₁ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
            p₁.toRingHom = resB)
          (hp₂ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
            p₂.toRingHom = resB)
          (hσ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
            σ.toRingHom = resB),
        (∀ b₁ b₂ : B, p₁ b₁ = p₁ b₂ → p₂ b₁ = p₂ b₂ → b₁ = b₂) →
        (∀ t₁ t₂ : DualNumber (ResidueField O), TrivSqZeroExt.fst t₁ = TrivSqZeroExt.fst t₂ →
            ∃ b : B, p₁ b = t₁ ∧ p₂ b = t₂) →
        (∀ b : B, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b)) →
        ∀ y : F B resB, e (Fmap σ hσ y) = e (Fmap p₁ hp₁ y) + e (Fmap p₂ hp₂ y)) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R) (_ : Algebra O R)
      (_ : IsAdicComplete (maximalIdeal R) R)
      (resR : R →+* ResidueField O) (_ : resR.comp (algebraMap O R) = residue O)
      (β : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O → F A resA → (R →ₐ[O] A)),
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (x : F A resA),
        resA.comp (β A resA hs hc x).toRingHom = resR) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (x y : F A resA),
        Frel x y → β A resA hs hc x = β A resA hs hc y) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O)
          (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
          (resA' : A' →+* ResidueField O) (hs' : Function.Surjective resA')
          (hc' : resA'.comp (algebraMap O A') = residue O)
          (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (x : F A resA),
        β A' resA' hs' hc' (Fmap f hf x) = f.comp (β A resA hs hc x)) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (x y : F A resA),
        β A resA hs hc x = β A resA hs hc y → Frel x y) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (χ : R →ₐ[O] A),
        resA.comp χ.toRingHom = resR → ∃ x : F A resA, β A resA hs hc x = χ) := by

  obtain ⟨R, _instR₁, _instR₂, _instR₃, _instR₄, _instR₅, resR, hresR, Ξ, hnat, hinj, hsurj, hlift⟩ :=
    IsLocalRing.exists_hull_of_forall_pullback_surjective_of_tangent_injective O F Frel hrefl hsymm htrans
      Fmap Fmap_rel Fmap_id Fmap_comp x₀ hx₀
      (fun B _ _ _ _ resB hsB hcB A' _ _ _ _ resA' hsA' hcA' A'' _ _ _ _ resA'' hsA'' hcA''
          A _ _ _ _ resA hsA hcA p' hp' p'' hp'' q' hq' q'' hq'' hcomm hcart hsq =>
        (hglue B resB hsB hcB A' resA' hsA' hcA' A'' resA'' hsA'' hcA'' A resA hsA hcA p' hp' p'' hp''
          q' hq' q'' hq'' hcomm hcart hsq).1)
      r e he_rel he_inj he_smul he_add

  obtain ⟨β, h₁, h₂, h₃, h₄, h₅⟩ :=
    IsLocalRing.exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull O F Frel hrefl hsymm
      htrans Fmap Fmap_rel Fmap_id Fmap_comp x₀ hx₀ hglue R resR hresR Ξ hnat hinj hsurj hlift
  exact ⟨R, _instR₁, _instR₂, _instR₃, _instR₄, _instR₅, resR, hresR, β, h₁, h₂, h₃, h₄, h₅⟩

end S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective
end P2MW
export P2MW.S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective (solution)
