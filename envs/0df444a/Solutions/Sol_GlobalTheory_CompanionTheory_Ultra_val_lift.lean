-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.val_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:06.504186+00:00
-- url     : https://prove2.me/submissions/0738f975-e863-4c56-940c-370aefb018c2

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_spec_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {R₀ R : Type} [CommRing R₀] [CommRing R] {X Y : Scheme.{0}}
  (f₀ : X ⟶ Spec (CommRingCat.of R₀))
variable {f₀}
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    {B L : Type} [CommRing B] [IsDomain B] [ValuationRing B] [Field L] [Algebra B L]
    [IsFractionRing B L] (ρ : R →+* B) (a₀ : Spec (CommRingCat.of L) ⟶ X)
    (H : a₀ ≫ f₀ = Spec.map (CommRingCat.ofHom ((algebraMap B L).comp (ρ.comp φ)))) :
    (∃ ℓ : Spec (CommRingCat.of B) ⟶ X, ℓ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ = a₀) ∧
    ∀ ℓ₁ ℓ₂ : Spec (CommRingCat.of B) ⟶ X,
      ℓ₁ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) →
      ℓ₂ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) →
      Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ₁ = a₀ →
      Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ₂ = a₀ → ℓ₁ = ℓ₂ := by
  let ã : Spec (CommRingCat.of L) ⟶ Y :=
    hpb.lift a₀ (Spec.map (CommRingCat.ofHom ((algebraMap B L).comp ρ)))
      (by rw [H, ← spec_comp])
  have ã₁ : ã ≫ π = a₀ := hpb.lift_fst _ _ _
  have ã₂ : ã ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap B L).comp ρ)) := hpb.lift_snd _ _ _
  let sq : ValuativeCommSq f :=
    { R := B, K := L, i₁ := ã, i₂ := Spec.map (CommRingCat.ofHom ρ),
      commSq := ⟨by rw [ã₂, spec_comp]⟩ }
  obtain ⟨u⟩ := hval sq
  refine ⟨?_, ?_⟩
  · let l := (u.default : sq.commSq.LiftStruct)
    have l₁ : Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ l.l = ã := l.fac_left
    have l₂ : l.l ≫ f = Spec.map (CommRingCat.ofHom ρ) := l.fac_right
    refine ⟨l.l ≫ π, ?_, ?_⟩
    · rw [Category.assoc, hpb.w, ← Category.assoc, l₂, spec_comp]
    · rw [← Category.assoc, l₁, ã₁]
  · intro ℓ₁ ℓ₂ e₁ e₂ d₁ d₂
    have mk : ∀ ℓ : Spec (CommRingCat.of B) ⟶ X,
        ℓ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) →
        Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ = a₀ →
        ∃ l : sq.commSq.LiftStruct, l.l ≫ π = ℓ := by
      intro ℓ e d
      let m : Spec (CommRingCat.of B) ⟶ Y :=
        hpb.lift ℓ (Spec.map (CommRingCat.ofHom ρ)) (by rw [e, spec_comp])
      have m₁ : m ≫ π = ℓ := hpb.lift_fst _ _ _
      have m₂ : m ≫ f = Spec.map (CommRingCat.ofHom ρ) := hpb.lift_snd _ _ _
      refine ⟨⟨m, ?_, m₂⟩, m₁⟩
      change Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ m = ã
      apply hpb.hom_ext
      · rw [Category.assoc, m₁, d, ã₁]
      · rw [Category.assoc, m₂, ã₂, spec_comp]
    obtain ⟨l₁, rfl⟩ := mk ℓ₁ e₁ d₁
    obtain ⟨l₂, rfl⟩ := mk ℓ₂ e₂ d₂
    rw [show l₁ = l₂ from (u.uniq l₁).trans (u.uniq l₂).symm]
end GlobalTheory.CompanionTheory.Ultra
