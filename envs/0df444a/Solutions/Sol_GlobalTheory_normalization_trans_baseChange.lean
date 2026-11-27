-- Prove2me | solution 1 for GlobalTheory.normalization_trans_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:24.654338+00:00
-- url     : https://prove2.me/submissions/adb4a1b0-1f06-40de-b2ad-e3237349405c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_isPullback_normalizationMap_of_isLocalization
import Theorems.Thm_GlobalTheory_isIso_toNormalization_morphismRestrict
import Theorems.Thm_GlobalTheory_flat_fromNormalization_comp
import Theorems.Thm_GlobalTheory_eq_normalizationAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] PreservesNormalization.isIso_normalizationPullback
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] :
    (∀ {T : Scheme.{u}} (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂] [QuasiCompact f₁]
      [QuasiSeparated f₁], f = f₁ ≫ f₂ → ∃ e : f₁.normalization ≅ f.normalization,
        f₁.toNormalization ≫ e.hom = f.toNormalization ∧
        e.hom ≫ f.fromNormalization = f₁.fromNormalization ≫ f₂) ∧
    (∀ (V : Y.Opens) [IsFinite (f ∣_ V)],
      IsIso (f.toNormalization ∣_ (f.fromNormalization ⁻¹ᵁ V))) ∧
    (∀ (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
      (s : Y ⟶ Spec (.of R)) (c : X ⟶ Spec (.of K)),
      f ≫ s = c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) →
        Flat (f.fromNormalization ≫ s)) ∧
    (∀ {X' : Scheme.{u}} (f' : X' ⟶ Y) [QuasiCompact f'] [QuasiSeparated f'] (a : X ⟶ X'),
      a ≫ f' = f → ∃! m : f.normalization ⟶ f'.normalization,
        f.toNormalization ≫ m = a ≫ f'.toNormalization ∧
        m ≫ f'.fromNormalization = f.fromNormalization) ∧
    (∀ (G : Type v) [Group G] [Finite G] (ρ : G →* Aut X), (∀ g, (ρ g).hom ≫ f = f) →
      (∃! τ : G →* Aut f.normalization, ∀ g,
        f.toNormalization ≫ (τ g).hom = (ρ g).hom ≫ f.toNormalization ∧
        (τ g).hom ≫ f.fromNormalization = f.fromNormalization) ∧
      ∀ (τ : G →* Aut f.normalization), (∀ g,
        f.toNormalization ≫ (τ g).hom = (ρ g).hom ≫ f.toNormalization ∧
        (τ g).hom ≫ f.fromNormalization = f.fromNormalization) →
      ∀ {X' : Scheme.{u}} (f' : X' ⟶ Y) [QuasiCompact f'] [QuasiSeparated f'] (π : X ⟶ X'),
        (∀ g, (ρ g).hom ≫ π = π) →
        (∀ W : X'.Opens, Function.Injective (π.app W) ∧
          Set.range (π.app W) = {s | IsInvariantSection ρ (π ⁻¹ᵁ W) s}) →
        ∀ q : f.normalization ⟶ f'.normalization,
          f.toNormalization ≫ q = π ≫ f'.toNormalization →
          q ≫ f'.fromNormalization = f.fromNormalization →
          (∀ g, (τ g).hom ≫ q = q) ∧ IsIntegralHom q ∧ Surjective q ∧
            (∀ x y, q x = q y ↔ ∃ g, (τ g).hom x = y) ∧
            ∀ W : f'.normalization.Opens, Function.Injective (q.app W) ∧
              Set.range (q.app W) = {s | IsInvariantSection τ (q ⁻¹ᵁ W) s}) ∧
    (∀ (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (M : Submonoid R)
      [IsLocalization M R'] {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') [QuasiCompact f']
      [QuasiSeparated f'] (a : X' ⟶ X) (b : Y' ⟶ Y) (t : Y' ⟶ Spec (.of R'))
      (s : Y ⟶ Spec (.of R)), IsPullback b t s (Spec.map (CommRingCat.ofHom (algebraMap R R'))) →
      IsPullback a f' f b → ∃ m : f'.normalization ⟶ f.normalization,
        f'.toNormalization ≫ m = a ≫ f.toNormalization ∧
        IsPullback m f'.fromNormalization f.fromNormalization b) ∧
    (∀ {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') [QuasiCompact f'] [QuasiSeparated f'] (a : X' ⟶ X)
      (b : Y' ⟶ Y) [Smooth b], IsPullback a f' f b →
      ∃ m : f'.normalization ⟶ f.normalization,
        f'.toNormalization ≫ m = a ≫ f.toNormalization ∧
        IsPullback m f'.fromNormalization f.fromNormalization b) := by
  refine ⟨fun f₁ f₂ _ _ _ H ↦ ⟨normalizationTransIso f₁ f₂ f H, by simp, by simp⟩,
    fun V _ ↦ isIso_toNormalization_morphismRestrict f V,
    fun R K _ _ _ _ _ s c hc ↦ flat_fromNormalization_comp f K s c hc,
    fun f' _ _ a H ↦ ⟨normalizationMap f f' a (𝟙 Y) (by simp [H]), ⟨by simp, by simp⟩,
      fun m hm ↦ eq_normalizationMap f f' _ _ _ hm.1 (by simp [hm.2])⟩,
    fun G _ _ ρ hρ ↦ ?_,
    fun R R' _ _ _ M _ _ _ f' _ _ a b t s hb h ↦
      ⟨_, by simp, isPullback_normalizationMap_of_isLocalization M hb h⟩,
    fun f' _ _ a b _ h ↦ ⟨_, by simp, isPullback_normalizationMap h⟩⟩
  have huniq (τ : G →* Aut f.normalization) (hτ : ∀ g,
      f.toNormalization ≫ (τ g).hom = (ρ g).hom ≫ f.toNormalization ∧
      (τ g).hom ≫ f.fromNormalization = f.fromNormalization) :
      τ = normalizationActionOver f ρ hρ :=
    eq_normalizationAction f ρ 1 _ τ (fun g ↦ (hτ g).1)
      fun g ↦ (hτ g).2.trans (Category.comp_id _).symm
  refine ⟨⟨normalizationActionOver f ρ hρ, fun g ↦ ⟨by simp, by simp⟩, huniq⟩,
    fun τ hτ X' f' _ _ π hπ hW q hq₁ hq₂ ↦ ?_⟩
  have hf : π ≫ f' = f ≫ 𝟙 Y := by
    rw [← f'.toNormalization_fromNormalization, ← reassoc_of% hq₁, hq₂]
    simp
  obtain rfl := huniq τ hτ
  obtain rfl := eq_normalizationMap f f' π (𝟙 Y) hf hq₁ (by simp [hq₂])
  have : QuasiCompact (π ≫ f') := by rw [hf]; infer_instance
  have : QuasiCompact π := .of_comp π f'
  have : IsSchemeTheoreticallyDominant π := ⟨Scheme.IdealSheafData.ext (funext fun W ↦ by
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact (hW W).1)⟩
  refine normalization_quotient f f' π hf ρ hπ hρ fun y ↦ ?_
  obtain ⟨_, ⟨W, hW', rfl⟩, hy, -⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  exact ⟨W, hW', hy, fun s hs ↦ (hW W).2.ge hs⟩
end GlobalTheory
