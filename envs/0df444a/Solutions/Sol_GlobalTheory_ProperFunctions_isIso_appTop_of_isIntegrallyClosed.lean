-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_appTop_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:28:15.061747+00:00
-- url     : https://prove2.me/submissions/c1531d7e-6fe4-4438-8d89-fa95582b2e4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_injective_appTop_of_isPullback
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {R K : Type u} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] {p : X ⟶ Spec (.of R)}
    {g : Y ⟶ X} {q : Y ⟶ Spec (.of K)}
    (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    [Flat p] [UniversallyClosed p] [GeometricallyIntegral q] : IsIso p.appTop := by
  have : UniversallyClosed q := MorphismProperty.of_isPullback H ‹_›
  have := isIso_appTop_of_field q
  let F := (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop
  let G := g.appTop ≫ inv q.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  have hFG : F ≫ G = CommRingCat.ofHom (algebraMap R K) := by
    simp only [F, G, Category.assoc]
    rw [← Category.assoc p.appTop, ← Scheme.Hom.comp_appTop, H.w, Scheme.Hom.comp_appTop,
      Category.assoc, IsIso.hom_inv_id_assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hg : Function.Injective g.appTop := by
    refine injective_appTop_of_isPullback H ?_
    have : Mono (CommRingCat.ofHom (algebraMap R K)) :=
      ConcreteCategory.mono_of_injective _ (IsFractionRing.injective R K)
    have : Mono ((Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop ≫
        (Scheme.ΓSpecIso (.of K)).hom) := by
      rw [Scheme.ΓSpecIso_naturality]; infer_instance
    have := mono_of_mono (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop
      (Scheme.ΓSpecIso (.of K)).hom
    exact ConcreteCategory.injective_of_mono_of_preservesPullback _
  have hG : Function.Injective G := by
    have : Mono g.appTop := ConcreteCategory.mono_of_injective _ hg
    have : Mono G := by unfold G; infer_instance
    exact ConcreteCategory.injective_of_mono_of_preservesPullback _
  have hFG' : ∀ r : R, G (F r) = algebraMap R K r := fun r ↦ congr($hFG r)
  have : IsIso F := by
    refine (ConcreteCategory.isIso_iff_bijective F).mpr ⟨fun a b hab ↦ ?_, fun x ↦ ?_⟩
    · exact IsFractionRing.injective R K (by rw [← hFG', ← hFG', hab])
    · have hx : IsIntegral R (G x : K) := by
        obtain ⟨P, hP, hPx⟩ := hF x
        refine ⟨P, hP, ?_⟩
        have := congr(G.hom $hPx)
        rw [Polynomial.hom_eval₂, map_zero, ← CommRingCat.hom_comp, hFG] at this
        exact this
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hx
      exact ⟨r, hG ((hFG' r).trans hr)⟩
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of R)).inv p.appTop
end GlobalTheory.ProperFunctions
