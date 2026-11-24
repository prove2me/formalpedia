-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_appTop_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:37.972452+00:00
-- url     : https://prove2.me/submissions/14a30253-881d-4336-baf4-98855d8555fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isAffine
import Theorems.Thm_GlobalTheory_ProperFunctions_surjective_appTop_of_forall_finiteType
import Theorems.Thm_GlobalTheory_ProperFunctions_injective_appTop_of_flat_of_surjective

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
theorem _root_.solution {p : X ⟶ S} {f : T ⟶ S} {g : Y ⟶ X} {q : Y ⟶ T}
    (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [IsLocallyNoetherian S] [Flat p]
    [IsProper p] [GeometricallyIntegral p] : IsIso q.appTop := by
  have : Flat q := MorphismProperty.of_isPullback H ‹_›
  have : Surjective q := MorphismProperty.of_isPullback H inferInstance
  have : QuasiCompact q := MorphismProperty.of_isPullback H inferInstance
  refine (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨injective_appTop_of_flat_of_surjective q, ?_⟩
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  algebraize [f.appTop.hom]
  have H' : IsPullback g (q ≫ T.isoSpec.hom) (p ≫ S.isoSpec.hom) (Spec.map f.appTop) :=
    H.of_iso (.refl _) (.refl _) T.isoSpec S.isoSpec (by simp) (by simp) (by simp)
      (Scheme.isoSpec_hom_naturality f).symm
  have : GeometricallyIntegral (p ≫ S.isoSpec.hom) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
      (IsPullback.of_horiz_isIso (fst := 𝟙 X) (f := p) (g := S.isoSpec.inv) ⟨by simp⟩) ‹_›
  have := surjective_appTop_of_forall_finiteType (R := Γ(S, ⊤)) (A := Γ(T, ⊤))
    (p := p ≫ S.isoSpec.hom) (fun B _ _ _ ↦ by
      have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing Γ(S, ⊤) B
      have := isIso_appTop_of_isAffine (pullback.snd (p ≫ S.isoSpec.hom)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B))))
      exact (ConcreteCategory.bijective_of_isIso _).2) H'
  rw [Scheme.Hom.comp_appTop] at this
  intro x
  obtain ⟨y, rfl⟩ := this x
  exact ⟨_, rfl⟩
end GlobalTheory.ProperFunctions
