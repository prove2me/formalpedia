-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.functions_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:10:49.149748+00:00
-- url     : https://prove2.me/submissions/febadbd0-69d4-41d3-919f-4482965e9b78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_field
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_baseChange_of_field
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isIntegrallyClosed
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isAffine
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_baseChange
import Theorems.Thm_GlobalTheory_ProperFunctions_bijective_of_isIso_appTop

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
namespace GlobalTheory.ProperFunctions
theorem _root_.solution :
    (∀ (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [IsProper p]
      [GeometricallyIntegral p],
        Function.Bijective ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) ∧
        ∀ (A : Type u) [CommRing A] [Algebra k A],
          Function.Bijective ((Scheme.ΓSpecIso (.of A)).inv ≫
            (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop)) ∧
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (X : Scheme.{u})
      (p : X ⟶ Spec (.of R)) [IsProper p] [Flat p] [GeometricallyIntegral
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))],
        Function.Bijective ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop)) ∧
    (∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      [IsProper p] [Flat p] [GeometricallyIntegral p],
        Function.Bijective ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) ∧
        ∀ (A : Type u) [CommRing A] [Algebra R A],
          Function.Bijective ((Scheme.ΓSpecIso (.of A)).inv ≫
            (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop)) := by
  refine ⟨fun k _ X p _ _ ↦ ⟨?_, fun A _ _ ↦ ?_⟩, fun R _ _ _ X p _ _ _ ↦ ?_,
    fun R _ _ X p _ _ _ ↦ ⟨?_, fun A _ _ ↦ ?_⟩⟩
  · have := isIso_appTop_of_field p
    exact bijective_of_isIso_appTop p
  · have := isIso_appTop_baseChange_of_field
      (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    exact bijective_of_isIso_appTop _
  · have := isIso_appTop_of_isIntegrallyClosed (IsPullback.of_hasPullback p
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
    exact bijective_of_isIso_appTop p
  · have := isIso_appTop_of_isAffine p
    exact bijective_of_isIso_appTop p
  · have := isIso_appTop_baseChange
      (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    exact bijective_of_isIso_appTop _
end GlobalTheory.ProperFunctions
