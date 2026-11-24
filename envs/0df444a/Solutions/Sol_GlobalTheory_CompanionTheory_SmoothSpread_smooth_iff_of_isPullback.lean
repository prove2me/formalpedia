-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothSpread.smooth_iff_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:40:20.051342+00:00
-- url     : https://prove2.me/submissions/04e12a63-7893-46e7-9d3e-d49a1db71227

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOut

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct MvPolynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothSpread
namespace GlobalTheory.CompanionTheory.SmoothSpread
theorem _root_.solution {R₀ T B : Type} [CommRing R₀] [CommRing T] [CommRing B] [Algebra R₀ T]
    [Algebra R₀ B] {U W : Scheme.{0}} (g : U ⟶ Spec (CommRingCat.of R₀)) (e : U ≅ Spec (CommRingCat.of B))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = g)
    {p : W ⟶ U} {q : W ⟶ Spec (CommRingCat.of T)}
    (H : IsPullback p q g (Spec.map (CommRingCat.ofHom (algebraMap R₀ T)))) :
    Smooth q ↔ Algebra.Smooth T (T ⊗[R₀] B) := by
  have sq := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R₀ T B)).flip
  have H' : IsPullback (p ≫ e.hom) q (Spec.map (CommRingCat.ofHom (algebraMap R₀ B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R₀ T))) :=
    H.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [he]) (by simp)
  have hq : (H'.isoIsPullback _ _ sq).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[R₀] B)) = q :=
    IsPullback.isoIsPullback_hom_snd ..
  have : MorphismProperty.RespectsIso @Smooth.{0} := by
    first
      | exact inferInstance
      | exact HasRingHomProperty.respectsIso
      | exact MorphismProperty.IsStableUnderBaseChange.respectsIso
      | exact (HasRingHomProperty.isLocal_ringHomProperty (P := @Smooth.{0})).respectsIso.arrow
  rw [← hq, MorphismProperty.cancel_left_of_respectsIso (P := @Smooth.{0}), HasRingHomProperty.Spec_iff (P := @Smooth.{0})]
  exact RingHom.smooth_algebraMap (R := T) (S := T ⊗[R₀] B)
end GlobalTheory.CompanionTheory.SmoothSpread
