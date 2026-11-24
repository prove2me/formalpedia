-- Prove2me | solution 1 for GlobalTheory.ChartQF.range_subset_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:44.839606+00:00
-- url     : https://prove2.me/submissions/b5c4211b-5422-4bea-8805-1aa1aac361e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfMemClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartQF
namespace GlobalTheory.ChartQF
theorem _root_.solution {F R : Type} [CommRing F] [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (ξ : Sp R ⟶ S)
    (σ : S ⟶ Sp F) (b : F →+* R) (h : ξ ≫ σ = spMap b) :
    Set.range b ⊆ Set.range (Scheme.stalkClosedPointTo ξ).hom := by
  rintro _ ⟨c, rfl⟩
  have key : ∀ g : Sp R ⟶ Sp F, g = spMap b →
      (Sp F).presheaf.germ ⊤ (g (closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo g =
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom b := by
    rintro g rfl
    exact Scheme.germ_stalkClosedPointTo_Spec _
  have e := key _ h
  rw [Scheme.stalkClosedPointTo_comp] at e
  refine ⟨σ.stalkMap (ξ (closedPoint R))
    ((Sp F).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c)), ?_⟩
  have h1 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c)) e
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom b).hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c) = b c := by simp
  rw [← h2, ← h1]
  rfl
end GlobalTheory.ChartQF
