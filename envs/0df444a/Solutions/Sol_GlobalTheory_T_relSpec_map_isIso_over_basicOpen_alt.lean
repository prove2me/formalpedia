-- Prove2me | solution 1 for GlobalTheory.T.relSpec_map_isIso_over_basicOpen_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:13.795078+00:00
-- url     : https://prove2.me/submissions/0eaf4261-17f7-4d97-b382-42d6e9f55751

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpen
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpenStatement
import Theorems.Thm_GlobalTheory_relSpec_map_isIso_over_basicOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F), α' ≫ ι = α → ∀ (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued), g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase → (∀ V, (relativeGluingData hα).cover.f V ≫ g = Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V) → ∀ (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V)), Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b) → ∀ (W : (relativeGluingData hα').glued.Opens), (W : Set (relativeGluingData hα').glued) = (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V)))) → IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) = (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) : Set (PrimeSpectrum (F.obj (Opposite.op V)))) := by
  first | exact @GlobalTheory.relSpec_map_isIso_over_basicOpen | exact GlobalTheory.relSpec_map_isIso_over_basicOpen | (intros; apply GlobalTheory.relSpec_map_isIso_over_basicOpen <;> assumption)
end _root_.GlobalTheory.T
