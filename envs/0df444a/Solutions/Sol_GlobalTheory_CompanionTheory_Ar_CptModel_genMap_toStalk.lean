-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.genMap_toStalk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:38.31709+00:00
-- url     : https://prove2.me/submissions/9a0b238f-da43-45cd-8ca8-309bf4f4aa03

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory
variable {R K : Type} [CommRing R] [Field K]
namespace GlobalTheory.CompanionTheory.Ar.CptModel
theorem _root_.solution (φ : R →+* K) (p : Cpt (pt φ)) (r : R) :
    genMap (pt φ) p (tS p.1 r) = φ r := by
  have h1 := Scheme.germ_stalkClosedPointTo_Spec (R := CommRingCat.of R) (S := CommRingCat.of K)
    (CommRingCat.ofHom φ)
  have h2 := (Spec (CommRingCat.of R)).presheaf.germ_stalkSpecializes (U := ⊤) (y := p.1) trivial p.2
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ p.1 trivial ≫
      ((Spec (CommRingCat.of R)).presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo (pt φ)) =
      CommRingCat.ofHom φ := by
    have h4 : (Spec (CommRingCat.of R)).presheaf.germ ⊤ p.1 trivial ≫
      ((Spec (CommRingCat.of R)).presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo (pt φ)) =
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Scheme.stalkClosedPointTo (pt φ)) h2).trans h1)
    exact (congrArg ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ·) h4).trans (Iso.inv_hom_id_assoc _ _)
  exact congrArg (fun f => f.hom r) h3
end GlobalTheory.CompanionTheory.Ar.CptModel
