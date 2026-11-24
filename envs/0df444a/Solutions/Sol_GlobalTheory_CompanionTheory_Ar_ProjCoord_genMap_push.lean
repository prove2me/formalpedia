-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.ProjCoord.genMap_push
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:02.657189+00:00
-- url     : https://prove2.me/submissions/e09978c0-2242-4f92-9aa4-208eb7ff6a11

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
namespace GlobalTheory.CompanionTheory.Ar.ProjCoord
theorem _root_.solution (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (p : Cpt η) :
    genMap (η ≫ f) (push η f p) = (genMap η p).comp (f.stalkMap p.1).hom := by
  have h1 := Scheme.stalkClosedPointTo_comp η f
  have h2 := Scheme.Hom.stalkSpecializes_stalkMap f _ _ p.2
  have h3 : X.presheaf.stalkSpecializes (push η f p).2 ≫ Scheme.stalkClosedPointTo (η ≫ f) =
      f.stalkMap p.1 ≫ (Y.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo η) :=
    (congrArg (X.presheaf.stalkSpecializes (push η f p).2 ≫ ·) h1).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Scheme.stalkClosedPointTo η) h2).trans
        (Category.assoc _ _ _)))
  exact congrArg (fun g => g.hom) h3
end GlobalTheory.CompanionTheory.Ar.ProjCoord
