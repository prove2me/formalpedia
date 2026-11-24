-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.genMap_toSt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:48.986373+00:00
-- url     : https://prove2.me/submissions/bbc7664b-1f43-4cf7-b9b2-2e5ca791fbd8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CoordModel
open AlgebraicGeometry CategoryTheory
variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.CompanionTheory.Ar.CoordModel
theorem _root_.solution (p : Cpt (gen A Ω)) (a : A) :
    genMap (gen A Ω) p (toSt A p.1 a) = algebraMap A Ω a := by
  have h1 := (Spec (CommRingCat.of A)).presheaf.germ_stalkSpecializes (U := ⊤) (y := p.1) trivial p.2
  have h2 := Scheme.germ_stalkClosedPointTo_Spec (R := CommRingCat.of A) (S := CommRingCat.of Ω)
    (CommRingCat.ofHom (algebraMap A Ω))
  have h3 : ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Spec (CommRingCat.of A)).presheaf.germ ⊤ p.1 trivial) ≫
      ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo (gen A Ω)) =
      CommRingCat.ofHom (algebraMap A Ω) := by
    rw [Category.assoc, ← Category.assoc ((Spec (CommRingCat.of A)).presheaf.germ ⊤ p.1 trivial), h1]
    erw [h2]
    simp
  exact congrArg (fun f => f.hom a) h3
end GlobalTheory.CompanionTheory.Ar.CoordModel
