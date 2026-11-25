-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AbForms.parSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:25.653265+00:00
-- url     : https://prove2.me/submissions/b2d08080-34f5-4c02-8a64-a19f6427833d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_uOf_isBaseChange
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_uOf_res
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_par_of_family

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.AbForms
theorem _root_.solution : CotSt → SteinSt → ParSt := by
  intro hc hs R _ A _ g hab hg
  obtain ⟨W, _, _, _, _, y₀, hV, hy⟩ := hc R A.left A.hom η[A].left g (Over.w η[A]) hg
  haveI : ∀ U : A.left.affineOpens, IsOpenImmersion (affPt A.hom U) := fun U ↦
    IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact par_of_family (OAff A.hom) (hs R A g hab hg) g hV
    (fun T ↦ uOf hy (affPt A.hom T.unop) (affPt_w A.hom T.unop))
    (fun T ↦ uOf_isBaseChange hy (affPt A.hom T.unop) (affPt_w A.hom T.unop))
    (fun T T' φ w ↦ congrArg (fun t ↦ t w) (uOf_res hy (affPt A.hom T.unop) (affPt_w A.hom T.unop)
      (Sec.res A.hom (leOfHom φ.unop)) (affPt A.hom T'.unop) (affPt_w A.hom T'.unop)
      (affPt_res A.hom (leOfHom φ.unop)).symm))
end GlobalTheory.CompanionTheory.AbForms
