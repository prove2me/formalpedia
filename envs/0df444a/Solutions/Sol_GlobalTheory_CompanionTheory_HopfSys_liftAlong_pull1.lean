-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.liftAlong_pull1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:39:57.126661+00:00
-- url     : https://prove2.me/submissions/e25d6f2d-18d4-46b6-9645-96538dc5ee04

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul
import Theorems.Thm_GlobalTheory_CechDR_isPullO_pullHO1


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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
  {C D : Type} [Category.{0} C] [Category.{0} D]
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (u : C ⥤ AffOp X) (t : D ⥤ C)
    (fb : D ⥤ AffOp X') (hle : ∀ d, (fb.obj d).unop.1 ≤ φ ⁻¹ᵁ (u.obj (t.obj d)).unop.1) (c : HO1 s) :
    (liftAlong h u t fb hle).pull1 ((CoefMap.restrict (OAff s) u).pull1 c) =
      (CoefMap.restrict (OAff s') fb).pull1 (pullHO1 h c) := by
  let r : CoefMap (RingHom.id R) (OPair φ s') (fb ⋙ OAff s') :=
    { G := pairFn φ u t fb hle
      α _ := RingHom.id _
      naturality _ _ := rfl
      smul _ _ _ := rfl }
  have t1 : (liftAlong h u t fb hle).pull1 ((CoefMap.restrict (OAff s) u).pull1 c) =
      r.pull1 ((pairPull h).pull1 c) := by
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c; rfl
  have t2 : ∀ x : HO1 s', r.pull1 ((pairRes φ s').pull1 x) = (CoefMap.restrict (OAff s') fb).pull1 x := by
    intro x
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ x; rfl
  rw [t1, (isPullO_pullHO1 h c : _ = _), t2]
end GlobalTheory.CompanionTheory.HopfSys
