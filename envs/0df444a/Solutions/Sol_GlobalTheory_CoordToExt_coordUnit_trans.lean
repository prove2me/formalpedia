-- Prove2me | solution 1 for GlobalTheory.CoordToExt.coordUnit_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:41:19.356871+00:00
-- url     : https://prove2.me/submissions/081191e7-2bc1-4b30-9c5b-a2776d1d4f17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
import Theorems.Thm_GlobalTheory_CoordToExt_gm_coordUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CoordToExt
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ)
variable {I D e} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
namespace GlobalTheory.CoordToExt
theorem _root_.solution (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z)
    (a a' : (bundle I D e χ).ι) (h : g.q.left (r z) ∈ (bundle I D e χ).U a)
    (h' : g.q.left (r z) ∈ (bundle I D e χ).U a') :
    gm r z _ (coordUnit g χ a') = gm (r ≫ g.q.left) z _ ((bundle I D e χ).g a a') * gm r z _ (coordUnit g χ a) := by
  have e₁ := gen_trans (g.t_gen χ) r z (mem_chart g χ a _ h) (mem_chart g χ a' _ h')
  have e₂ := gm_linComb D.P.L (Y := (thickObj R I e D.P.A).left) (D.Oφ (D.prBe I e) χ) Oε (r ≫ g.q.left) z a a' h h'
  have e₃ : (∏ k, gm ((r ≫ g.q.left) ≫ D.Oφ (D.prBe I e) χ k) z (D.P.L.U (a k) ⊓ D.P.L.U (a' k))
      (D.P.L.g (a k) (a' k)) ^ Oε k) * trF (D.Oφ g.pG χ) Oinvε r z a a' = 1 := by
    refine Finset.prod_mul_distrib.symm.trans (Finset.prod_eq_one fun k _ => ?_)
    have hk : Oinvε k = - Oε k := by revert k; decide
    have hq : (r ≫ g.q.left) ≫ D.Oφ (D.prBe I e) χ k = r ≫ D.Oφ g.pG χ k :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (q_Oφ g χ k))
    rw [hk, zpow_neg]
    exact (congrArg (fun f => gm f z (D.P.L.U (a k) ⊓ D.P.L.U (a' k)) (D.P.L.g (a k) (a' k)) ^ Oε k * _) hq).trans
      (mul_inv_cancel _)
  refine (gm_coordUnit g χ a' r z h').trans (Eq.symm ((congrArg₂ (· * ·) e₂ ((gm_coordUnit g χ a r z h).trans e₁)).trans ?_))
  exact (_root_.mul_assoc _ _ _).symm.trans ((congrArg (· * _) e₃).trans (_root_.one_mul _))
end GlobalTheory.CoordToExt
