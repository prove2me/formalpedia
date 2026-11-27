-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.samePt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:23.580482+00:00
-- url     : https://prove2.me/submissions/c1b147cf-c76a-44c6-aa8a-8274b9ec3432

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UU.RelModel
theorem _root_.solution (U : PreU I D A G) {x x' : TFK (R := R) F ⟶ A.A} {y y' : TF (R := R) F ⟶ G}
    (h : U.SamePt x y) (h' : U.SamePt x' y') : U.SamePt (x * x') (y * y') := by
  have := U.gen_hom
  have e := (isGrpPullback_pullback G (jK R)).2 _ (x ≫ U.gen.inv) (x' ≫ U.gen.inv) y y'
    (h.symm.trans (Category.assoc _ _ _).symm) (h'.symm.trans (Category.assoc _ _ _).symm)
  rw [← MonObj.mul_comp] at e
  exact (Category.assoc _ _ _).symm.trans e.symm
end GlobalTheory.UU.RelModel
