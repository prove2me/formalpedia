-- Prove2me | solution 1 for GlobalTheory.LN.FourthSide.pG_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:58:07.078111+00:00
-- url     : https://prove2.me/submissions/65da65c1-4d16-4234-b14f-e10d4ddff3f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourthSideRespectsRigSymmetryCube
import Theorems.Thm_GlobalTheory_UU_toBase_mul_pullback
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.LN GlobalTheory.LN.FourthSide
namespace GlobalTheory.LN.FourthSide
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {e : ℕ} (g : GtCoord I D e G)
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y : T ⟶ thickObj R I e G) :
    toBase (A' := thickObj R I e G) (f := thick R I e) (g := g.pG.left) (Over.w g.pG) (x * y) =
      toBase (Over.w g.pG) x * toBase (Over.w g.pG) y := by
  have := g.q_hom
  have := toBase_mul_pullback D.P.A (thick R I e) T (x ≫ g.q) (y ≫ g.q)
  rw [← MonObj.mul_comp] at this
  have a : ∀ x : T ⟶ thickObj R I e G, toBase (Over.w g.pG) x =
      toBase (A := D.P.A) (g := pullback.fst D.P.A.hom (thick R I e)) pullback.condition (x ≫ g.q) :=
    fun x => Over.OverMorphism.ext (Category.assoc _ _ _).symm
  exact (a _).trans (this.trans (congrArg₂ (· * ·) (a x) (a y)).symm)
end GlobalTheory.LN.FourthSide
