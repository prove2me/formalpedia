-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.evalPt_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:18.284592+00:00
-- url     : https://prove2.me/submissions/9a0f7480-bcbf-4cf7-add1-8d578fe5e32c

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
variable {R : Type} [CommRing R] {X Y : Scheme.{0}}
namespace GlobalTheory.ArtinKernel
theorem _root_.solution (x : Sp R ⟶ X) (φ : X ⟶ Y) (y : Sp R ⟶ Y) (hy : x ≫ φ = y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ φ ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (hU : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(Y, U)) :
    evalPt x V hV ((φ.appLE U V e).hom f) = evalPt y U hU f := by
  subst hy
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
end GlobalTheory.ArtinKernel
