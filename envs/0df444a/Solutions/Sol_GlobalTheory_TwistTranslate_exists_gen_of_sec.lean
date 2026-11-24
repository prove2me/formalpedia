-- Prove2me | solution 1 for GlobalTheory.TwistTranslate.exists_gen_of_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:42:24.713729+00:00
-- url     : https://prove2.me/submissions/8e05a7ef-605c-4526-8c19-b508b355ce04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TwistedPowTranslate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_UnitAt_mul


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistTranslate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.TwistTranslate
theorem _root_.solution (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (hs : ∀ (y : Y) J, Good L y J → IsUnit (sval s (𝟙 Y) y J)) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have hu : ∀ j, IsUnit (s.f j) := fun j => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    exact (congrArg IsUnit ((gs_eq (𝟙 Y) y (LB.wchart L φ j) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul (hs y J hJ))
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j)⟩
end GlobalTheory.TwistTranslate
