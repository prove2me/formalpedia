-- Prove2me | solution 1 for GlobalTheory.NoBasePoint.unitAt_transl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:14.626263+00:00
-- url     : https://prove2.me/submissions/08763959-fb46-493f-bb93-2a638a0d5b43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSecValueIsUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_isUnit_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_UnitAt_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_formEq_of_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.NoBasePoint
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left}
namespace GlobalTheory.NoBasePoint
theorem _root_.solution (hL : L.IsLB) {T : Over S} (θ : LB.Sec (LPow A L 1 T)) (k : (LPow A L 1 T).ι)
    (a : T ⟶ A) (y : (T ⊗ A).left) (hy : (translT A a).left y ∈ (T ⊗ A).left.basicOpen (θ.f k)) :
    UnitAt L (K := Fin 1) (fun _ => (translPt A a).left) (fun _ => 1) y := by
  refine UnitAt.congr hL ?_ ⟨pullSec θ (translT A a).left, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Over.comp_left, translT, lift_snd]
  · rw [sval_pullSec θ _ (𝟙 _) y hJ]
    exact isUnit_sval θ _ y hJ k hy
end GlobalTheory.NoBasePoint
