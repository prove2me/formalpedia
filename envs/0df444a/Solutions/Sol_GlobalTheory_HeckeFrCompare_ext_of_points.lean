-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.ext_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:54:55.506404+00:00
-- url     : https://prove2.me/submissions/5c2e2006-1224-4092-a4f6-477e666ba5a0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution {Ω : Type} [Field Ω] [IsAlgClosed Ω] {T Y Z : Scheme.{0}} (t : T ⟶ Sp Ω)
    [LocallyOfFiniteType t] [IsReduced T] (s : Y ⟶ Z) [IsSeparated s] {f g : T ⟶ Y} (H' : f ≫ s = g ≫ s)
    (Hq : ∀ q : Sp Ω ⟶ T, q ≫ t = 𝟙 _ → q ≫ f = q ≫ g) : f = g := by
  have : JacobsonSpace ↥T := LocallyOfFiniteType.jacobsonSpace t
  refine ext_of_fromSpecResidueField_eq f g s (closedPoints T) ?_ ?_ H'
  · rw [dense_iff_closure_eq, closure_closedPoints]
  · intro x hx
    rw [← cancel_epi (Spec.map (residueFieldIsoBase t x hx).hom)]
    have := Hq _ (pointOfClosedPoint_comp t x hx)
    simpa only [pointOfClosedPoint, Category.assoc] using this
end GlobalTheory.HeckeFrCompare
