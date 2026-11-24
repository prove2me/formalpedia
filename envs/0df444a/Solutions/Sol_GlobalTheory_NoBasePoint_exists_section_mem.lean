-- Prove2me | solution 1 for GlobalTheory.NoBasePoint.exists_section_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:08:37.012215+00:00
-- url     : https://prove2.me/submissions/2de9f32c-c3e8-4ebd-8acf-0aeb5f43fbb4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSecValueIsUnit

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
namespace GlobalTheory.NoBasePoint
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] (W : Y.Opens) (hW : (W : Set Y).Nonempty) :
    ∃ σ : Spec (CommRingCat.of K) ⟶ Y, σ ≫ f = 𝟙 _ ∧ ∀ p, σ p ∈ W := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hW W.isOpen.isLocallyClosed
  exact ⟨pointOfClosedPoint f c hc, pointOfClosedPoint_comp f c hc, fun p =>
    (congrArg (· ∈ W) (pointOfClosedPoint_apply f c hc p)).mpr hcW⟩
end GlobalTheory.NoBasePoint
