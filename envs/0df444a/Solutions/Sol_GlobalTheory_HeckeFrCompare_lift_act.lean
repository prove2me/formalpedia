-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.lift_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:07:07.383994+00:00
-- url     : https://prove2.me/submissions/588496d3-31b0-4b9f-9d15-8837b72b2381

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Ω : Type} [CommRing Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution (x : Sp Ω ⟶ Xo.X) (a : Over.mk x ⟶ Xo.univ.t.G) (f : Xo.univ.t.G ⟶ Xo.univ.t.G) :
    (lift (𝟙 (Over.mk x)) (a ≫ f)).left = (lift (𝟙 (Over.mk x)) a).left ≫ (Over.mk x ◁ f).left := by
  rw [← Over.comp_left, lift_whiskerLeft]
end GlobalTheory.HeckeFrCompare
