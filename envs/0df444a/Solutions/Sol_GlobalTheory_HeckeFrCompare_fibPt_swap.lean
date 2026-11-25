-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.fibPt_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:48:14.204341+00:00
-- url     : https://prove2.me/submissions/dc317241-ed40-446f-a895-c1702eb7eaec

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
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution {Ω : Type} [Field Ω] {x : Sp Ω ⟶ Xo.X} (a : Over.mk x ⟶ Xo.univ.t.G) :
    (lift (𝟙 (Over.mk x)) a).left ≫ (swap x).hom = fibPt _ a := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, swap_hom_fst, lift_l_snd, fibPt, pullback.lift_fst]
  · rw [Category.assoc, swap_hom_snd, lift_l_fst, fibPt, pullback.lift_snd]; rfl
end GlobalTheory.HeckeFrCompare
